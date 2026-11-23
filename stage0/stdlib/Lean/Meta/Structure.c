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
v___x_506_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_503_);
lean_ctor_set(v___x_506_, 3, v___x_504_);
lean_ctor_set(v___x_506_, 4, v___x_504_);
lean_ctor_set(v___x_506_, 5, v___x_504_);
lean_ctor_set(v___x_506_, 6, v___x_502_);
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
lean_ctor_set(v___x_813_, 0, v___y_810_);
lean_ctor_set(v___x_813_, 1, v___y_805_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*3, v___x_732_);
v___x_814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_addDecl(v___x_814_, v___y_807_, v___y_808_, v___y_809_);
lean_dec_ref(v___y_808_);
v___y_793_ = v___y_806_;
v___y_794_ = v___y_809_;
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
v___y_805_ = v___x_835_;
v___y_806_ = v___y_820_;
v___y_807_ = v___x_823_;
v___y_808_ = v___x_837_;
v___y_809_ = v___y_822_;
v___y_810_ = v___x_860_;
goto v___jp_804_;
}
}
else
{
lean_dec_ref(v_env_862_);
v___y_805_ = v___x_835_;
v___y_806_ = v___y_820_;
v___y_807_ = v___x_823_;
v___y_808_ = v___x_837_;
v___y_809_ = v___y_822_;
v___y_810_ = v___x_860_;
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
uint8_t v_instImplicit_boxed_953_; uint8_t v___x_18434__boxed_954_; uint8_t v_a_18440__boxed_955_; lean_object* v_res_956_; 
v_instImplicit_boxed_953_ = lean_unbox(v_instImplicit_934_);
v___x_18434__boxed_954_ = lean_unbox(v___x_939_);
v_a_18440__boxed_955_ = lean_unbox(v_a_946_);
v_res_956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v___x_930_, v_projName_931_, v___x_932_, v_a_933_, v_instImplicit_boxed_953_, v___x_935_, v_params_936_, v_self_937_, v_b_938_, v___x_18434__boxed_954_, v_a_940_, v___x_941_, v_paramInfoOverrides_942_, v_n_943_, v_ref_944_, v___x_945_, v_a_18440__boxed_955_, v_____r_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
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
uint8_t v___x_18833__boxed_1002_; lean_object* v_res_1003_; 
v___x_18833__boxed_1002_ = lean_unbox(v___x_992_);
v_res_1003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1(v___x_18833__boxed_1002_, v_projName_993_, v_n_994_, v_ref_995_, v___f_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
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
uint8_t v_instImplicit_boxed_1063_; uint8_t v_a_18914__boxed_1064_; lean_object* v_res_1065_; 
v_instImplicit_boxed_1063_ = lean_unbox(v_instImplicit_1047_);
v_a_18914__boxed_1064_ = lean_unbox(v_a_1055_);
v_res_1065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v_upperBound_1043_, v_projDecls_1044_, v___x_1045_, v___x_1046_, v_instImplicit_boxed_1063_, v___x_1048_, v_params_1049_, v_self_1050_, v_a_1051_, v___x_1052_, v_n_1053_, v___x_1054_, v_a_18914__boxed_1064_, v_a_1056_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
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
uint8_t v_instImplicit_boxed_1132_; uint8_t v_a_18986__boxed_1133_; lean_object* v_res_1134_; 
v_instImplicit_boxed_1132_ = lean_unbox(v_instImplicit_1117_);
v_a_18986__boxed_1133_ = lean_unbox(v_a_1124_);
v_res_1134_ = l_Lean_Meta_mkProjections___lam__0(v_params_1116_, v_instImplicit_boxed_1132_, v_projDecls_1118_, v_toConstantVal_1119_, v_numParams_1120_, v___x_1121_, v_n_1122_, v_levelParams_1123_, v_a_18986__boxed_1133_, v_ctorType_1125_, v_self_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
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
v___x_1169_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(v___x_1167_, v___y_1166_, v___y_1165_, v___y_1162_, v___x_1168_, v___y_1160_, v___y_1164_, v___y_1163_, v___y_1161_);
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
v___y_1160_ = v___y_1154_;
v___y_1161_ = v___y_1157_;
v___y_1162_ = v___f_1172_;
v___y_1163_ = v___y_1156_;
v___y_1164_ = v___y_1155_;
v___y_1165_ = v___x_1175_;
v___y_1166_ = v___x_1176_;
goto v___jp_1159_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = 3;
v___y_1160_ = v___y_1154_;
v___y_1161_ = v___y_1157_;
v___y_1162_ = v___f_1172_;
v___y_1163_ = v___y_1156_;
v___y_1164_ = v___y_1155_;
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
uint8_t v_instImplicit_boxed_1201_; uint8_t v_a_19090__boxed_1202_; lean_object* v_res_1203_; 
v_instImplicit_boxed_1201_ = lean_unbox(v_instImplicit_1186_);
v_a_19090__boxed_1202_ = lean_unbox(v_a_1193_);
v_res_1203_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1201_, v_projDecls_1187_, v_toConstantVal_1188_, v_numParams_1189_, v___x_1190_, v_n_1191_, v_levelParams_1192_, v_a_19090__boxed_1202_, v_params_1194_, v_ctorType_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
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
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_13566__overap_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = l_instInhabitedOfMonad___redArg(v___x_1277_, v___x_1278_);
v___x_13566__overap_1280_ = lean_panic_fn_borrowed(v___x_1279_, v_msg_1223_);
lean_dec(v___x_1279_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1281_ = lean_apply_5(v___x_13566__overap_1280_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
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
uint8_t v_instImplicit_boxed_1645_; uint8_t v_a_19816__boxed_1646_; lean_object* v_res_1647_; 
v_instImplicit_boxed_1645_ = lean_unbox(v_instImplicit_1626_);
v_a_19816__boxed_1646_ = lean_unbox(v_a_1634_);
v_res_1647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9(v_upperBound_1622_, v_projDecls_1623_, v___x_1624_, v___x_1625_, v_instImplicit_boxed_1645_, v___x_1627_, v_params_1628_, v_self_1629_, v_a_1630_, v___x_1631_, v_n_1632_, v___x_1633_, v_a_19816__boxed_1646_, v_inst_1635_, v_R_1636_, v_a_1637_, v_b_1638_, v_c_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1(lean_object* v_x_2407_, lean_object* v_e_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_e_2408_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1___boxed(lean_object* v_x_2415_, lean_object* v_e_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1(v_x_2415_, v_e_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v_x_2415_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_apply_1(v_x_2424_, lean_box(0));
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_x_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2432_, v_x_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2440_, lean_object* v_b_2441_, lean_object* v_x_2442_){
_start:
{
if (lean_obj_tag(v_x_2442_) == 0)
{
lean_dec(v_b_2441_);
lean_dec_ref(v_a_2440_);
return v_x_2442_;
}
else
{
lean_object* v_key_2443_; lean_object* v_value_2444_; lean_object* v_tail_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2457_; 
v_key_2443_ = lean_ctor_get(v_x_2442_, 0);
v_value_2444_ = lean_ctor_get(v_x_2442_, 1);
v_tail_2445_ = lean_ctor_get(v_x_2442_, 2);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_x_2442_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2447_ = v_x_2442_;
v_isShared_2448_ = v_isSharedCheck_2457_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_tail_2445_);
lean_inc(v_value_2444_);
lean_inc(v_key_2443_);
lean_dec(v_x_2442_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2457_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
uint8_t v___x_2449_; 
v___x_2449_ = l_Lean_ExprStructEq_beq(v_key_2443_, v_a_2440_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2440_, v_b_2441_, v_tail_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 2, v___x_2450_);
v___x_2452_ = v___x_2447_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_key_2443_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_value_2444_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
lean_object* v___x_2455_; 
lean_dec(v_value_2444_);
lean_dec(v_key_2443_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v_b_2441_);
lean_ctor_set(v___x_2447_, 0, v_a_2440_);
v___x_2455_ = v___x_2447_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2440_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_b_2441_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_tail_2445_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
if (lean_obj_tag(v_x_2459_) == 0)
{
return v_x_2458_;
}
else
{
lean_object* v_key_2460_; lean_object* v_value_2461_; lean_object* v_tail_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2485_; 
v_key_2460_ = lean_ctor_get(v_x_2459_, 0);
v_value_2461_ = lean_ctor_get(v_x_2459_, 1);
v_tail_2462_ = lean_ctor_get(v_x_2459_, 2);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_x_2459_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2464_ = v_x_2459_;
v_isShared_2465_ = v_isSharedCheck_2485_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_tail_2462_);
lean_inc(v_value_2461_);
lean_inc(v_key_2460_);
lean_dec(v_x_2459_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2485_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; uint64_t v___x_2467_; uint64_t v___x_2468_; uint64_t v___x_2469_; uint64_t v_fold_2470_; uint64_t v___x_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; size_t v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2466_ = lean_array_get_size(v_x_2458_);
v___x_2467_ = l_Lean_ExprStructEq_hash(v_key_2460_);
v___x_2468_ = 32ULL;
v___x_2469_ = lean_uint64_shift_right(v___x_2467_, v___x_2468_);
v_fold_2470_ = lean_uint64_xor(v___x_2467_, v___x_2469_);
v___x_2471_ = 16ULL;
v___x_2472_ = lean_uint64_shift_right(v_fold_2470_, v___x_2471_);
v___x_2473_ = lean_uint64_xor(v_fold_2470_, v___x_2472_);
v___x_2474_ = lean_uint64_to_usize(v___x_2473_);
v___x_2475_ = lean_usize_of_nat(v___x_2466_);
v___x_2476_ = ((size_t)1ULL);
v___x_2477_ = lean_usize_sub(v___x_2475_, v___x_2476_);
v___x_2478_ = lean_usize_land(v___x_2474_, v___x_2477_);
v___x_2479_ = lean_array_uget_borrowed(v_x_2458_, v___x_2478_);
lean_inc(v___x_2479_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 2, v___x_2479_);
v___x_2481_ = v___x_2464_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_key_2460_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_value_2461_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_array_uset(v_x_2458_, v___x_2478_, v___x_2481_);
v_x_2458_ = v___x_2482_;
v_x_2459_ = v_tail_2462_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2486_, lean_object* v_source_2487_, lean_object* v_target_2488_){
_start:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = lean_array_get_size(v_source_2487_);
v___x_2490_ = lean_nat_dec_lt(v_i_2486_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v_source_2487_);
lean_dec(v_i_2486_);
return v_target_2488_;
}
else
{
lean_object* v_es_2491_; lean_object* v___x_2492_; lean_object* v_source_2493_; lean_object* v_target_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_es_2491_ = lean_array_fget(v_source_2487_, v_i_2486_);
v___x_2492_ = lean_box(0);
v_source_2493_ = lean_array_fset(v_source_2487_, v_i_2486_, v___x_2492_);
v_target_2494_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2488_, v_es_2491_);
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2496_ = lean_nat_add(v_i_2486_, v___x_2495_);
lean_dec(v_i_2486_);
v_i_2486_ = v___x_2496_;
v_source_2487_ = v_source_2493_;
v_target_2488_ = v_target_2494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2498_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v_nbuckets_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2499_ = lean_array_get_size(v_data_2498_);
v___x_2500_ = lean_unsigned_to_nat(2u);
v_nbuckets_2501_ = lean_nat_mul(v___x_2499_, v___x_2500_);
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_mk_array(v_nbuckets_2501_, v___x_2503_);
v___x_2505_ = lean_array_propagate_mark(v_data_2498_, v___x_2504_);
v___x_2506_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2502_, v_data_2498_, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2507_, lean_object* v_x_2508_){
_start:
{
if (lean_obj_tag(v_x_2508_) == 0)
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
return v___x_2509_;
}
else
{
lean_object* v_key_2510_; lean_object* v_tail_2511_; uint8_t v___x_2512_; 
v_key_2510_ = lean_ctor_get(v_x_2508_, 0);
v_tail_2511_ = lean_ctor_get(v_x_2508_, 2);
v___x_2512_ = l_Lean_ExprStructEq_beq(v_key_2510_, v_a_2507_);
if (v___x_2512_ == 0)
{
v_x_2508_ = v_tail_2511_;
goto _start;
}
else
{
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2514_, lean_object* v_x_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2514_, v_x_2515_);
lean_dec(v_x_2515_);
lean_dec_ref(v_a_2514_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2518_, lean_object* v_a_2519_, lean_object* v_b_2520_){
_start:
{
lean_object* v_size_2521_; lean_object* v_buckets_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2565_; 
v_size_2521_ = lean_ctor_get(v_m_2518_, 0);
v_buckets_2522_ = lean_ctor_get(v_m_2518_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_m_2518_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2524_ = v_m_2518_;
v_isShared_2525_ = v_isSharedCheck_2565_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_buckets_2522_);
lean_inc(v_size_2521_);
lean_dec(v_m_2518_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2565_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; uint64_t v___x_2527_; uint64_t v___x_2528_; uint64_t v___x_2529_; uint64_t v_fold_2530_; uint64_t v___x_2531_; uint64_t v___x_2532_; uint64_t v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; size_t v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; lean_object* v_bkt_2539_; uint8_t v___x_2540_; 
v___x_2526_ = lean_array_get_size(v_buckets_2522_);
v___x_2527_ = l_Lean_ExprStructEq_hash(v_a_2519_);
v___x_2528_ = 32ULL;
v___x_2529_ = lean_uint64_shift_right(v___x_2527_, v___x_2528_);
v_fold_2530_ = lean_uint64_xor(v___x_2527_, v___x_2529_);
v___x_2531_ = 16ULL;
v___x_2532_ = lean_uint64_shift_right(v_fold_2530_, v___x_2531_);
v___x_2533_ = lean_uint64_xor(v_fold_2530_, v___x_2532_);
v___x_2534_ = lean_uint64_to_usize(v___x_2533_);
v___x_2535_ = lean_usize_of_nat(v___x_2526_);
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_sub(v___x_2535_, v___x_2536_);
v___x_2538_ = lean_usize_land(v___x_2534_, v___x_2537_);
v_bkt_2539_ = lean_array_uget_borrowed(v_buckets_2522_, v___x_2538_);
v___x_2540_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2519_, v_bkt_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v_size_x27_2542_; lean_object* v___x_2543_; lean_object* v_buckets_x27_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2541_ = lean_unsigned_to_nat(1u);
v_size_x27_2542_ = lean_nat_add(v_size_2521_, v___x_2541_);
lean_dec(v_size_2521_);
lean_inc(v_bkt_2539_);
v___x_2543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2543_, 0, v_a_2519_);
lean_ctor_set(v___x_2543_, 1, v_b_2520_);
lean_ctor_set(v___x_2543_, 2, v_bkt_2539_);
v_buckets_x27_2544_ = lean_array_uset(v_buckets_2522_, v___x_2538_, v___x_2543_);
v___x_2545_ = lean_unsigned_to_nat(4u);
v___x_2546_ = lean_nat_mul(v_size_x27_2542_, v___x_2545_);
v___x_2547_ = lean_unsigned_to_nat(3u);
v___x_2548_ = lean_nat_div(v___x_2546_, v___x_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_array_get_size(v_buckets_x27_2544_);
v___x_2550_ = lean_nat_dec_le(v___x_2548_, v___x_2549_);
lean_dec(v___x_2548_);
if (v___x_2550_ == 0)
{
lean_object* v_val_2551_; lean_object* v___x_2553_; 
v_val_2551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2544_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v_val_2551_);
lean_ctor_set(v___x_2524_, 0, v_size_x27_2542_);
v___x_2553_ = v___x_2524_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_size_x27_2542_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_val_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
else
{
lean_object* v___x_2556_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v_buckets_x27_2544_);
lean_ctor_set(v___x_2524_, 0, v_size_x27_2542_);
v___x_2556_ = v___x_2524_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_x27_2542_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_buckets_x27_2544_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
else
{
lean_object* v___x_2558_; lean_object* v_buckets_x27_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_inc(v_bkt_2539_);
v___x_2558_ = lean_box(0);
v_buckets_x27_2559_ = lean_array_uset(v_buckets_2522_, v___x_2538_, v___x_2558_);
v___x_2560_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2519_, v_b_2520_, v_bkt_2539_);
v___x_2561_ = lean_array_uset(v_buckets_x27_2559_, v___x_2538_, v___x_2560_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2561_);
v___x_2563_ = v___x_2524_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_size_2521_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2566_, lean_object* v_e_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2570_ = lean_st_ref_take(v_a_2566_);
v___x_2571_ = lean_box(0);
v___x_2572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2570_, v_e_2567_, v_a_2568_);
v___x_2573_ = lean_st_ref_put(v_a_2566_, v___x_2572_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2574_, lean_object* v_e_2575_, lean_object* v_a_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2574_, v_e_2575_, v_a_2576_);
lean_dec(v_a_2574_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_apply_1(v_x_2580_, lean_box(0));
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2588_, v_x_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2(lean_object* v___x_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2649_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2___boxed(lean_object* v___x_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2(v___x_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
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
lean_object* v___y_2728_; lean_object* v_toCold_2737_; lean_object* v_currRecDepth_2738_; lean_object* v_ref_2739_; uint16_t v_optionFlags_2740_; uint8_t v_suppressElabErrors_2741_; uint8_t v_checkDeprecated_2742_; uint8_t v_isRecordingDeps_2743_; lean_object* v_maxRecDepth_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_toCold_2737_ = lean_ctor_get(v___y_2724_, 0);
v_currRecDepth_2738_ = lean_ctor_get(v___y_2724_, 1);
v_ref_2739_ = lean_ctor_get(v___y_2724_, 2);
v_optionFlags_2740_ = lean_ctor_get_uint16(v___y_2724_, sizeof(void*)*3);
v_suppressElabErrors_2741_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*3 + 2);
v_checkDeprecated_2742_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2743_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*3 + 4);
v_maxRecDepth_2749_ = lean_ctor_get(v_toCold_2737_, 3);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = lean_nat_dec_eq(v_maxRecDepth_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_nat_dec_eq(v_currRecDepth_2738_, v_maxRecDepth_2749_);
if (v___x_2752_ == 0)
{
goto v___jp_2744_;
}
else
{
lean_object* v___x_2753_; 
lean_dec_ref(v_x_2720_);
lean_inc(v_ref_2739_);
v___x_2753_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2739_);
v___y_2728_ = v___x_2753_;
goto v___jp_2727_;
}
}
else
{
goto v___jp_2744_;
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
v___jp_2744_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2745_ = lean_unsigned_to_nat(1u);
v___x_2746_ = lean_nat_add(v_currRecDepth_2738_, v___x_2745_);
lean_inc(v_ref_2739_);
lean_inc_ref(v_toCold_2737_);
v___x_2747_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2747_, 0, v_toCold_2737_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
lean_ctor_set(v___x_2747_, 2, v_ref_2739_);
lean_ctor_set_uint16(v___x_2747_, sizeof(void*)*3, v_optionFlags_2740_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*3 + 2, v_suppressElabErrors_2741_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*3 + 3, v_checkDeprecated_2742_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*3 + 4, v_isRecordingDeps_2743_);
lean_inc(v___y_2725_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
v___x_2748_ = lean_apply_6(v_x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___x_2747_, v___y_2725_, lean_box(0));
v___y_2728_ = v___x_2748_;
goto v___jp_2727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_a_2762_, lean_object* v_x_2763_){
_start:
{
if (lean_obj_tag(v_x_2763_) == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
else
{
lean_object* v_key_2765_; lean_object* v_value_2766_; lean_object* v_tail_2767_; uint8_t v___x_2768_; 
v_key_2765_ = lean_ctor_get(v_x_2763_, 0);
v_value_2766_ = lean_ctor_get(v_x_2763_, 1);
v_tail_2767_ = lean_ctor_get(v_x_2763_, 2);
v___x_2768_ = l_Lean_ExprStructEq_beq(v_key_2765_, v_a_2762_);
if (v___x_2768_ == 0)
{
v_x_2763_ = v_tail_2767_;
goto _start;
}
else
{
lean_object* v___x_2770_; 
lean_inc(v_value_2766_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_value_2766_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_a_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2771_, v_x_2772_);
lean_dec(v_x_2772_);
lean_dec_ref(v_a_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(lean_object* v_m_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_buckets_2776_; lean_object* v___x_2777_; uint64_t v___x_2778_; uint64_t v___x_2779_; uint64_t v___x_2780_; uint64_t v_fold_2781_; uint64_t v___x_2782_; uint64_t v___x_2783_; uint64_t v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; size_t v___x_2788_; size_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_buckets_2776_ = lean_ctor_get(v_m_2774_, 1);
v___x_2777_ = lean_array_get_size(v_buckets_2776_);
v___x_2778_ = l_Lean_ExprStructEq_hash(v_a_2775_);
v___x_2779_ = 32ULL;
v___x_2780_ = lean_uint64_shift_right(v___x_2778_, v___x_2779_);
v_fold_2781_ = lean_uint64_xor(v___x_2778_, v___x_2780_);
v___x_2782_ = 16ULL;
v___x_2783_ = lean_uint64_shift_right(v_fold_2781_, v___x_2782_);
v___x_2784_ = lean_uint64_xor(v_fold_2781_, v___x_2783_);
v___x_2785_ = lean_uint64_to_usize(v___x_2784_);
v___x_2786_ = lean_usize_of_nat(v___x_2777_);
v___x_2787_ = ((size_t)1ULL);
v___x_2788_ = lean_usize_sub(v___x_2786_, v___x_2787_);
v___x_2789_ = lean_usize_land(v___x_2785_, v___x_2788_);
v___x_2790_ = lean_array_uget_borrowed(v_buckets_2776_, v___x_2789_);
v___x_2791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2775_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(v_m_2792_, v_a_2793_);
lean_dec_ref(v_a_2793_);
lean_dec_ref(v_m_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2795_, lean_object* v_pre_2796_, lean_object* v_post_2797_, lean_object* v_usedLetOnly_2798_, lean_object* v_skipConstInApp_2799_, lean_object* v_skipInstances_2800_, lean_object* v_postApp_2801_, lean_object* v_body_2802_, lean_object* v_x_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v_usedLetOnly_boxed_2810_; uint8_t v_skipConstInApp_boxed_2811_; uint8_t v_skipInstances_boxed_2812_; lean_object* v_res_2813_; 
v_usedLetOnly_boxed_2810_ = lean_unbox(v_usedLetOnly_2798_);
v_skipConstInApp_boxed_2811_ = lean_unbox(v_skipConstInApp_2799_);
v_skipInstances_boxed_2812_ = lean_unbox(v_skipInstances_2800_);
v_res_2813_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2795_, v_pre_2796_, v_post_2797_, v_usedLetOnly_boxed_2810_, v_skipConstInApp_boxed_2811_, v_skipInstances_boxed_2812_, v_postApp_2801_, v_body_2802_, v_x_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2817_, lean_object* v_pre_2818_, lean_object* v_post_2819_, uint8_t v_usedLetOnly_2820_, uint8_t v_skipConstInApp_2821_, uint8_t v_skipInstances_2822_, lean_object* v_postApp_2823_, lean_object* v_body_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_array_push(v_fvars_2817_, v_x_2825_);
v___x_2833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2818_, v_post_2819_, v_usedLetOnly_2820_, v_skipConstInApp_2821_, v_skipInstances_2822_, v_postApp_2823_, v___x_2832_, v_body_2824_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2834_, lean_object* v_pre_2835_, lean_object* v_post_2836_, lean_object* v_usedLetOnly_2837_, lean_object* v_skipConstInApp_2838_, lean_object* v_skipInstances_2839_, lean_object* v_postApp_2840_, lean_object* v_body_2841_, lean_object* v_x_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_usedLetOnly_boxed_2849_; uint8_t v_skipConstInApp_boxed_2850_; uint8_t v_skipInstances_boxed_2851_; lean_object* v_res_2852_; 
v_usedLetOnly_boxed_2849_ = lean_unbox(v_usedLetOnly_2837_);
v_skipConstInApp_boxed_2850_ = lean_unbox(v_skipConstInApp_2838_);
v_skipInstances_boxed_2851_ = lean_unbox(v_skipInstances_2839_);
v_res_2852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2834_, v_pre_2835_, v_post_2836_, v_usedLetOnly_boxed_2849_, v_skipConstInApp_boxed_2850_, v_skipInstances_boxed_2851_, v_postApp_2840_, v_body_2841_, v_x_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_pre_2853_, lean_object* v_post_2854_, uint8_t v_usedLetOnly_2855_, uint8_t v_skipConstInApp_2856_, uint8_t v_skipInstances_2857_, lean_object* v_postApp_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; 
lean_inc_ref(v_post_2854_);
lean_inc(v___y_2864_);
lean_inc_ref(v___y_2863_);
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc_ref(v_e_2859_);
v___x_2866_ = lean_apply_6(v_post_2854_, v_e_2859_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, lean_box(0));
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2885_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2885_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2885_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
switch(lean_obj_tag(v_a_2867_))
{
case 0:
{
lean_object* v_e_2871_; lean_object* v___x_2873_; 
lean_dec_ref(v_e_2859_);
lean_dec_ref(v_postApp_2858_);
lean_dec_ref(v_post_2854_);
lean_dec_ref(v_pre_2853_);
v_e_2871_ = lean_ctor_get(v_a_2867_, 0);
lean_inc_ref(v_e_2871_);
lean_dec_ref_known(v_a_2867_, 1);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v_e_2871_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_e_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
case 1:
{
lean_object* v_e_2875_; lean_object* v___x_2876_; 
lean_del_object(v___x_2869_);
lean_dec_ref(v_e_2859_);
v_e_2875_ = lean_ctor_get(v_a_2867_, 0);
lean_inc_ref(v_e_2875_);
lean_dec_ref_known(v_a_2867_, 1);
v___x_2876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2853_, v_post_2854_, v_usedLetOnly_2855_, v_skipConstInApp_2856_, v_skipInstances_2857_, v_postApp_2858_, v_e_2875_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
return v___x_2876_;
}
default: 
{
lean_object* v_e_x3f_2877_; 
lean_dec_ref(v_postApp_2858_);
lean_dec_ref(v_post_2854_);
lean_dec_ref(v_pre_2853_);
v_e_x3f_2877_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_e_x3f_2877_);
lean_dec_ref_known(v_a_2867_, 1);
if (lean_obj_tag(v_e_x3f_2877_) == 0)
{
lean_object* v___x_2879_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v_e_2859_);
v___x_2879_ = v___x_2869_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_e_2859_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
else
{
lean_object* v_val_2881_; lean_object* v___x_2883_; 
lean_dec_ref(v_e_2859_);
v_val_2881_ = lean_ctor_get(v_e_x3f_2877_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_e_x3f_2877_, 1);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v_val_2881_);
v___x_2883_ = v___x_2869_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_val_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v_e_2859_);
lean_dec_ref(v_postApp_2858_);
lean_dec_ref(v_post_2854_);
lean_dec_ref(v_pre_2853_);
v_a_2886_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2866_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2866_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2894_, lean_object* v_post_2895_, uint8_t v_usedLetOnly_2896_, uint8_t v_skipConstInApp_2897_, uint8_t v_skipInstances_2898_, lean_object* v_postApp_2899_, lean_object* v_fvars_2900_, lean_object* v_e_2901_, lean_object* v_a_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
if (lean_obj_tag(v_e_2901_) == 6)
{
lean_object* v_binderName_2908_; lean_object* v_binderType_2909_; lean_object* v_body_2910_; uint8_t v_binderInfo_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_binderName_2908_ = lean_ctor_get(v_e_2901_, 0);
lean_inc(v_binderName_2908_);
v_binderType_2909_ = lean_ctor_get(v_e_2901_, 1);
lean_inc_ref(v_binderType_2909_);
v_body_2910_ = lean_ctor_get(v_e_2901_, 2);
lean_inc_ref(v_body_2910_);
v_binderInfo_2911_ = lean_ctor_get_uint8(v_e_2901_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2901_, 3);
v___x_2912_ = lean_box(v_usedLetOnly_2896_);
v___x_2913_ = lean_box(v_skipConstInApp_2897_);
v___x_2914_ = lean_box(v_skipInstances_2898_);
lean_inc_ref(v_postApp_2899_);
lean_inc_ref(v_post_2895_);
lean_inc_ref(v_pre_2894_);
lean_inc_ref(v_fvars_2900_);
v___f_2915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2915_, 0, v_fvars_2900_);
lean_closure_set(v___f_2915_, 1, v_pre_2894_);
lean_closure_set(v___f_2915_, 2, v_post_2895_);
lean_closure_set(v___f_2915_, 3, v___x_2912_);
lean_closure_set(v___f_2915_, 4, v___x_2913_);
lean_closure_set(v___f_2915_, 5, v___x_2914_);
lean_closure_set(v___f_2915_, 6, v_postApp_2899_);
lean_closure_set(v___f_2915_, 7, v_body_2910_);
v___x_2916_ = lean_expr_instantiate_rev(v_binderType_2909_, v_fvars_2900_);
lean_dec_ref(v_fvars_2900_);
lean_dec_ref(v_binderType_2909_);
v___x_2917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2894_, v_post_2895_, v_usedLetOnly_2896_, v_skipConstInApp_2897_, v_skipInstances_2898_, v_postApp_2899_, v___x_2916_, v_a_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2919_ = 0;
v___x_2920_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2908_, v_binderInfo_2911_, v_a_2918_, v___f_2915_, v___x_2919_, v_a_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
return v___x_2920_;
}
else
{
lean_dec_ref(v___f_2915_);
lean_dec(v_binderName_2908_);
return v___x_2917_;
}
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_expr_instantiate_rev(v_e_2901_, v_fvars_2900_);
lean_dec_ref(v_e_2901_);
lean_inc_ref(v_postApp_2899_);
lean_inc_ref(v_post_2895_);
lean_inc_ref(v_pre_2894_);
v___x_2922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2894_, v_post_2895_, v_usedLetOnly_2896_, v_skipConstInApp_2897_, v_skipInstances_2898_, v_postApp_2899_, v___x_2921_, v_a_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; uint8_t v___x_2924_; uint8_t v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = 0;
v___x_2925_ = 1;
v___x_2926_ = 1;
v___x_2927_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2900_, v_a_2923_, v___x_2924_, v_usedLetOnly_2896_, v___x_2924_, v___x_2925_, v___x_2926_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec_ref(v_fvars_2900_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_2894_, v_post_2895_, v_usedLetOnly_2896_, v_skipConstInApp_2897_, v_skipInstances_2898_, v_postApp_2899_, v_a_2928_, v_a_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
return v___x_2929_;
}
else
{
lean_dec_ref(v_postApp_2899_);
lean_dec_ref(v_post_2895_);
lean_dec_ref(v_pre_2894_);
return v___x_2927_;
}
}
else
{
lean_dec_ref(v_fvars_2900_);
lean_dec_ref(v_postApp_2899_);
lean_dec_ref(v_post_2895_);
lean_dec_ref(v_pre_2894_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2930_, lean_object* v_pre_2931_, lean_object* v_post_2932_, uint8_t v_usedLetOnly_2933_, uint8_t v_skipConstInApp_2934_, uint8_t v_skipInstances_2935_, lean_object* v_postApp_2936_, lean_object* v_body_2937_, lean_object* v_x_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_array_push(v_fvars_2930_, v_x_2938_);
v___x_2946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2931_, v_post_2932_, v_usedLetOnly_2933_, v_skipConstInApp_2934_, v_skipInstances_2935_, v_postApp_2936_, v___x_2945_, v_body_2937_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2947_, lean_object* v_pre_2948_, lean_object* v_post_2949_, lean_object* v_usedLetOnly_2950_, lean_object* v_skipConstInApp_2951_, lean_object* v_skipInstances_2952_, lean_object* v_postApp_2953_, lean_object* v_body_2954_, lean_object* v_x_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v_usedLetOnly_boxed_2962_; uint8_t v_skipConstInApp_boxed_2963_; uint8_t v_skipInstances_boxed_2964_; lean_object* v_res_2965_; 
v_usedLetOnly_boxed_2962_ = lean_unbox(v_usedLetOnly_2950_);
v_skipConstInApp_boxed_2963_ = lean_unbox(v_skipConstInApp_2951_);
v_skipInstances_boxed_2964_ = lean_unbox(v_skipInstances_2952_);
v_res_2965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2947_, v_pre_2948_, v_post_2949_, v_usedLetOnly_boxed_2962_, v_skipConstInApp_boxed_2963_, v_skipInstances_boxed_2964_, v_postApp_2953_, v_body_2954_, v_x_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2966_, lean_object* v_post_2967_, uint8_t v_usedLetOnly_2968_, uint8_t v_skipConstInApp_2969_, uint8_t v_skipInstances_2970_, lean_object* v_postApp_2971_, lean_object* v_fvars_2972_, lean_object* v_e_2973_, lean_object* v_a_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
if (lean_obj_tag(v_e_2973_) == 8)
{
lean_object* v_declName_2980_; lean_object* v_type_2981_; lean_object* v_value_2982_; lean_object* v_body_2983_; uint8_t v_nondep_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_declName_2980_ = lean_ctor_get(v_e_2973_, 0);
lean_inc(v_declName_2980_);
v_type_2981_ = lean_ctor_get(v_e_2973_, 1);
lean_inc_ref(v_type_2981_);
v_value_2982_ = lean_ctor_get(v_e_2973_, 2);
lean_inc_ref(v_value_2982_);
v_body_2983_ = lean_ctor_get(v_e_2973_, 3);
lean_inc_ref(v_body_2983_);
v_nondep_2984_ = lean_ctor_get_uint8(v_e_2973_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2973_, 4);
v___x_2985_ = lean_box(v_usedLetOnly_2968_);
v___x_2986_ = lean_box(v_skipConstInApp_2969_);
v___x_2987_ = lean_box(v_skipInstances_2970_);
lean_inc_ref_n(v_postApp_2971_, 2);
lean_inc_ref_n(v_post_2967_, 2);
lean_inc_ref_n(v_pre_2966_, 2);
lean_inc_ref(v_fvars_2972_);
v___f_2988_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2988_, 0, v_fvars_2972_);
lean_closure_set(v___f_2988_, 1, v_pre_2966_);
lean_closure_set(v___f_2988_, 2, v_post_2967_);
lean_closure_set(v___f_2988_, 3, v___x_2985_);
lean_closure_set(v___f_2988_, 4, v___x_2986_);
lean_closure_set(v___f_2988_, 5, v___x_2987_);
lean_closure_set(v___f_2988_, 6, v_postApp_2971_);
lean_closure_set(v___f_2988_, 7, v_body_2983_);
v___x_2989_ = lean_expr_instantiate_rev(v_type_2981_, v_fvars_2972_);
lean_dec_ref(v_type_2981_);
v___x_2990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2966_, v_post_2967_, v_usedLetOnly_2968_, v_skipConstInApp_2969_, v_skipInstances_2970_, v_postApp_2971_, v___x_2989_, v_a_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = lean_expr_instantiate_rev(v_value_2982_, v_fvars_2972_);
lean_dec_ref(v_fvars_2972_);
lean_dec_ref(v_value_2982_);
v___x_2993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2966_, v_post_2967_, v_usedLetOnly_2968_, v_skipConstInApp_2969_, v_skipInstances_2970_, v_postApp_2971_, v___x_2992_, v_a_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = 0;
v___x_2996_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2980_, v_a_2991_, v_a_2994_, v___f_2988_, v_nondep_2984_, v___x_2995_, v_a_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
return v___x_2996_;
}
else
{
lean_dec(v_a_2991_);
lean_dec_ref(v___f_2988_);
lean_dec(v_declName_2980_);
return v___x_2993_;
}
}
else
{
lean_dec_ref(v___f_2988_);
lean_dec_ref(v_value_2982_);
lean_dec(v_declName_2980_);
lean_dec_ref(v_fvars_2972_);
lean_dec_ref(v_postApp_2971_);
lean_dec_ref(v_post_2967_);
lean_dec_ref(v_pre_2966_);
return v___x_2990_;
}
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_expr_instantiate_rev(v_e_2973_, v_fvars_2972_);
lean_dec_ref(v_e_2973_);
lean_inc_ref(v_postApp_2971_);
lean_inc_ref(v_post_2967_);
lean_inc_ref(v_pre_2966_);
v___x_2998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2966_, v_post_2967_, v_usedLetOnly_2968_, v_skipConstInApp_2969_, v_skipInstances_2970_, v_postApp_2971_, v___x_2997_, v_a_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; uint8_t v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = 0;
v___x_3001_ = 1;
v___x_3002_ = l_Lean_Meta_mkLetFVars(v_fvars_2972_, v_a_2999_, v_usedLetOnly_2968_, v___x_3000_, v___x_3001_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec_ref(v_fvars_2972_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_2966_, v_post_2967_, v_usedLetOnly_2968_, v_skipConstInApp_2969_, v_skipInstances_2970_, v_postApp_2971_, v_a_3003_, v_a_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
return v___x_3004_;
}
else
{
lean_dec_ref(v_postApp_2971_);
lean_dec_ref(v_post_2967_);
lean_dec_ref(v_pre_2966_);
return v___x_3002_;
}
}
else
{
lean_dec_ref(v_fvars_2972_);
lean_dec_ref(v_postApp_2971_);
lean_dec_ref(v_post_2967_);
lean_dec_ref(v_pre_2966_);
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3005_, lean_object* v_post_3006_, uint8_t v_usedLetOnly_3007_, uint8_t v_skipConstInApp_3008_, uint8_t v_skipInstances_3009_, lean_object* v_postApp_3010_, size_t v_sz_3011_, size_t v_i_3012_, lean_object* v_bs_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_usize_dec_lt(v_i_3012_, v_sz_3011_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_dec_ref(v_postApp_3010_);
lean_dec_ref(v_post_3006_);
lean_dec_ref(v_pre_3005_);
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_bs_3013_);
return v___x_3021_;
}
else
{
lean_object* v_v_3022_; lean_object* v___x_3023_; lean_object* v_bs_x27_3024_; lean_object* v___x_3025_; 
v_v_3022_ = lean_array_uget(v_bs_3013_, v_i_3012_);
v___x_3023_ = lean_unsigned_to_nat(0u);
v_bs_x27_3024_ = lean_array_uset(v_bs_3013_, v_i_3012_, v___x_3023_);
lean_inc_ref(v_postApp_3010_);
lean_inc_ref(v_post_3006_);
lean_inc_ref(v_pre_3005_);
v___x_3025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3005_, v_post_3006_, v_usedLetOnly_3007_, v_skipConstInApp_3008_, v_skipInstances_3009_, v_postApp_3010_, v_v_3022_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_add(v_i_3012_, v___x_3027_);
v___x_3029_ = lean_array_uset(v_bs_x27_3024_, v_i_3012_, v_a_3026_);
v_i_3012_ = v___x_3028_;
v_bs_3013_ = v___x_3029_;
goto _start;
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v_bs_x27_3024_);
lean_dec_ref(v_postApp_3010_);
lean_dec_ref(v_post_3006_);
lean_dec_ref(v_pre_3005_);
v_a_3031_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3025_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3025_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0(lean_object* v_pre_3039_, lean_object* v_post_3040_, uint8_t v_usedLetOnly_3041_, uint8_t v_skipConstInApp_3042_, uint8_t v_skipInstances_3043_, lean_object* v_postApp_3044_, lean_object* v___x_3045_, lean_object* v___y_3046_, lean_object* v_b_3047_, lean_object* v_a_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3039_, v_post_3040_, v_usedLetOnly_3041_, v_skipConstInApp_3042_, v_skipInstances_3043_, v_postApp_3044_, v___x_3045_, v___y_3046_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3064_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3059_ = lean_array_fset(v_b_3047_, v_a_3048_, v_a_3055_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3060_);
v___x_3062_ = v___x_3057_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v_b_3047_);
v_a_3065_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3054_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3054_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed(lean_object* v_pre_3073_, lean_object* v_post_3074_, lean_object* v_usedLetOnly_3075_, lean_object* v_skipConstInApp_3076_, lean_object* v_skipInstances_3077_, lean_object* v_postApp_3078_, lean_object* v___x_3079_, lean_object* v___y_3080_, lean_object* v_b_3081_, lean_object* v_a_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
uint8_t v_usedLetOnly_boxed_3088_; uint8_t v_skipConstInApp_boxed_3089_; uint8_t v_skipInstances_boxed_3090_; lean_object* v_res_3091_; 
v_usedLetOnly_boxed_3088_ = lean_unbox(v_usedLetOnly_3075_);
v_skipConstInApp_boxed_3089_ = lean_unbox(v_skipConstInApp_3076_);
v_skipInstances_boxed_3090_ = lean_unbox(v_skipInstances_3077_);
v_res_3091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0(v_pre_3073_, v_post_3074_, v_usedLetOnly_boxed_3088_, v_skipConstInApp_boxed_3089_, v_skipInstances_boxed_3090_, v_postApp_3078_, v___x_3079_, v___y_3080_, v_b_3081_, v_a_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v_a_3082_);
lean_dec(v___y_3080_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_upperBound_3092_, lean_object* v___x_3093_, lean_object* v_pre_3094_, lean_object* v_post_3095_, uint8_t v_usedLetOnly_3096_, uint8_t v_skipConstInApp_3097_, uint8_t v_skipInstances_3098_, lean_object* v_postApp_3099_, lean_object* v_a_3100_, lean_object* v_b_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___y_3109_; uint8_t v___x_3132_; 
v___x_3132_ = lean_nat_dec_lt(v_a_3100_, v_upperBound_3092_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
lean_dec(v_a_3100_);
lean_dec_ref(v_postApp_3099_);
lean_dec_ref(v_post_3095_);
lean_dec_ref(v_pre_3094_);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_b_3101_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3134_ = lean_array_fget_borrowed(v_b_3101_, v_a_3100_);
v___x_3135_ = lean_array_get_size(v___x_3093_);
v___x_3136_ = lean_nat_dec_lt(v_a_3100_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___f_3140_; 
lean_inc(v___x_3134_);
v___x_3137_ = lean_box(v_usedLetOnly_3096_);
v___x_3138_ = lean_box(v_skipConstInApp_3097_);
v___x_3139_ = lean_box(v_skipInstances_3098_);
lean_inc(v_a_3100_);
lean_inc(v___y_3102_);
lean_inc_ref(v_postApp_3099_);
lean_inc_ref(v_post_3095_);
lean_inc_ref(v_pre_3094_);
v___f_3140_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3140_, 0, v_pre_3094_);
lean_closure_set(v___f_3140_, 1, v_post_3095_);
lean_closure_set(v___f_3140_, 2, v___x_3137_);
lean_closure_set(v___f_3140_, 3, v___x_3138_);
lean_closure_set(v___f_3140_, 4, v___x_3139_);
lean_closure_set(v___f_3140_, 5, v_postApp_3099_);
lean_closure_set(v___f_3140_, 6, v___x_3134_);
lean_closure_set(v___f_3140_, 7, v___y_3102_);
lean_closure_set(v___f_3140_, 8, v_b_3101_);
lean_closure_set(v___f_3140_, 9, v_a_3100_);
v___y_3109_ = v___f_3140_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3141_; uint8_t v_isInstance_3142_; 
v___x_3141_ = lean_array_fget_borrowed(v___x_3093_, v_a_3100_);
v_isInstance_3142_ = lean_ctor_get_uint8(v___x_3141_, sizeof(void*)*1 + 4);
if (v_isInstance_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___f_3146_; 
lean_inc(v___x_3134_);
v___x_3143_ = lean_box(v_usedLetOnly_3096_);
v___x_3144_ = lean_box(v_skipConstInApp_3097_);
v___x_3145_ = lean_box(v_skipInstances_3098_);
lean_inc(v_a_3100_);
lean_inc(v___y_3102_);
lean_inc_ref(v_postApp_3099_);
lean_inc_ref(v_post_3095_);
lean_inc_ref(v_pre_3094_);
v___f_3146_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3146_, 0, v_pre_3094_);
lean_closure_set(v___f_3146_, 1, v_post_3095_);
lean_closure_set(v___f_3146_, 2, v___x_3143_);
lean_closure_set(v___f_3146_, 3, v___x_3144_);
lean_closure_set(v___f_3146_, 4, v___x_3145_);
lean_closure_set(v___f_3146_, 5, v_postApp_3099_);
lean_closure_set(v___f_3146_, 6, v___x_3134_);
lean_closure_set(v___f_3146_, 7, v___y_3102_);
lean_closure_set(v___f_3146_, 8, v_b_3101_);
lean_closure_set(v___f_3146_, 9, v_a_3100_);
v___y_3109_ = v___f_3146_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3147_; lean_object* v___f_3148_; 
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_b_3101_);
v___f_3148_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3148_, 0, v___x_3147_);
v___y_3109_ = v___f_3148_;
goto v___jp_3108_;
}
}
}
v___jp_3108_:
{
lean_object* v___x_3110_; 
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
v___x_3110_ = lean_apply_5(v___y_3109_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, lean_box(0));
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3123_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3123_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3123_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
if (lean_obj_tag(v_a_3111_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; 
lean_dec(v_a_3100_);
lean_dec_ref(v_postApp_3099_);
lean_dec_ref(v_post_3095_);
lean_dec_ref(v_pre_3094_);
v_a_3115_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v_a_3111_, 1);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v_a_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_del_object(v___x_3113_);
v_a_3119_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v_a_3111_, 1);
v___x_3120_ = lean_unsigned_to_nat(1u);
v___x_3121_ = lean_nat_add(v_a_3100_, v___x_3120_);
lean_dec(v_a_3100_);
v_a_3100_ = v___x_3121_;
v_b_3101_ = v_a_3119_;
goto _start;
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3100_);
lean_dec_ref(v_postApp_3099_);
lean_dec_ref(v_post_3095_);
lean_dec_ref(v_pre_3094_);
v_a_3124_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3110_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3110_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3149_, lean_object* v_pre_3150_, lean_object* v_post_3151_, uint8_t v_usedLetOnly_3152_, uint8_t v_skipConstInApp_3153_, lean_object* v_postApp_3154_, lean_object* v___y_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_f_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; 
if (lean_obj_tag(v_x_3156_) == 5)
{
lean_object* v_fn_3218_; lean_object* v_arg_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_fn_3218_ = lean_ctor_get(v_x_3156_, 0);
lean_inc_ref(v_fn_3218_);
v_arg_3219_ = lean_ctor_get(v_x_3156_, 1);
lean_inc_ref(v_arg_3219_);
lean_dec_ref_known(v_x_3156_, 2);
v___x_3220_ = lean_array_set(v_x_3157_, v_x_3158_, v_arg_3219_);
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_sub(v_x_3158_, v___x_3221_);
lean_dec(v_x_3158_);
v_x_3156_ = v_fn_3218_;
v_x_3157_ = v___x_3220_;
v_x_3158_ = v___x_3222_;
goto _start;
}
else
{
lean_dec(v_x_3158_);
if (v_skipConstInApp_3153_ == 0)
{
goto v___jp_3215_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Lean_Expr_isConst(v_x_3156_);
if (v___x_3224_ == 0)
{
goto v___jp_3215_;
}
else
{
v_f_3166_ = v_x_3156_;
v___y_3167_ = v___y_3159_;
v___y_3168_ = v___y_3160_;
v___y_3169_ = v___y_3161_;
v___y_3170_ = v___y_3162_;
v___y_3171_ = v___y_3163_;
goto v___jp_3165_;
}
}
}
v___jp_3165_:
{
if (v_skipInstances_3149_ == 0)
{
size_t v_sz_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v_sz_3172_ = lean_array_size(v_x_3157_);
v___x_3173_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_3154_);
lean_inc_ref(v_post_3151_);
lean_inc_ref(v_pre_3150_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3150_, v_post_3151_, v_usedLetOnly_3152_, v_skipConstInApp_3153_, v_skipInstances_3149_, v_postApp_3154_, v_sz_3172_, v___x_3173_, v_x_3157_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v___x_3176_ = l_Lean_mkAppN(v_f_3166_, v_a_3175_);
lean_dec(v_a_3175_);
lean_inc_ref(v_postApp_3154_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
v___x_3177_ = lean_apply_7(v_postApp_3154_, v___y_3155_, v___x_3176_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, lean_box(0));
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3150_, v_post_3151_, v_usedLetOnly_3152_, v_skipConstInApp_3153_, v_skipInstances_3149_, v_postApp_3154_, v_a_3178_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3179_;
}
else
{
lean_dec_ref(v_postApp_3154_);
lean_dec_ref(v_post_3151_);
lean_dec_ref(v_pre_3150_);
return v___x_3177_;
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref(v_f_3166_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_postApp_3154_);
lean_dec_ref(v_post_3151_);
lean_dec_ref(v_pre_3150_);
v_a_3180_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3174_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3174_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_array_get_size(v_x_3157_);
lean_inc_ref(v_f_3166_);
v___x_3189_ = l_Lean_Meta_getFunInfoNArgs(v_f_3166_, v___x_3188_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v_paramInfo_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v_paramInfo_3191_ = lean_ctor_get(v_a_3190_, 0);
lean_inc_ref(v_paramInfo_3191_);
lean_dec(v_a_3190_);
v___x_3192_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_3154_);
lean_inc_ref(v_post_3151_);
lean_inc_ref(v_pre_3150_);
v___x_3193_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v___x_3188_, v_paramInfo_3191_, v_pre_3150_, v_post_3151_, v_usedLetOnly_3152_, v_skipConstInApp_3153_, v_skipInstances_3149_, v_postApp_3154_, v___x_3192_, v_x_3157_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec_ref(v_paramInfo_3191_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = l_Lean_mkAppN(v_f_3166_, v_a_3194_);
lean_dec(v_a_3194_);
lean_inc_ref(v_postApp_3154_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
v___x_3196_ = lean_apply_7(v_postApp_3154_, v___y_3155_, v___x_3195_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, lean_box(0));
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3150_, v_post_3151_, v_usedLetOnly_3152_, v_skipConstInApp_3153_, v_skipInstances_3149_, v_postApp_3154_, v_a_3197_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3198_;
}
else
{
lean_dec_ref(v_postApp_3154_);
lean_dec_ref(v_post_3151_);
lean_dec_ref(v_pre_3150_);
return v___x_3196_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v_f_3166_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_postApp_3154_);
lean_dec_ref(v_post_3151_);
lean_dec_ref(v_pre_3150_);
v_a_3199_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3193_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3193_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref(v_f_3166_);
lean_dec_ref(v_x_3157_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_postApp_3154_);
lean_dec_ref(v_post_3151_);
lean_dec_ref(v_pre_3150_);
v_a_3207_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3189_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3189_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
v___jp_3215_:
{
lean_object* v___x_3216_; 
lean_inc_ref(v_postApp_3154_);
lean_inc_ref(v_post_3151_);
lean_inc_ref(v_pre_3150_);
v___x_3216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3150_, v_post_3151_, v_usedLetOnly_3152_, v_skipConstInApp_3153_, v_skipInstances_3149_, v_postApp_3154_, v_x_3156_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v_f_3166_ = v_a_3217_;
v___y_3167_ = v___y_3159_;
v___y_3168_ = v___y_3160_;
v___y_3169_ = v___y_3161_;
v___y_3170_ = v___y_3162_;
v___y_3171_ = v___y_3163_;
goto v___jp_3165_;
}
else
{
lean_dec_ref(v_x_3157_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_postApp_3154_);
lean_dec_ref(v_post_3151_);
lean_dec_ref(v_pre_3150_);
return v___x_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3225_, lean_object* v_pre_3226_, lean_object* v_e_3227_, lean_object* v_post_3228_, uint8_t v_usedLetOnly_3229_, uint8_t v_skipConstInApp_3230_, uint8_t v_skipInstances_3231_, lean_object* v_postApp_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Core_checkSystem(v___x_3225_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v___x_3240_; 
lean_dec_ref_known(v___x_3239_, 1);
lean_inc_ref(v_pre_3226_);
lean_inc(v___y_3237_);
lean_inc_ref(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
lean_inc_ref(v_e_3227_);
v___x_3240_ = lean_apply_6(v_pre_3226_, v_e_3227_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, lean_box(0));
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3289_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3289_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3289_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___y_3246_; 
switch(lean_obj_tag(v_a_3241_))
{
case 0:
{
lean_object* v_e_3281_; lean_object* v___x_3283_; 
lean_dec_ref(v_postApp_3232_);
lean_dec_ref(v_post_3228_);
lean_dec_ref(v_e_3227_);
lean_dec_ref(v_pre_3226_);
v_e_3281_ = lean_ctor_get(v_a_3241_, 0);
lean_inc_ref(v_e_3281_);
lean_dec_ref_known(v_a_3241_, 1);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v_e_3281_);
v___x_3283_ = v___x_3243_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_e_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
case 1:
{
lean_object* v_e_3285_; lean_object* v___x_3286_; 
lean_del_object(v___x_3243_);
lean_dec_ref(v_e_3227_);
v_e_3285_ = lean_ctor_get(v_a_3241_, 0);
lean_inc_ref(v_e_3285_);
lean_dec_ref_known(v_a_3241_, 1);
v___x_3286_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v_e_3285_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3286_;
}
default: 
{
lean_object* v_e_x3f_3287_; 
lean_del_object(v___x_3243_);
v_e_x3f_3287_ = lean_ctor_get(v_a_3241_, 0);
lean_inc(v_e_x3f_3287_);
lean_dec_ref_known(v_a_3241_, 1);
if (lean_obj_tag(v_e_x3f_3287_) == 0)
{
v___y_3246_ = v_e_3227_;
goto v___jp_3245_;
}
else
{
lean_object* v_val_3288_; 
lean_dec_ref(v_e_3227_);
v_val_3288_ = lean_ctor_get(v_e_x3f_3287_, 0);
lean_inc(v_val_3288_);
lean_dec_ref_known(v_e_x3f_3287_, 1);
v___y_3246_ = v_val_3288_;
goto v___jp_3245_;
}
}
}
v___jp_3245_:
{
switch(lean_obj_tag(v___y_3246_))
{
case 7:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___x_3247_, v___y_3246_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3248_;
}
case 6:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___x_3249_, v___y_3246_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3250_;
}
case 8:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___x_3251_, v___y_3246_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3252_;
}
case 5:
{
lean_object* v_dummy_3253_; lean_object* v_nargs_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_dummy_3253_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3254_ = l_Lean_Expr_getAppNumArgs(v___y_3246_);
lean_inc(v_nargs_3254_);
v___x_3255_ = lean_mk_array(v_nargs_3254_, v_dummy_3253_);
v___x_3256_ = lean_unsigned_to_nat(1u);
v___x_3257_ = lean_nat_sub(v_nargs_3254_, v___x_3256_);
lean_dec(v_nargs_3254_);
lean_inc_ref(v___y_3246_);
v___x_3258_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3231_, v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_postApp_3232_, v___y_3246_, v___y_3246_, v___x_3255_, v___x_3257_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3258_;
}
case 10:
{
lean_object* v_data_3259_; lean_object* v_expr_3260_; lean_object* v___x_3261_; 
v_data_3259_ = lean_ctor_get(v___y_3246_, 0);
v_expr_3260_ = lean_ctor_get(v___y_3246_, 1);
lean_inc_ref(v_expr_3260_);
lean_inc_ref(v_postApp_3232_);
lean_inc_ref(v_post_3228_);
lean_inc_ref(v_pre_3226_);
v___x_3261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v_expr_3260_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; size_t v___x_3263_; size_t v___x_3264_; uint8_t v___x_3265_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3261_, 1);
v___x_3263_ = lean_ptr_addr(v_expr_3260_);
v___x_3264_ = lean_ptr_addr(v_a_3262_);
v___x_3265_ = lean_usize_dec_eq(v___x_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_inc(v_data_3259_);
lean_dec_ref_known(v___y_3246_, 2);
v___x_3266_ = l_Lean_Expr_mdata___override(v_data_3259_, v_a_3262_);
v___x_3267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___x_3266_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; 
lean_dec(v_a_3262_);
v___x_3268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___y_3246_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3268_;
}
}
else
{
lean_dec_ref_known(v___y_3246_, 2);
lean_dec_ref(v_postApp_3232_);
lean_dec_ref(v_post_3228_);
lean_dec_ref(v_pre_3226_);
return v___x_3261_;
}
}
case 11:
{
lean_object* v_typeName_3269_; lean_object* v_idx_3270_; lean_object* v_struct_3271_; lean_object* v___x_3272_; 
v_typeName_3269_ = lean_ctor_get(v___y_3246_, 0);
v_idx_3270_ = lean_ctor_get(v___y_3246_, 1);
v_struct_3271_ = lean_ctor_get(v___y_3246_, 2);
lean_inc_ref(v_struct_3271_);
lean_inc_ref(v_postApp_3232_);
lean_inc_ref(v_post_3228_);
lean_inc_ref(v_pre_3226_);
v___x_3272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v_struct_3271_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; size_t v___x_3274_; size_t v___x_3275_; uint8_t v___x_3276_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
v___x_3274_ = lean_ptr_addr(v_struct_3271_);
v___x_3275_ = lean_ptr_addr(v_a_3273_);
v___x_3276_ = lean_usize_dec_eq(v___x_3274_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_inc(v_idx_3270_);
lean_inc(v_typeName_3269_);
lean_dec_ref_known(v___y_3246_, 3);
v___x_3277_ = l_Lean_Expr_proj___override(v_typeName_3269_, v_idx_3270_, v_a_3273_);
v___x_3278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___x_3277_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; 
lean_dec(v_a_3273_);
v___x_3279_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___y_3246_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3279_;
}
}
else
{
lean_dec_ref_known(v___y_3246_, 3);
lean_dec_ref(v_postApp_3232_);
lean_dec_ref(v_post_3228_);
lean_dec_ref(v_pre_3226_);
return v___x_3272_;
}
}
default: 
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3226_, v_post_3228_, v_usedLetOnly_3229_, v_skipConstInApp_3230_, v_skipInstances_3231_, v_postApp_3232_, v___y_3246_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3280_;
}
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec_ref(v_postApp_3232_);
lean_dec_ref(v_post_3228_);
lean_dec_ref(v_e_3227_);
lean_dec_ref(v_pre_3226_);
v_a_3290_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3240_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3240_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v_postApp_3232_);
lean_dec_ref(v_post_3228_);
lean_dec_ref(v_e_3227_);
lean_dec_ref(v_pre_3226_);
v_a_3298_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3239_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3239_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3306_, lean_object* v_pre_3307_, lean_object* v_e_3308_, lean_object* v_post_3309_, lean_object* v_usedLetOnly_3310_, lean_object* v_skipConstInApp_3311_, lean_object* v_skipInstances_3312_, lean_object* v_postApp_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v_usedLetOnly_boxed_3320_; uint8_t v_skipConstInApp_boxed_3321_; uint8_t v_skipInstances_boxed_3322_; lean_object* v_res_3323_; 
v_usedLetOnly_boxed_3320_ = lean_unbox(v_usedLetOnly_3310_);
v_skipConstInApp_boxed_3321_ = lean_unbox(v_skipConstInApp_3311_);
v_skipInstances_boxed_3322_ = lean_unbox(v_skipInstances_3312_);
v_res_3323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3306_, v_pre_3307_, v_e_3308_, v_post_3309_, v_usedLetOnly_boxed_3320_, v_skipConstInApp_boxed_3321_, v_skipInstances_boxed_3322_, v_postApp_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3324_, lean_object* v_post_3325_, uint8_t v_usedLetOnly_3326_, uint8_t v_skipConstInApp_3327_, uint8_t v_skipInstances_3328_, lean_object* v_postApp_3329_, lean_object* v_e_3330_, lean_object* v_a_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_inc(v_a_3331_);
v___x_3337_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3337_, 0, lean_box(0));
lean_closure_set(v___x_3337_, 1, lean_box(0));
lean_closure_set(v___x_3337_, 2, v_a_3331_);
v___x_3338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3337_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3373_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3373_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3373_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(v_a_3339_, v_e_3330_);
lean_dec(v_a_3339_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; 
lean_del_object(v___x_3341_);
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3345_ = lean_box(v_usedLetOnly_3326_);
v___x_3346_ = lean_box(v_skipConstInApp_3327_);
v___x_3347_ = lean_box(v_skipInstances_3328_);
lean_inc_ref(v_e_3330_);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 14, 8);
lean_closure_set(v___f_3348_, 0, v___x_3344_);
lean_closure_set(v___f_3348_, 1, v_pre_3324_);
lean_closure_set(v___f_3348_, 2, v_e_3330_);
lean_closure_set(v___f_3348_, 3, v_post_3325_);
lean_closure_set(v___f_3348_, 4, v___x_3345_);
lean_closure_set(v___f_3348_, 5, v___x_3346_);
lean_closure_set(v___f_3348_, 6, v___x_3347_);
lean_closure_set(v___f_3348_, 7, v_postApp_3329_);
v___x_3349_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3348_, v_a_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___f_3351_; lean_object* v___x_3352_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_n(v_a_3350_, 2);
lean_dec_ref_known(v___x_3349_, 1);
lean_inc(v_a_3331_);
v___f_3351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3351_, 0, v_a_3331_);
lean_closure_set(v___f_3351_, 1, v_e_3330_);
lean_closure_set(v___f_3351_, 2, v_a_3350_);
v___x_3352_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3351_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v___x_3352_, 0);
lean_dec(v_unused_3360_);
v___x_3354_ = v___x_3352_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v___x_3352_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_a_3350_);
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3350_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3350_);
v_a_3361_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3352_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3352_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_dec_ref(v_e_3330_);
return v___x_3349_;
}
}
else
{
lean_object* v_val_3369_; lean_object* v___x_3371_; 
lean_dec_ref(v_e_3330_);
lean_dec_ref(v_postApp_3329_);
lean_dec_ref(v_post_3325_);
lean_dec_ref(v_pre_3324_);
v_val_3369_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v___x_3343_, 1);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v_val_3369_);
v___x_3371_ = v___x_3341_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_val_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref(v_e_3330_);
lean_dec_ref(v_postApp_3329_);
lean_dec_ref(v_post_3325_);
lean_dec_ref(v_pre_3324_);
v_a_3374_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3338_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3338_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3382_, lean_object* v_post_3383_, uint8_t v_usedLetOnly_3384_, uint8_t v_skipConstInApp_3385_, uint8_t v_skipInstances_3386_, lean_object* v_postApp_3387_, lean_object* v_fvars_3388_, lean_object* v_e_3389_, lean_object* v_a_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
if (lean_obj_tag(v_e_3389_) == 7)
{
lean_object* v_binderName_3396_; lean_object* v_binderType_3397_; lean_object* v_body_3398_; uint8_t v_binderInfo_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_binderName_3396_ = lean_ctor_get(v_e_3389_, 0);
lean_inc(v_binderName_3396_);
v_binderType_3397_ = lean_ctor_get(v_e_3389_, 1);
lean_inc_ref(v_binderType_3397_);
v_body_3398_ = lean_ctor_get(v_e_3389_, 2);
lean_inc_ref(v_body_3398_);
v_binderInfo_3399_ = lean_ctor_get_uint8(v_e_3389_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3389_, 3);
v___x_3400_ = lean_box(v_usedLetOnly_3384_);
v___x_3401_ = lean_box(v_skipConstInApp_3385_);
v___x_3402_ = lean_box(v_skipInstances_3386_);
lean_inc_ref(v_postApp_3387_);
lean_inc_ref(v_post_3383_);
lean_inc_ref(v_pre_3382_);
lean_inc_ref(v_fvars_3388_);
v___f_3403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3403_, 0, v_fvars_3388_);
lean_closure_set(v___f_3403_, 1, v_pre_3382_);
lean_closure_set(v___f_3403_, 2, v_post_3383_);
lean_closure_set(v___f_3403_, 3, v___x_3400_);
lean_closure_set(v___f_3403_, 4, v___x_3401_);
lean_closure_set(v___f_3403_, 5, v___x_3402_);
lean_closure_set(v___f_3403_, 6, v_postApp_3387_);
lean_closure_set(v___f_3403_, 7, v_body_3398_);
v___x_3404_ = lean_expr_instantiate_rev(v_binderType_3397_, v_fvars_3388_);
lean_dec_ref(v_fvars_3388_);
lean_dec_ref(v_binderType_3397_);
v___x_3405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3382_, v_post_3383_, v_usedLetOnly_3384_, v_skipConstInApp_3385_, v_skipInstances_3386_, v_postApp_3387_, v___x_3404_, v_a_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = 0;
v___x_3408_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3396_, v_binderInfo_3399_, v_a_3406_, v___f_3403_, v___x_3407_, v_a_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v___x_3408_;
}
else
{
lean_dec_ref(v___f_3403_);
lean_dec(v_binderName_3396_);
return v___x_3405_;
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_expr_instantiate_rev(v_e_3389_, v_fvars_3388_);
lean_dec_ref(v_e_3389_);
lean_inc_ref(v_postApp_3387_);
lean_inc_ref(v_post_3383_);
lean_inc_ref(v_pre_3382_);
v___x_3410_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3382_, v_post_3383_, v_usedLetOnly_3384_, v_skipConstInApp_3385_, v_skipInstances_3386_, v_postApp_3387_, v___x_3409_, v_a_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; uint8_t v___x_3412_; uint8_t v___x_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = 0;
v___x_3413_ = 1;
v___x_3414_ = 1;
v___x_3415_ = l_Lean_Meta_mkForallFVars(v_fvars_3388_, v_a_3411_, v___x_3412_, v_usedLetOnly_3384_, v___x_3413_, v___x_3414_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec_ref(v_fvars_3388_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v___x_3417_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3382_, v_post_3383_, v_usedLetOnly_3384_, v_skipConstInApp_3385_, v_skipInstances_3386_, v_postApp_3387_, v_a_3416_, v_a_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v___x_3417_;
}
else
{
lean_dec_ref(v_postApp_3387_);
lean_dec_ref(v_post_3383_);
lean_dec_ref(v_pre_3382_);
return v___x_3415_;
}
}
else
{
lean_dec_ref(v_fvars_3388_);
lean_dec_ref(v_postApp_3387_);
lean_dec_ref(v_post_3383_);
lean_dec_ref(v_pre_3382_);
return v___x_3410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3418_, lean_object* v_pre_3419_, lean_object* v_post_3420_, uint8_t v_usedLetOnly_3421_, uint8_t v_skipConstInApp_3422_, uint8_t v_skipInstances_3423_, lean_object* v_postApp_3424_, lean_object* v_body_3425_, lean_object* v_x_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_array_push(v_fvars_3418_, v_x_3426_);
v___x_3434_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3419_, v_post_3420_, v_usedLetOnly_3421_, v_skipConstInApp_3422_, v_skipInstances_3423_, v_postApp_3424_, v___x_3433_, v_body_3425_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_3435_, lean_object* v_post_3436_, lean_object* v_usedLetOnly_3437_, lean_object* v_skipConstInApp_3438_, lean_object* v_skipInstances_3439_, lean_object* v_postApp_3440_, lean_object* v_e_3441_, lean_object* v_a_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
uint8_t v_usedLetOnly_boxed_3448_; uint8_t v_skipConstInApp_boxed_3449_; uint8_t v_skipInstances_boxed_3450_; lean_object* v_res_3451_; 
v_usedLetOnly_boxed_3448_ = lean_unbox(v_usedLetOnly_3437_);
v_skipConstInApp_boxed_3449_ = lean_unbox(v_skipConstInApp_3438_);
v_skipInstances_boxed_3450_ = lean_unbox(v_skipInstances_3439_);
v_res_3451_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3435_, v_post_3436_, v_usedLetOnly_boxed_3448_, v_skipConstInApp_boxed_3449_, v_skipInstances_boxed_3450_, v_postApp_3440_, v_e_3441_, v_a_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v_a_3442_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3452_, lean_object* v_post_3453_, lean_object* v_usedLetOnly_3454_, lean_object* v_skipConstInApp_3455_, lean_object* v_skipInstances_3456_, lean_object* v_postApp_3457_, lean_object* v_sz_3458_, lean_object* v_i_3459_, lean_object* v_bs_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
uint8_t v_usedLetOnly_boxed_3467_; uint8_t v_skipConstInApp_boxed_3468_; uint8_t v_skipInstances_boxed_3469_; size_t v_sz_boxed_3470_; size_t v_i_boxed_3471_; lean_object* v_res_3472_; 
v_usedLetOnly_boxed_3467_ = lean_unbox(v_usedLetOnly_3454_);
v_skipConstInApp_boxed_3468_ = lean_unbox(v_skipConstInApp_3455_);
v_skipInstances_boxed_3469_ = lean_unbox(v_skipInstances_3456_);
v_sz_boxed_3470_ = lean_unbox_usize(v_sz_3458_);
lean_dec(v_sz_3458_);
v_i_boxed_3471_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_res_3472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3452_, v_post_3453_, v_usedLetOnly_boxed_3467_, v_skipConstInApp_boxed_3468_, v_skipInstances_boxed_3469_, v_postApp_3457_, v_sz_boxed_3470_, v_i_boxed_3471_, v_bs_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3473_, lean_object* v_post_3474_, lean_object* v_usedLetOnly_3475_, lean_object* v_skipConstInApp_3476_, lean_object* v_skipInstances_3477_, lean_object* v_postApp_3478_, lean_object* v_e_3479_, lean_object* v_a_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
uint8_t v_usedLetOnly_boxed_3486_; uint8_t v_skipConstInApp_boxed_3487_; uint8_t v_skipInstances_boxed_3488_; lean_object* v_res_3489_; 
v_usedLetOnly_boxed_3486_ = lean_unbox(v_usedLetOnly_3475_);
v_skipConstInApp_boxed_3487_ = lean_unbox(v_skipConstInApp_3476_);
v_skipInstances_boxed_3488_ = lean_unbox(v_skipInstances_3477_);
v_res_3489_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3473_, v_post_3474_, v_usedLetOnly_boxed_3486_, v_skipConstInApp_boxed_3487_, v_skipInstances_boxed_3488_, v_postApp_3478_, v_e_3479_, v_a_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_a_3480_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3490_, lean_object* v_post_3491_, lean_object* v_usedLetOnly_3492_, lean_object* v_skipConstInApp_3493_, lean_object* v_skipInstances_3494_, lean_object* v_postApp_3495_, lean_object* v_fvars_3496_, lean_object* v_e_3497_, lean_object* v_a_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
uint8_t v_usedLetOnly_boxed_3504_; uint8_t v_skipConstInApp_boxed_3505_; uint8_t v_skipInstances_boxed_3506_; lean_object* v_res_3507_; 
v_usedLetOnly_boxed_3504_ = lean_unbox(v_usedLetOnly_3492_);
v_skipConstInApp_boxed_3505_ = lean_unbox(v_skipConstInApp_3493_);
v_skipInstances_boxed_3506_ = lean_unbox(v_skipInstances_3494_);
v_res_3507_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3490_, v_post_3491_, v_usedLetOnly_boxed_3504_, v_skipConstInApp_boxed_3505_, v_skipInstances_boxed_3506_, v_postApp_3495_, v_fvars_3496_, v_e_3497_, v_a_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v_a_3498_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3508_, lean_object* v_post_3509_, lean_object* v_usedLetOnly_3510_, lean_object* v_skipConstInApp_3511_, lean_object* v_skipInstances_3512_, lean_object* v_postApp_3513_, lean_object* v_fvars_3514_, lean_object* v_e_3515_, lean_object* v_a_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
uint8_t v_usedLetOnly_boxed_3522_; uint8_t v_skipConstInApp_boxed_3523_; uint8_t v_skipInstances_boxed_3524_; lean_object* v_res_3525_; 
v_usedLetOnly_boxed_3522_ = lean_unbox(v_usedLetOnly_3510_);
v_skipConstInApp_boxed_3523_ = lean_unbox(v_skipConstInApp_3511_);
v_skipInstances_boxed_3524_ = lean_unbox(v_skipInstances_3512_);
v_res_3525_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3508_, v_post_3509_, v_usedLetOnly_boxed_3522_, v_skipConstInApp_boxed_3523_, v_skipInstances_boxed_3524_, v_postApp_3513_, v_fvars_3514_, v_e_3515_, v_a_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v_a_3516_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3526_, lean_object* v_post_3527_, lean_object* v_usedLetOnly_3528_, lean_object* v_skipConstInApp_3529_, lean_object* v_skipInstances_3530_, lean_object* v_postApp_3531_, lean_object* v_fvars_3532_, lean_object* v_e_3533_, lean_object* v_a_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
uint8_t v_usedLetOnly_boxed_3540_; uint8_t v_skipConstInApp_boxed_3541_; uint8_t v_skipInstances_boxed_3542_; lean_object* v_res_3543_; 
v_usedLetOnly_boxed_3540_ = lean_unbox(v_usedLetOnly_3528_);
v_skipConstInApp_boxed_3541_ = lean_unbox(v_skipConstInApp_3529_);
v_skipInstances_boxed_3542_ = lean_unbox(v_skipInstances_3530_);
v_res_3543_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3526_, v_post_3527_, v_usedLetOnly_boxed_3540_, v_skipConstInApp_boxed_3541_, v_skipInstances_boxed_3542_, v_postApp_3531_, v_fvars_3532_, v_e_3533_, v_a_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v_a_3534_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_upperBound_3544_, lean_object* v___x_3545_, lean_object* v_pre_3546_, lean_object* v_post_3547_, lean_object* v_usedLetOnly_3548_, lean_object* v_skipConstInApp_3549_, lean_object* v_skipInstances_3550_, lean_object* v_postApp_3551_, lean_object* v_a_3552_, lean_object* v_b_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
uint8_t v_usedLetOnly_boxed_3560_; uint8_t v_skipConstInApp_boxed_3561_; uint8_t v_skipInstances_boxed_3562_; lean_object* v_res_3563_; 
v_usedLetOnly_boxed_3560_ = lean_unbox(v_usedLetOnly_3548_);
v_skipConstInApp_boxed_3561_ = lean_unbox(v_skipConstInApp_3549_);
v_skipInstances_boxed_3562_ = lean_unbox(v_skipInstances_3550_);
v_res_3563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_upperBound_3544_, v___x_3545_, v_pre_3546_, v_post_3547_, v_usedLetOnly_boxed_3560_, v_skipConstInApp_boxed_3561_, v_skipInstances_boxed_3562_, v_postApp_3551_, v_a_3552_, v_b_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___x_3545_);
lean_dec(v_upperBound_3544_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3564_, lean_object* v_pre_3565_, lean_object* v_post_3566_, lean_object* v_usedLetOnly_3567_, lean_object* v_skipConstInApp_3568_, lean_object* v_postApp_3569_, lean_object* v___y_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v_skipInstances_boxed_3580_; uint8_t v_usedLetOnly_boxed_3581_; uint8_t v_skipConstInApp_boxed_3582_; lean_object* v_res_3583_; 
v_skipInstances_boxed_3580_ = lean_unbox(v_skipInstances_3564_);
v_usedLetOnly_boxed_3581_ = lean_unbox(v_usedLetOnly_3567_);
v_skipConstInApp_boxed_3582_ = lean_unbox(v_skipConstInApp_3568_);
v_res_3583_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3580_, v_pre_3565_, v_post_3566_, v_usedLetOnly_boxed_3581_, v_skipConstInApp_boxed_3582_, v_postApp_3569_, v___y_3570_, v_x_3571_, v_x_3572_, v_x_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
return v_res_3583_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_box(0);
v___x_3586_ = lean_unsigned_to_nat(16u);
v___x_3587_ = lean_mk_array(v___x_3586_, v___x_3585_);
return v___x_3587_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v___x_3588_);
return v___x_3590_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3592_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3592_, 0, lean_box(0));
lean_closure_set(v___x_3592_, 1, lean_box(0));
lean_closure_set(v___x_3592_, 2, v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3593_, lean_object* v_pre_3594_, lean_object* v_post_3595_, uint8_t v_usedLetOnly_3596_, uint8_t v_skipConstInApp_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___f_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_a_3607_; lean_object* v___x_3608_; 
v___f_3603_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0));
v___x_3604_ = 0;
v___x_3605_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3);
v___x_3606_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3605_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___x_3606_);
v___x_3608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3594_, v_post_3595_, v_usedLetOnly_3596_, v_skipConstInApp_3597_, v___x_3604_, v___f_3603_, v_input_3593_, v_a_3607_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3610_, 0, lean_box(0));
lean_closure_set(v___x_3610_, 1, lean_box(0));
lean_closure_set(v___x_3610_, 2, v_a_3607_);
v___x_3611_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3610_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v___x_3611_, 0);
lean_dec(v_unused_3619_);
v___x_3613_ = v___x_3611_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_dec(v___x_3611_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v_a_3609_);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3609_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
else
{
lean_dec(v_a_3607_);
return v___x_3608_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3634_, lean_object* v_p_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3647_, lean_object* v_p_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Meta_etaStructReduce(v_e_3647_, v_p_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3655_, lean_object* v_m_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(v_m_3656_, v_a_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3659_, lean_object* v_m_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_00_u03b2_3659_, v_m_3660_, v_a_3661_);
lean_dec_ref(v_a_3661_);
lean_dec_ref(v_m_3660_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_upperBound_3663_, lean_object* v___x_3664_, lean_object* v_pre_3665_, lean_object* v_post_3666_, uint8_t v_usedLetOnly_3667_, uint8_t v_skipConstInApp_3668_, uint8_t v_skipInstances_3669_, lean_object* v_postApp_3670_, lean_object* v___x_3671_, lean_object* v_inst_3672_, lean_object* v_R_3673_, lean_object* v_a_3674_, lean_object* v_b_3675_, lean_object* v_c_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_upperBound_3663_, v___x_3664_, v_pre_3665_, v_post_3666_, v_usedLetOnly_3667_, v_skipConstInApp_3668_, v_skipInstances_3669_, v_postApp_3670_, v_a_3674_, v_b_3675_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_3684_ = _args[0];
lean_object* v___x_3685_ = _args[1];
lean_object* v_pre_3686_ = _args[2];
lean_object* v_post_3687_ = _args[3];
lean_object* v_usedLetOnly_3688_ = _args[4];
lean_object* v_skipConstInApp_3689_ = _args[5];
lean_object* v_skipInstances_3690_ = _args[6];
lean_object* v_postApp_3691_ = _args[7];
lean_object* v___x_3692_ = _args[8];
lean_object* v_inst_3693_ = _args[9];
lean_object* v_R_3694_ = _args[10];
lean_object* v_a_3695_ = _args[11];
lean_object* v_b_3696_ = _args[12];
lean_object* v_c_3697_ = _args[13];
lean_object* v___y_3698_ = _args[14];
lean_object* v___y_3699_ = _args[15];
lean_object* v___y_3700_ = _args[16];
lean_object* v___y_3701_ = _args[17];
lean_object* v___y_3702_ = _args[18];
lean_object* v___y_3703_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3704_; uint8_t v_skipConstInApp_boxed_3705_; uint8_t v_skipInstances_boxed_3706_; lean_object* v_res_3707_; 
v_usedLetOnly_boxed_3704_ = lean_unbox(v_usedLetOnly_3688_);
v_skipConstInApp_boxed_3705_ = lean_unbox(v_skipConstInApp_3689_);
v_skipInstances_boxed_3706_ = lean_unbox(v_skipInstances_3690_);
v_res_3707_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_upperBound_3684_, v___x_3685_, v_pre_3686_, v_post_3687_, v_usedLetOnly_boxed_3704_, v_skipConstInApp_boxed_3705_, v_skipInstances_boxed_3706_, v_postApp_3691_, v___x_3692_, v_inst_3693_, v_R_3694_, v_a_3695_, v_b_3696_, v_c_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec(v___x_3692_);
lean_dec_ref(v___x_3685_);
lean_dec(v_upperBound_3684_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3708_, lean_object* v_name_3709_, uint8_t v_bi_3710_, lean_object* v_type_3711_, lean_object* v_k_3712_, uint8_t v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3709_, v_bi_3710_, v_type_3711_, v_k_3712_, v_kind_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3721_, lean_object* v_name_3722_, lean_object* v_bi_3723_, lean_object* v_type_3724_, lean_object* v_k_3725_, lean_object* v_kind_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
uint8_t v_bi_boxed_3733_; uint8_t v_kind_boxed_3734_; lean_object* v_res_3735_; 
v_bi_boxed_3733_ = lean_unbox(v_bi_3723_);
v_kind_boxed_3734_ = lean_unbox(v_kind_3726_);
v_res_3735_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3721_, v_name_3722_, v_bi_boxed_3733_, v_type_3724_, v_k_3725_, v_kind_boxed_3734_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3736_, lean_object* v_name_3737_, lean_object* v_type_3738_, lean_object* v_val_3739_, lean_object* v_k_3740_, uint8_t v_nondep_3741_, uint8_t v_kind_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3737_, v_type_3738_, v_val_3739_, v_k_3740_, v_nondep_3741_, v_kind_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3750_, lean_object* v_name_3751_, lean_object* v_type_3752_, lean_object* v_val_3753_, lean_object* v_k_3754_, lean_object* v_nondep_3755_, lean_object* v_kind_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
uint8_t v_nondep_boxed_3763_; uint8_t v_kind_boxed_3764_; lean_object* v_res_3765_; 
v_nondep_boxed_3763_ = lean_unbox(v_nondep_3755_);
v_kind_boxed_3764_ = lean_unbox(v_kind_3756_);
v_res_3765_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3750_, v_name_3751_, v_type_3752_, v_val_3753_, v_k_3754_, v_nondep_boxed_3763_, v_kind_boxed_3764_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3766_, lean_object* v_ref_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3767_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3774_, lean_object* v_ref_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3774_, v_ref_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3782_, lean_object* v_x_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3791_, lean_object* v_x_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3791_, v_x_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3800_, lean_object* v_m_3801_, lean_object* v_a_3802_, lean_object* v_b_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3801_, v_a_3802_, v_b_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3805_, lean_object* v_a_3806_, lean_object* v_x_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(v_a_3806_, v_x_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3809_, lean_object* v_a_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_3809_, v_a_3810_, v_x_3811_);
lean_dec(v_x_3811_);
lean_dec_ref(v_a_3810_);
return v_res_3812_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3813_, lean_object* v_a_3814_, lean_object* v_x_3815_){
_start:
{
uint8_t v___x_3816_; 
v___x_3816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3814_, v_x_3815_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3817_, lean_object* v_a_3818_, lean_object* v_x_3819_){
_start:
{
uint8_t v_res_3820_; lean_object* v_r_3821_; 
v_res_3820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3817_, v_a_3818_, v_x_3819_);
lean_dec(v_x_3819_);
lean_dec_ref(v_a_3818_);
v_r_3821_ = lean_box(v_res_3820_);
return v_r_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3822_, lean_object* v_data_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3825_, lean_object* v_a_3826_, lean_object* v_b_3827_, lean_object* v_x_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3826_, v_b_3827_, v_x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3830_, lean_object* v_i_3831_, lean_object* v_source_3832_, lean_object* v_target_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3831_, v_source_3832_, v_target_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3835_, lean_object* v_x_3836_, lean_object* v_x_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3836_, v_x_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3839_, lean_object* v_inst_3840_, lean_object* v_toBind_3841_, lean_object* v___f_3842_, lean_object* v_____do__lift_3843_){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3844_, 0, v_____do__lift_3843_);
lean_closure_set(v___x_3844_, 1, v_binderType_3839_);
v___x_3845_ = lean_apply_2(v_inst_3840_, lean_box(0), v___x_3844_);
v___x_3846_ = lean_apply_4(v_toBind_3841_, lean_box(0), lean_box(0), v___x_3845_, v___f_3842_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3847_, lean_object* v_usedFields_3848_, lean_object* v_binderName_3849_, lean_object* v_body_3850_, lean_object* v_val_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_fieldVal_x3f_3854_, lean_object* v_____do__lift_3855_){
_start:
{
uint8_t v_____do__lift_285__boxed_3856_; lean_object* v_res_3857_; 
v_____do__lift_285__boxed_3856_ = lean_unbox(v_____do__lift_3855_);
v_res_3857_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3847_, v_usedFields_3848_, v_binderName_3849_, v_body_3850_, v_val_3851_, v_inst_3852_, v_inst_3853_, v_fieldVal_x3f_3854_, v_____do__lift_285__boxed_3856_);
lean_dec_ref(v_val_3851_);
lean_dec_ref(v_body_3850_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3858_, lean_object* v_usedFields_3859_, lean_object* v_binderName_3860_, lean_object* v_body_3861_, lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_fieldVal_x3f_3864_, lean_object* v_binderType_3865_, lean_object* v_toBind_3866_, lean_object* v_____x_3867_){
_start:
{
if (lean_obj_tag(v_____x_3867_) == 1)
{
lean_object* v_val_3868_; lean_object* v___f_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_val_3868_ = lean_ctor_get(v_____x_3867_, 0);
lean_inc_n(v_val_3868_, 2);
lean_dec_ref_known(v_____x_3867_, 1);
lean_inc_n(v_inst_3863_, 2);
v___f_3869_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3869_, 0, v_toPure_3858_);
lean_closure_set(v___f_3869_, 1, v_usedFields_3859_);
lean_closure_set(v___f_3869_, 2, v_binderName_3860_);
lean_closure_set(v___f_3869_, 3, v_body_3861_);
lean_closure_set(v___f_3869_, 4, v_val_3868_);
lean_closure_set(v___f_3869_, 5, v_inst_3862_);
lean_closure_set(v___f_3869_, 6, v_inst_3863_);
lean_closure_set(v___f_3869_, 7, v_fieldVal_x3f_3864_);
lean_inc(v_toBind_3866_);
v___f_3870_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3870_, 0, v_binderType_3865_);
lean_closure_set(v___f_3870_, 1, v_inst_3863_);
lean_closure_set(v___f_3870_, 2, v_toBind_3866_);
lean_closure_set(v___f_3870_, 3, v___f_3869_);
v___x_3871_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3871_, 0, v_val_3868_);
v___x_3872_ = lean_apply_2(v_inst_3863_, lean_box(0), v___x_3871_);
v___x_3873_ = lean_apply_4(v_toBind_3866_, lean_box(0), lean_box(0), v___x_3872_, v___f_3870_);
return v___x_3873_;
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_dec(v_____x_3867_);
lean_dec(v_toBind_3866_);
lean_dec_ref(v_binderType_3865_);
lean_dec(v_fieldVal_x3f_3864_);
lean_dec(v_inst_3863_);
lean_dec_ref(v_inst_3862_);
lean_dec_ref(v_body_3861_);
lean_dec(v_binderName_3860_);
lean_dec(v_usedFields_3859_);
v___x_3874_ = lean_box(0);
v___x_3875_ = lean_apply_2(v_toPure_3858_, lean_box(0), v___x_3874_);
return v___x_3875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3879_, lean_object* v_inst_3880_, lean_object* v_fieldVal_x3f_3881_, lean_object* v_usedFields_3882_, lean_object* v_e_3883_){
_start:
{
lean_object* v_toApplicative_3884_; lean_object* v_toBind_3885_; lean_object* v_toPure_3886_; 
v_toApplicative_3884_ = lean_ctor_get(v_inst_3879_, 0);
v_toBind_3885_ = lean_ctor_get(v_inst_3879_, 1);
v_toPure_3886_ = lean_ctor_get(v_toApplicative_3884_, 1);
lean_inc(v_toPure_3886_);
if (lean_obj_tag(v_e_3883_) == 6)
{
lean_object* v_binderName_3891_; lean_object* v_binderType_3892_; lean_object* v_body_3893_; lean_object* v___f_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_inc_n(v_toBind_3885_, 2);
v_binderName_3891_ = lean_ctor_get(v_e_3883_, 0);
lean_inc_n(v_binderName_3891_, 2);
v_binderType_3892_ = lean_ctor_get(v_e_3883_, 1);
lean_inc_ref(v_binderType_3892_);
v_body_3893_ = lean_ctor_get(v_e_3883_, 2);
lean_inc_ref(v_body_3893_);
lean_dec_ref_known(v_e_3883_, 3);
lean_inc(v_fieldVal_x3f_3881_);
v___f_3894_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3894_, 0, v_toPure_3886_);
lean_closure_set(v___f_3894_, 1, v_usedFields_3882_);
lean_closure_set(v___f_3894_, 2, v_binderName_3891_);
lean_closure_set(v___f_3894_, 3, v_body_3893_);
lean_closure_set(v___f_3894_, 4, v_inst_3879_);
lean_closure_set(v___f_3894_, 5, v_inst_3880_);
lean_closure_set(v___f_3894_, 6, v_fieldVal_x3f_3881_);
lean_closure_set(v___f_3894_, 7, v_binderType_3892_);
lean_closure_set(v___f_3894_, 8, v_toBind_3885_);
v___x_3895_ = lean_apply_1(v_fieldVal_x3f_3881_, v_binderName_3891_);
v___x_3896_ = lean_apply_4(v_toBind_3885_, lean_box(0), lean_box(0), v___x_3895_, v___f_3894_);
return v___x_3896_;
}
else
{
lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_fieldVal_x3f_3881_);
lean_dec(v_inst_3880_);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_inst_3879_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; 
v_unused_3914_ = lean_ctor_get(v_inst_3879_, 1);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_inst_3879_, 0);
lean_dec(v_unused_3915_);
v___x_3898_ = v_inst_3879_;
v_isShared_3899_ = v_isSharedCheck_3913_;
goto v_resetjp_3897_;
}
else
{
lean_dec(v_inst_3879_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3913_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = l_Lean_Expr_cleanupAnnotations(v_e_3883_);
v___x_3901_ = l_Lean_Expr_isApp(v___x_3900_);
if (v___x_3901_ == 0)
{
lean_dec_ref(v___x_3900_);
lean_del_object(v___x_3898_);
goto v___jp_3887_;
}
else
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3900_);
v___x_3903_ = l_Lean_Expr_isApp(v___x_3902_);
if (v___x_3903_ == 0)
{
lean_dec_ref(v___x_3902_);
lean_dec_ref(v___x_3900_);
lean_del_object(v___x_3898_);
goto v___jp_3887_;
}
else
{
lean_object* v___x_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___x_3904_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3902_);
lean_dec_ref(v___x_3902_);
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3906_ = l_Lean_Expr_isConstOf(v___x_3904_, v___x_3905_);
lean_dec_ref(v___x_3904_);
if (v___x_3906_ == 0)
{
lean_dec_ref(v___x_3900_);
lean_del_object(v___x_3898_);
goto v___jp_3887_;
}
else
{
lean_object* v_arg_3907_; lean_object* v___x_3909_; 
lean_dec_ref(v_e_3883_);
v_arg_3907_ = lean_ctor_get(v___x_3900_, 1);
lean_inc_ref(v_arg_3907_);
lean_dec_ref(v___x_3900_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 1, v_arg_3907_);
lean_ctor_set(v___x_3898_, 0, v_usedFields_3882_);
v___x_3909_ = v___x_3898_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_usedFields_3882_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_arg_3907_);
v___x_3909_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
v___x_3911_ = lean_apply_2(v_toPure_3886_, lean_box(0), v___x_3910_);
return v___x_3911_;
}
}
}
}
}
}
v___jp_3887_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3888_, 0, v_usedFields_3882_);
lean_ctor_set(v___x_3888_, 1, v_e_3883_);
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
v___x_3890_ = lean_apply_2(v_toPure_3886_, lean_box(0), v___x_3889_);
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3916_, lean_object* v_usedFields_3917_, lean_object* v_binderName_3918_, lean_object* v_body_3919_, lean_object* v_val_3920_, lean_object* v_inst_3921_, lean_object* v_inst_3922_, lean_object* v_fieldVal_x3f_3923_, uint8_t v_____do__lift_3924_){
_start:
{
if (v_____do__lift_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_dec(v_fieldVal_x3f_3923_);
lean_dec(v_inst_3922_);
lean_dec_ref(v_inst_3921_);
lean_dec(v_binderName_3918_);
lean_dec(v_usedFields_3917_);
v___x_3925_ = lean_box(0);
v___x_3926_ = lean_apply_2(v_toPure_3916_, lean_box(0), v___x_3925_);
return v___x_3926_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec(v_toPure_3916_);
v___x_3927_ = l_Lean_NameSet_insert(v_usedFields_3917_, v_binderName_3918_);
v___x_3928_ = lean_expr_instantiate1(v_body_3919_, v_val_3920_);
v___x_3929_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3921_, v_inst_3922_, v_fieldVal_x3f_3923_, v___x_3927_, v___x_3928_);
return v___x_3929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3930_, lean_object* v_inst_3931_, lean_object* v_inst_3932_, lean_object* v_fieldVal_x3f_3933_, lean_object* v_usedFields_3934_, lean_object* v_e_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3931_, v_inst_3932_, v_fieldVal_x3f_3933_, v_usedFields_3934_, v_e_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3937_, lean_object* v_inst_3938_, lean_object* v_fieldVal_x3f_3939_, lean_object* v_toPure_3940_, lean_object* v_____s_3941_){
_start:
{
lean_object* v_fst_3942_; 
v_fst_3942_ = lean_ctor_get(v_____s_3941_, 0);
if (lean_obj_tag(v_fst_3942_) == 0)
{
lean_object* v_snd_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_dec(v_toPure_3940_);
v_snd_3943_ = lean_ctor_get(v_____s_3941_, 1);
lean_inc(v_snd_3943_);
lean_dec_ref(v_____s_3941_);
v___x_3944_ = l_Lean_NameSet_empty;
v___x_3945_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3937_, v_inst_3938_, v_fieldVal_x3f_3939_, v___x_3944_, v_snd_3943_);
return v___x_3945_;
}
else
{
lean_object* v_val_3946_; lean_object* v___x_3947_; 
lean_inc_ref(v_fst_3942_);
lean_dec_ref(v_____s_3941_);
lean_dec(v_fieldVal_x3f_3939_);
lean_dec(v_inst_3938_);
lean_dec_ref(v_inst_3937_);
v_val_3946_ = lean_ctor_get(v_fst_3942_, 0);
lean_inc(v_val_3946_);
lean_dec_ref_known(v_fst_3942_, 1);
v___x_3947_ = lean_apply_2(v_toPure_3940_, lean_box(0), v_val_3946_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3948_, lean_object* v_a_3949_, lean_object* v___x_3950_, lean_object* v_toPure_3951_, lean_object* v_____r_3952_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3953_ = lean_expr_instantiate1(v_body_3948_, v_a_3949_);
v___x_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3950_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
v___x_3956_ = lean_apply_2(v_toPure_3951_, lean_box(0), v___x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3957_, lean_object* v_a_3958_, lean_object* v___x_3959_, lean_object* v_toPure_3960_, lean_object* v_____r_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3957_, v_a_3958_, v___x_3959_, v_toPure_3960_, v_____r_3961_);
lean_dec_ref(v_a_3958_);
lean_dec_ref(v_body_3957_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3965_, lean_object* v_toPure_3966_, lean_object* v___f_3967_, uint8_t v_____do__lift_3968_){
_start:
{
if (v_____do__lift_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec(v___f_3967_);
v___x_3969_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v_snd_3965_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = lean_apply_2(v_toPure_3966_, lean_box(0), v___x_3971_);
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec(v_toPure_3966_);
lean_dec(v_snd_3965_);
v___x_3973_ = lean_box(0);
v___x_3974_ = lean_apply_1(v___f_3967_, v___x_3973_);
return v___x_3974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3975_, lean_object* v_toPure_3976_, lean_object* v___f_3977_, lean_object* v_____do__lift_3978_){
_start:
{
uint8_t v_____do__lift_566__boxed_3979_; lean_object* v_res_3980_; 
v_____do__lift_566__boxed_3979_ = lean_unbox(v_____do__lift_3978_);
v_res_3980_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3975_, v_toPure_3976_, v___f_3977_, v_____do__lift_566__boxed_3979_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3981_, lean_object* v_inst_3982_, lean_object* v_toBind_3983_, lean_object* v___f_3984_, lean_object* v_____do__lift_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3986_, 0, v_____do__lift_3985_);
lean_closure_set(v___x_3986_, 1, v_binderType_3981_);
v___x_3987_ = lean_apply_2(v_inst_3982_, lean_box(0), v___x_3986_);
v___x_3988_ = lean_apply_4(v_toBind_3983_, lean_box(0), lean_box(0), v___x_3987_, v___f_3984_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3989_, lean_object* v_toPure_3990_, lean_object* v_levels_x3f_3991_, lean_object* v_inst_3992_, lean_object* v_toBind_3993_, lean_object* v_a_3994_, lean_object* v_x_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_snd_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4017_; 
v_snd_3997_ = lean_ctor_get(v___y_3996_, 1);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___y_3996_);
if (v_isSharedCheck_4017_ == 0)
{
lean_object* v_unused_4018_; 
v_unused_4018_ = lean_ctor_get(v___y_3996_, 0);
lean_dec(v_unused_4018_);
v___x_3999_ = v___y_3996_;
v_isShared_4000_ = v_isSharedCheck_4017_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_snd_3997_);
lean_dec(v___y_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4017_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
if (lean_obj_tag(v_snd_3997_) == 6)
{
lean_object* v_binderType_4001_; lean_object* v_body_4002_; lean_object* v___f_4003_; 
lean_del_object(v___x_3999_);
v_binderType_4001_ = lean_ctor_get(v_snd_3997_, 1);
lean_inc_ref(v_binderType_4001_);
v_body_4002_ = lean_ctor_get(v_snd_3997_, 2);
lean_inc(v_toPure_3990_);
lean_inc(v___x_3989_);
lean_inc_ref(v_a_3994_);
lean_inc_ref(v_body_4002_);
v___f_4003_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_4003_, 0, v_body_4002_);
lean_closure_set(v___f_4003_, 1, v_a_3994_);
lean_closure_set(v___f_4003_, 2, v___x_3989_);
lean_closure_set(v___f_4003_, 3, v_toPure_3990_);
if (lean_obj_tag(v_levels_x3f_3991_) == 0)
{
lean_object* v___f_4004_; lean_object* v___f_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_dec(v___x_3989_);
v___f_4004_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4004_, 0, v_snd_3997_);
lean_closure_set(v___f_4004_, 1, v_toPure_3990_);
lean_closure_set(v___f_4004_, 2, v___f_4003_);
lean_inc(v_toBind_3993_);
lean_inc(v_inst_3992_);
v___f_4005_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4005_, 0, v_binderType_4001_);
lean_closure_set(v___f_4005_, 1, v_inst_3992_);
lean_closure_set(v___f_4005_, 2, v_toBind_3993_);
lean_closure_set(v___f_4005_, 3, v___f_4004_);
v___x_4006_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_4006_, 0, v_a_3994_);
v___x_4007_ = lean_apply_2(v_inst_3992_, lean_box(0), v___x_4006_);
v___x_4008_ = lean_apply_4(v_toBind_3993_, lean_box(0), lean_box(0), v___x_4007_, v___f_4005_);
return v___x_4008_;
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_inc_ref(v_body_4002_);
lean_dec_ref(v___f_4003_);
lean_dec_ref(v_binderType_4001_);
lean_dec_ref_known(v_snd_3997_, 3);
lean_dec(v_toBind_3993_);
lean_dec(v_inst_3992_);
v___x_4009_ = lean_box(0);
v___x_4010_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_4002_, v_a_3994_, v___x_3989_, v_toPure_3990_, v___x_4009_);
lean_dec_ref(v_a_3994_);
lean_dec_ref(v_body_4002_);
return v___x_4010_;
}
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
lean_dec_ref(v_a_3994_);
lean_dec(v_toBind_3993_);
lean_dec(v_inst_3992_);
lean_dec(v___x_3989_);
v___x_4011_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4011_);
v___x_4013_ = v___x_3999_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4011_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_snd_3997_);
v___x_4013_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
v___x_4015_ = lean_apply_2(v_toPure_3990_, lean_box(0), v___x_4014_);
return v___x_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_4019_, lean_object* v_toPure_4020_, lean_object* v_levels_x3f_4021_, lean_object* v_inst_4022_, lean_object* v_toBind_4023_, lean_object* v_a_4024_, lean_object* v_x_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_4019_, v_toPure_4020_, v_levels_x3f_4021_, v_inst_4022_, v_toBind_4023_, v_a_4024_, v_x_4025_, v___y_4026_);
lean_dec(v_levels_x3f_4021_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_4028_, lean_object* v_levels_x3f_4029_, lean_object* v_inst_4030_, lean_object* v_toBind_4031_, lean_object* v_params_4032_, lean_object* v_inst_4033_, lean_object* v___f_4034_, lean_object* v_val_4035_){
_start:
{
lean_object* v___x_4036_; lean_object* v___f_4037_; lean_object* v___x_4038_; size_t v_sz_4039_; size_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4036_ = lean_box(0);
lean_inc(v_toBind_4031_);
v___f_4037_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_4037_, 0, v___x_4036_);
lean_closure_set(v___f_4037_, 1, v_toPure_4028_);
lean_closure_set(v___f_4037_, 2, v_levels_x3f_4029_);
lean_closure_set(v___f_4037_, 3, v_inst_4030_);
lean_closure_set(v___f_4037_, 4, v_toBind_4031_);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v_val_4035_);
v_sz_4039_ = lean_array_size(v_params_4032_);
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4033_, v_params_4032_, v___f_4037_, v_sz_4039_, v___x_4040_, v___x_4038_);
v___x_4042_ = lean_apply_4(v_toBind_4031_, lean_box(0), lean_box(0), v___x_4041_, v___f_4034_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4043_, lean_object* v_us_4044_, uint8_t v___x_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4043_, v_us_4044_, v___x_4045_, v___y_4048_, v___y_4049_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4052_, lean_object* v_us_4053_, lean_object* v___x_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
uint8_t v___x_677__boxed_4060_; lean_object* v_res_4061_; 
v___x_677__boxed_4060_ = lean_unbox(v___x_4054_);
v_res_4061_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4052_, v_us_4053_, v___x_677__boxed_4060_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v_cinfo_4052_);
return v_res_4061_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4065_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4066_ = lean_unsigned_to_nat(2u);
v___x_4067_ = lean_unsigned_to_nat(202u);
v___x_4068_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4069_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4070_ = l_mkPanicMessageWithDecl(v___x_4069_, v___x_4068_, v___x_4067_, v___x_4066_, v___x_4065_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4071_, lean_object* v___x_4072_, lean_object* v_inst_4073_, lean_object* v_toBind_4074_, lean_object* v___f_4075_, lean_object* v_us_4076_){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v___x_4077_ = l_List_lengthTR___redArg(v_us_4076_);
v___x_4078_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4071_);
v___x_4079_ = l_List_lengthTR___redArg(v___x_4078_);
lean_dec(v___x_4078_);
v___x_4080_ = lean_nat_dec_eq(v___x_4077_, v___x_4079_);
lean_dec(v___x_4079_);
lean_dec(v___x_4077_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec(v_us_4076_);
lean_dec(v___f_4075_);
lean_dec(v_toBind_4074_);
lean_dec(v_inst_4073_);
lean_dec_ref(v_cinfo_4071_);
v___x_4081_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4082_ = l_panic___redArg(v___x_4072_, v___x_4081_);
return v___x_4082_;
}
else
{
uint8_t v___x_4083_; lean_object* v___x_4084_; lean_object* v___f_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4083_ = 0;
v___x_4084_ = lean_box(v___x_4083_);
v___f_4085_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4085_, 0, v_cinfo_4071_);
lean_closure_set(v___f_4085_, 1, v_us_4076_);
lean_closure_set(v___f_4085_, 2, v___x_4084_);
v___x_4086_ = lean_apply_2(v_inst_4073_, lean_box(0), v___f_4085_);
v___x_4087_ = lean_apply_4(v_toBind_4074_, lean_box(0), lean_box(0), v___x_4086_, v___f_4075_);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4088_, lean_object* v___x_4089_, lean_object* v_inst_4090_, lean_object* v_toBind_4091_, lean_object* v___f_4092_, lean_object* v_us_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4088_, v___x_4089_, v_inst_4090_, v_toBind_4091_, v___f_4092_, v_us_4093_);
lean_dec(v___x_4089_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4095_, lean_object* v_inst_4096_, lean_object* v_toBind_4097_, lean_object* v___f_4098_, lean_object* v_levels_x3f_4099_, lean_object* v_toPure_4100_, lean_object* v_cinfo_4101_){
_start:
{
lean_object* v___f_4102_; 
lean_inc(v_toBind_4097_);
lean_inc(v_inst_4096_);
lean_inc_ref(v_cinfo_4101_);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4102_, 0, v_cinfo_4101_);
lean_closure_set(v___f_4102_, 1, v___x_4095_);
lean_closure_set(v___f_4102_, 2, v_inst_4096_);
lean_closure_set(v___f_4102_, 3, v_toBind_4097_);
lean_closure_set(v___f_4102_, 4, v___f_4098_);
if (lean_obj_tag(v_levels_x3f_4099_) == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
lean_dec(v_toPure_4100_);
v___x_4103_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4103_, 0, v_cinfo_4101_);
v___x_4104_ = lean_apply_2(v_inst_4096_, lean_box(0), v___x_4103_);
v___x_4105_ = lean_apply_4(v_toBind_4097_, lean_box(0), lean_box(0), v___x_4104_, v___f_4102_);
return v___x_4105_;
}
else
{
lean_object* v_val_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref(v_cinfo_4101_);
lean_dec(v_inst_4096_);
v_val_4106_ = lean_ctor_get(v_levels_x3f_4099_, 0);
lean_inc(v_val_4106_);
lean_dec_ref_known(v_levels_x3f_4099_, 1);
v___x_4107_ = lean_apply_2(v_toPure_4100_, lean_box(0), v_val_4106_);
v___x_4108_ = lean_apply_4(v_toBind_4097_, lean_box(0), lean_box(0), v___x_4107_, v___f_4102_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4109_, lean_object* v_inst_4110_, lean_object* v_inst_4111_, lean_object* v_inst_4112_, lean_object* v_defaultFn_4113_, lean_object* v_levels_x3f_4114_, lean_object* v_params_4115_, lean_object* v_fieldVal_x3f_4116_){
_start:
{
lean_object* v_toApplicative_4117_; lean_object* v_toBind_4118_; lean_object* v_toPure_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___f_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; lean_object* v___f_4125_; lean_object* v___x_4126_; 
v_toApplicative_4117_ = lean_ctor_get(v_inst_4109_, 0);
v_toBind_4118_ = lean_ctor_get(v_inst_4109_, 1);
lean_inc_n(v_toBind_4118_, 3);
v_toPure_4119_ = lean_ctor_get(v_toApplicative_4117_, 1);
lean_inc_n(v_toPure_4119_, 3);
v___x_4120_ = lean_box(0);
lean_inc_ref_n(v_inst_4109_, 3);
v___x_4121_ = l_Lean_getConstInfo___redArg(v_inst_4109_, v_inst_4110_, v_inst_4111_, v_defaultFn_4113_);
lean_inc_n(v_inst_4112_, 2);
v___f_4122_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4122_, 0, v_inst_4109_);
lean_closure_set(v___f_4122_, 1, v_inst_4112_);
lean_closure_set(v___f_4122_, 2, v_fieldVal_x3f_4116_);
lean_closure_set(v___f_4122_, 3, v_toPure_4119_);
lean_inc(v_levels_x3f_4114_);
v___f_4123_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4123_, 0, v_toPure_4119_);
lean_closure_set(v___f_4123_, 1, v_levels_x3f_4114_);
lean_closure_set(v___f_4123_, 2, v_inst_4112_);
lean_closure_set(v___f_4123_, 3, v_toBind_4118_);
lean_closure_set(v___f_4123_, 4, v_params_4115_);
lean_closure_set(v___f_4123_, 5, v_inst_4109_);
lean_closure_set(v___f_4123_, 6, v___f_4122_);
v___x_4124_ = l_instInhabitedOfMonad___redArg(v_inst_4109_, v___x_4120_);
v___f_4125_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4125_, 0, v___x_4124_);
lean_closure_set(v___f_4125_, 1, v_inst_4112_);
lean_closure_set(v___f_4125_, 2, v_toBind_4118_);
lean_closure_set(v___f_4125_, 3, v___f_4123_);
lean_closure_set(v___f_4125_, 4, v_levels_x3f_4114_);
lean_closure_set(v___f_4125_, 5, v_toPure_4119_);
v___x_4126_ = lean_apply_4(v_toBind_4118_, lean_box(0), lean_box(0), v___x_4121_, v___f_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4127_, lean_object* v_inst_4128_, lean_object* v_inst_4129_, lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_inst_4132_, lean_object* v_defaultFn_4133_, lean_object* v_levels_x3f_4134_, lean_object* v_params_4135_, lean_object* v_fieldVal_x3f_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4128_, v_inst_4129_, v_inst_4130_, v_inst_4131_, v_defaultFn_4133_, v_levels_x3f_4134_, v_params_4135_, v_fieldVal_x3f_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4138_, lean_object* v_inst_4139_, lean_object* v_inst_4140_, lean_object* v_inst_4141_, lean_object* v_inst_4142_, lean_object* v_inst_4143_, lean_object* v_defaultFn_4144_, lean_object* v_levels_x3f_4145_, lean_object* v_params_4146_, lean_object* v_fieldVal_x3f_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4138_, v_inst_4139_, v_inst_4140_, v_inst_4141_, v_inst_4142_, v_inst_4143_, v_defaultFn_4144_, v_levels_x3f_4145_, v_params_4146_, v_fieldVal_x3f_4147_);
lean_dec_ref(v_inst_4143_);
return v_res_4148_;
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
