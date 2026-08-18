// Lean compiler output
// Module: Lean.Meta.HaveTelescope
// Imports: public import Lean.Meta.Basic public import Lean.Meta.MonadSimp import Lean.Util.CollectFVars import Lean.Util.CollectLooseBVars import Lean.Meta.AppBuilder import Init.While
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_collectLooseBVars(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveInfo;
static const lean_array_object l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0_value;
static const lean_string_object l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "_have_telescope_info_dummy_"};
static const lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 236, 171, 204, 19, 216, 21, 195)}};
static const lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2 = (const lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1;
static const lean_array_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0 = (const lean_object*)&l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpHaveResult_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "have_unused_dep'"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "have_unused'"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "have_body_congr_dep'"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "have_val_congr'"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "have_body_congr'"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "have_congr'"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "have telescope; simplifying body "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(224, 171, 76, 175, 220, 234, 86, 123)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(203, 102, 186, 241, 230, 68, 112, 189)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(231, 39, 204, 185, 148, 242, 27, 8)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "have telescope; unused "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "have telescope; fixed "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "have telescope; non-fixed "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__5_value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__7_value),LEAN_SCALAR_PTR_LITERAL(66, 96, 215, 110, 82, 218, 253, 207)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(255, 213, 12, 50, 85, 170, 122, 222)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(238, 251, 30, 34, 208, 131, 54, 223)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(33, 35, 129, 148, 230, 9, 239, 46)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.HaveTelescope"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Meta.HaveTelescope.0.Lean.Meta.simpHaveTelescopeAux"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "assertion violation: !rb.exprType.hasLooseBVar 0\n        "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "_simp_let_unused_dummy"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 140, 102, 13, 80, 16, 156, 102)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.simpHaveTelescope"};
static const lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "assertion violation: !info.haveInfo.isEmpty\n  "};
static const lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__0(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__0, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__0_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = lean_box(0);
v___x_10_ = l_Lean_instInhabitedLocalDecl_default;
v___x_11_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__2, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__3, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__3_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__3);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_instInhabitedHaveInfo_default;
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_box(0);
v___x_21_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2));
v___x_22_ = l_Lean_Expr_const___override(v___x_21_, v___x_20_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2));
v___x_24_ = l_Lean_Level_param___override(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4);
v___x_26_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3);
v___x_27_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__2, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2);
v___x_28_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_29_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_27_);
lean_ctor_set(v___x_29_, 3, v___x_26_);
lean_ctor_set(v___x_29_, 4, v___x_26_);
lean_ctor_set(v___x_29_, 5, v___x_25_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default;
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(lean_object* v_lctx_32_, lean_object* v_x_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_keyedConfig_39_; uint8_t v_trackZetaDelta_40_; lean_object* v_zetaDeltaSet_41_; lean_object* v_localInstances_42_; lean_object* v_defEqCtx_x3f_43_; lean_object* v_synthPendingDepth_44_; lean_object* v_customCanUnfoldPredicate_x3f_45_; uint8_t v_univApprox_46_; uint8_t v_inTypeClassResolution_47_; uint8_t v_cacheInferType_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_keyedConfig_39_ = lean_ctor_get(v___y_34_, 0);
v_trackZetaDelta_40_ = lean_ctor_get_uint8(v___y_34_, sizeof(void*)*7);
v_zetaDeltaSet_41_ = lean_ctor_get(v___y_34_, 1);
v_localInstances_42_ = lean_ctor_get(v___y_34_, 3);
v_defEqCtx_x3f_43_ = lean_ctor_get(v___y_34_, 4);
v_synthPendingDepth_44_ = lean_ctor_get(v___y_34_, 5);
v_customCanUnfoldPredicate_x3f_45_ = lean_ctor_get(v___y_34_, 6);
v_univApprox_46_ = lean_ctor_get_uint8(v___y_34_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_47_ = lean_ctor_get_uint8(v___y_34_, sizeof(void*)*7 + 2);
v_cacheInferType_48_ = lean_ctor_get_uint8(v___y_34_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_45_);
lean_inc(v_synthPendingDepth_44_);
lean_inc(v_defEqCtx_x3f_43_);
lean_inc_ref(v_localInstances_42_);
lean_inc(v_zetaDeltaSet_41_);
lean_inc_ref(v_keyedConfig_39_);
v___x_49_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_49_, 0, v_keyedConfig_39_);
lean_ctor_set(v___x_49_, 1, v_zetaDeltaSet_41_);
lean_ctor_set(v___x_49_, 2, v_lctx_32_);
lean_ctor_set(v___x_49_, 3, v_localInstances_42_);
lean_ctor_set(v___x_49_, 4, v_defEqCtx_x3f_43_);
lean_ctor_set(v___x_49_, 5, v_synthPendingDepth_44_);
lean_ctor_set(v___x_49_, 6, v_customCanUnfoldPredicate_x3f_45_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*7, v_trackZetaDelta_40_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*7 + 1, v_univApprox_46_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*7 + 2, v_inTypeClassResolution_47_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*7 + 3, v_cacheInferType_48_);
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
v___x_50_ = lean_apply_5(v_x_33_, v___x_49_, v___y_35_, v___y_36_, v___y_37_, lean_box(0));
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object* v_lctx_51_, lean_object* v_x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_51_, v_x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object* v_00_u03b1_59_, lean_object* v_lctx_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(lean_object* v_00_u03b1_68_, lean_object* v_lctx_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(v_00_u03b1_68_, v_lctx_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object* v_m_77_, lean_object* v_query_78_, lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_zero_82_; uint8_t v_isZero_83_; 
v_zero_82_ = lean_unsigned_to_nat(0u);
v_isZero_83_ = lean_nat_dec_eq(v_x_80_, v_zero_82_);
if (v_isZero_83_ == 1)
{
lean_dec(v_x_81_);
lean_dec(v_x_80_);
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(2);
return v___x_84_;
}
else
{
lean_object* v_val_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_val_85_ = lean_ctor_get(v_x_79_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v_x_79_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_val_85_);
lean_dec(v_x_79_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_val_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v_keyArray_93_; lean_object* v_valueArray_94_; lean_object* v___x_95_; uint8_t v_isSome_96_; 
v_keyArray_93_ = lean_ctor_get(v_m_77_, 1);
v_valueArray_94_ = lean_ctor_get(v_m_77_, 2);
v___x_95_ = lean_array_fget_borrowed(v_keyArray_93_, v_x_81_);
v_isSome_96_ = lean_noption_is_some(v___x_95_);
if (v_isSome_96_ == 0)
{
lean_dec(v_x_80_);
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_x_81_);
return v___x_97_;
}
else
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_x_81_);
v_val_98_ = lean_ctor_get(v_x_79_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v_x_79_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_x_79_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_val_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
else
{
lean_object* v_one_106_; lean_object* v_n_107_; lean_object* v___y_109_; 
v_one_106_ = lean_unsigned_to_nat(1u);
v_n_107_ = lean_nat_sub(v_x_80_, v_one_106_);
lean_dec(v_x_80_);
if (v_isSome_96_ == 0)
{
goto v___jp_115_;
}
else
{
lean_object* v___x_117_; uint8_t v_isSome_118_; 
v___x_117_ = lean_array_fget_borrowed(v_valueArray_94_, v_x_81_);
v_isSome_118_ = lean_noption_is_some(v___x_117_);
if (v_isSome_118_ == 0)
{
goto v___jp_115_;
}
else
{
lean_object* v_val_119_; uint8_t v___x_120_; 
lean_inc(v___x_95_);
v_val_119_ = lean_noption_get(v___x_95_);
v___x_120_ = lean_nat_dec_eq(v_val_119_, v_query_78_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
lean_dec(v_val_119_);
v___x_121_ = lean_array_get_size(v_keyArray_93_);
v___x_122_ = lean_nat_add(v_x_81_, v_one_106_);
lean_dec(v_x_81_);
v___x_123_ = lean_nat_dec_lt(v___x_122_, v___x_121_);
if (v___x_123_ == 0)
{
lean_dec(v___x_122_);
v_x_80_ = v_n_107_;
v_x_81_ = v_zero_82_;
goto _start;
}
else
{
v_x_80_ = v_n_107_;
v_x_81_ = v___x_122_;
goto _start;
}
}
else
{
lean_object* v_val_126_; lean_object* v___x_127_; 
lean_dec(v_n_107_);
lean_dec(v_x_79_);
lean_inc(v___x_117_);
v_val_126_ = lean_noption_get(v___x_117_);
v___x_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_127_, 0, v_x_81_);
lean_ctor_set(v___x_127_, 1, v_val_119_);
lean_ctor_set(v___x_127_, 2, v_val_126_);
return v___x_127_;
}
}
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = lean_array_get_size(v_keyArray_93_);
v___x_111_ = lean_nat_add(v_x_81_, v_one_106_);
lean_dec(v_x_81_);
v___x_112_ = lean_nat_dec_lt(v___x_111_, v___x_110_);
if (v___x_112_ == 0)
{
lean_dec(v___x_111_);
v_x_79_ = v___y_109_;
v_x_80_ = v_n_107_;
v_x_81_ = v_zero_82_;
goto _start;
}
else
{
v_x_79_ = v___y_109_;
v_x_80_ = v_n_107_;
v_x_81_ = v___x_111_;
goto _start;
}
}
v___jp_115_:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_116_; 
lean_inc(v_x_81_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_x_81_);
v___y_109_ = v___x_116_;
goto v___jp_108_;
}
else
{
v___y_109_ = v_x_79_;
goto v___jp_108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object* v_m_128_, lean_object* v_query_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_m_128_, v_query_129_, v_x_130_, v_x_131_, v_x_132_);
lean_dec(v_query_129_);
lean_dec_ref(v_m_128_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object* v_m_134_, lean_object* v_query_135_){
_start:
{
lean_object* v_keyArray_136_; lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_keyArray_136_ = lean_ctor_get(v_m_134_, 1);
v___x_137_ = lean_array_get_size(v_keyArray_136_);
v___x_138_ = lean_uint64_of_nat(v_query_135_);
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___x_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___x_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_137_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v___x_150_ = lean_usize_to_nat(v___x_149_);
v___x_151_ = lean_box(0);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_m_134_, v_query_135_, v___x_151_, v___x_137_, v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg___boxed(lean_object* v_m_153_, lean_object* v_query_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_153_, v_query_154_);
lean_dec(v_query_154_);
lean_dec_ref(v_m_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg(lean_object* v_b_156_, lean_object* v_acc_157_, lean_object* v_i_158_){
_start:
{
lean_object* v___y_160_; lean_object* v_keyArray_168_; lean_object* v_valueArray_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_keyArray_168_ = lean_ctor_get(v_b_156_, 1);
v_valueArray_169_ = lean_ctor_get(v_b_156_, 2);
v___x_170_ = lean_array_get_size(v_keyArray_168_);
v___x_171_ = lean_nat_dec_lt(v_i_158_, v___x_170_);
if (v___x_171_ == 0)
{
lean_dec(v_i_158_);
return v_acc_157_;
}
else
{
lean_object* v___x_172_; uint8_t v_isSome_173_; 
v___x_172_ = lean_array_fget_borrowed(v_keyArray_168_, v_i_158_);
v_isSome_173_ = lean_noption_is_some(v___x_172_);
if (v_isSome_173_ == 0)
{
goto v___jp_164_;
}
else
{
lean_object* v___x_174_; uint8_t v_isSome_175_; 
v___x_174_ = lean_array_fget_borrowed(v_valueArray_169_, v_i_158_);
v_isSome_175_ = lean_noption_is_some(v___x_174_);
if (v_isSome_175_ == 0)
{
goto v___jp_164_;
}
else
{
lean_object* v_val_176_; lean_object* v_val_177_; lean_object* v_i_179_; lean_object* v___x_184_; 
lean_inc(v___x_172_);
v_val_176_ = lean_noption_get(v___x_172_);
lean_inc(v___x_174_);
v_val_177_ = lean_noption_get(v___x_174_);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_acc_157_, v_val_176_);
switch(lean_obj_tag(v___x_184_))
{
case 0:
{
lean_object* v_index_185_; lean_object* v_size_186_; lean_object* v___x_187_; 
v_index_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_185_);
lean_dec_ref_known(v___x_184_, 3);
v_size_186_ = lean_ctor_get(v_acc_157_, 0);
lean_inc(v_size_186_);
v___x_187_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_157_, v_size_186_, v_index_185_, v_val_176_, v_val_177_);
lean_dec(v_index_185_);
v___y_160_ = v___x_187_;
goto v___jp_159_;
}
case 1:
{
lean_object* v_index_188_; 
v_index_188_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_188_);
lean_dec_ref_known(v___x_184_, 1);
v_i_179_ = v_index_188_;
goto v___jp_178_;
}
default: 
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_157_, v___x_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_index_191_; 
v_index_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_index_191_);
lean_dec_ref_known(v___x_190_, 1);
v_i_179_ = v_index_191_;
goto v___jp_178_;
}
else
{
lean_dec(v_val_177_);
lean_dec(v_val_176_);
v___y_160_ = v_acc_157_;
goto v___jp_159_;
}
}
}
v___jp_178_:
{
lean_object* v_size_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_size_180_ = lean_ctor_get(v_acc_157_, 0);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_size_180_, v___x_181_);
v___x_183_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_157_, v___x_182_, v_i_179_, v_val_176_, v_val_177_);
lean_dec(v_i_179_);
v___y_160_ = v___x_183_;
goto v___jp_159_;
}
}
}
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_i_158_, v___x_161_);
lean_dec(v_i_158_);
v_acc_157_ = v___y_160_;
v_i_158_ = v___x_162_;
goto _start;
}
v___jp_164_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_158_, v___x_165_);
lean_dec(v_i_158_);
v_i_158_ = v___x_166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_b_192_, lean_object* v_acc_193_, lean_object* v_i_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg(v_b_192_, v_acc_193_, v_i_194_);
lean_dec_ref(v_b_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg(lean_object* v_init_196_, lean_object* v_b_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg(v_b_197_, v_init_196_, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg___boxed(lean_object* v_init_200_, lean_object* v_b_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg(v_init_200_, v_b_201_);
lean_dec_ref(v_b_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(lean_object* v_m_203_){
_start:
{
lean_object* v_keyArray_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_cellCount_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_target_211_; lean_object* v___x_212_; 
v_keyArray_204_ = lean_ctor_get(v_m_203_, 1);
v___x_205_ = lean_array_get_size(v_keyArray_204_);
v___x_206_ = lean_unsigned_to_nat(2u);
v_cellCount_207_ = lean_nat_mul(v___x_205_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_207_);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_207_);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_207_);
v_target_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_211_, 0, v___x_208_);
lean_ctor_set(v_target_211_, 1, v___x_209_);
lean_ctor_set(v_target_211_, 2, v___x_210_);
v___x_212_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg(v_target_211_, v_m_203_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg___boxed(lean_object* v_m_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_m_213_);
lean_dec_ref(v_m_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_spec__4(lean_object* v_numHaves_215_, lean_object* v_b_216_, lean_object* v_acc_217_, lean_object* v_i_218_){
_start:
{
lean_object* v___y_220_; lean_object* v_keyArray_228_; lean_object* v_valueArray_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_keyArray_228_ = lean_ctor_get(v_b_216_, 1);
v_valueArray_229_ = lean_ctor_get(v_b_216_, 2);
v___x_230_ = lean_array_get_size(v_keyArray_228_);
v___x_231_ = lean_nat_dec_lt(v_i_218_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec(v_i_218_);
return v_acc_217_;
}
else
{
lean_object* v___x_232_; uint8_t v_isSome_233_; 
v___x_232_ = lean_array_fget_borrowed(v_keyArray_228_, v_i_218_);
v_isSome_233_ = lean_noption_is_some(v___x_232_);
if (v_isSome_233_ == 0)
{
goto v___jp_224_;
}
else
{
lean_object* v___x_234_; uint8_t v_isSome_235_; 
v___x_234_ = lean_array_fget_borrowed(v_valueArray_229_, v_i_218_);
v_isSome_235_ = lean_noption_is_some(v___x_234_);
if (v_isSome_235_ == 0)
{
goto v___jp_224_;
}
else
{
lean_object* v_val_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___y_242_; lean_object* v_i_243_; lean_object* v___y_248_; lean_object* v___y_258_; lean_object* v_i_259_; lean_object* v___x_273_; 
lean_inc(v___x_232_);
v_val_236_ = lean_noption_get(v___x_232_);
v___x_237_ = lean_nat_sub(v_numHaves_215_, v_val_236_);
lean_dec(v_val_236_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_sub(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_acc_217_, v___x_239_);
switch(lean_obj_tag(v___x_273_))
{
case 0:
{
lean_dec_ref_known(v___x_273_, 3);
lean_dec(v___x_239_);
v___y_220_ = v_acc_217_;
goto v___jp_219_;
}
case 1:
{
lean_object* v_index_274_; lean_object* v_size_275_; lean_object* v_keyArray_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_index_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_index_274_);
lean_dec_ref_known(v___x_273_, 1);
v_size_275_ = lean_ctor_get(v_acc_217_, 0);
v_keyArray_276_ = lean_ctor_get(v_acc_217_, 1);
v___x_277_ = lean_nat_add(v_size_275_, v___x_238_);
v___x_278_ = lean_array_get_size(v_keyArray_276_);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec(v___x_277_);
lean_dec(v_index_274_);
goto v___jp_263_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_280_ = lean_unsigned_to_nat(4u);
v___x_281_ = lean_nat_mul(v___x_277_, v___x_280_);
v___x_282_ = lean_unsigned_to_nat(3u);
v___x_283_ = lean_nat_mul(v___x_278_, v___x_282_);
v___x_284_ = lean_nat_dec_le(v___x_281_, v___x_283_);
lean_dec(v___x_283_);
lean_dec(v___x_281_);
if (v___x_284_ == 0)
{
lean_dec(v___x_277_);
lean_dec(v_index_274_);
goto v___jp_263_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_217_, v___x_277_, v_index_274_, v___x_239_, v___x_240_);
lean_dec(v_index_274_);
v___y_220_ = v___x_285_;
goto v___jp_219_;
}
}
}
default: 
{
lean_object* v_size_286_; lean_object* v_keyArray_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_size_286_ = lean_ctor_get(v_acc_217_, 0);
v_keyArray_287_ = lean_ctor_get(v_acc_217_, 1);
v___x_288_ = lean_nat_add(v_size_286_, v___x_238_);
v___x_289_ = lean_array_get_size(v_keyArray_287_);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_dec(v___x_288_);
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_acc_217_);
lean_dec_ref(v_acc_217_);
v___y_248_ = v___x_291_;
goto v___jp_247_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_292_ = lean_unsigned_to_nat(4u);
v___x_293_ = lean_nat_mul(v___x_288_, v___x_292_);
lean_dec(v___x_288_);
v___x_294_ = lean_unsigned_to_nat(3u);
v___x_295_ = lean_nat_mul(v___x_289_, v___x_294_);
v___x_296_ = lean_nat_dec_le(v___x_293_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___x_293_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_acc_217_);
lean_dec_ref(v_acc_217_);
v___y_248_ = v___x_297_;
goto v___jp_247_;
}
else
{
v___y_248_ = v_acc_217_;
goto v___jp_247_;
}
}
}
}
v___jp_241_:
{
lean_object* v_size_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_size_244_ = lean_ctor_get(v___y_242_, 0);
v___x_245_ = lean_nat_add(v_size_244_, v___x_238_);
v___x_246_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_242_, v___x_245_, v_i_243_, v___x_239_, v___x_240_);
lean_dec(v_i_243_);
v___y_220_ = v___x_246_;
goto v___jp_219_;
}
v___jp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v___y_248_, v___x_239_);
switch(lean_obj_tag(v___x_249_))
{
case 0:
{
lean_object* v_index_250_; lean_object* v_size_251_; lean_object* v___x_252_; 
v_index_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_index_250_);
lean_dec_ref_known(v___x_249_, 3);
v_size_251_ = lean_ctor_get(v___y_248_, 0);
lean_inc(v_size_251_);
v___x_252_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_248_, v_size_251_, v_index_250_, v___x_239_, v___x_240_);
lean_dec(v_index_250_);
v___y_220_ = v___x_252_;
goto v___jp_219_;
}
case 1:
{
lean_object* v_index_253_; 
v_index_253_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_index_253_);
lean_dec_ref_known(v___x_249_, 1);
v___y_242_ = v___y_248_;
v_i_243_ = v_index_253_;
goto v___jp_241_;
}
default: 
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_248_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_index_256_; 
v_index_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_256_);
lean_dec_ref_known(v___x_255_, 1);
v___y_242_ = v___y_248_;
v_i_243_ = v_index_256_;
goto v___jp_241_;
}
else
{
lean_dec(v___x_239_);
v___y_220_ = v___y_248_;
goto v___jp_219_;
}
}
}
}
v___jp_257_:
{
lean_object* v_size_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_size_260_ = lean_ctor_get(v___y_258_, 0);
v___x_261_ = lean_nat_add(v_size_260_, v___x_238_);
v___x_262_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_258_, v___x_261_, v_i_259_, v___x_239_, v___x_240_);
lean_dec(v_i_259_);
v___y_220_ = v___x_262_;
goto v___jp_219_;
}
v___jp_263_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_acc_217_);
lean_dec_ref(v_acc_217_);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v___x_264_, v___x_239_);
switch(lean_obj_tag(v___x_265_))
{
case 0:
{
lean_object* v_index_266_; lean_object* v_size_267_; lean_object* v___x_268_; 
v_index_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_index_266_);
lean_dec_ref_known(v___x_265_, 3);
v_size_267_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_size_267_);
v___x_268_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_264_, v_size_267_, v_index_266_, v___x_239_, v___x_240_);
lean_dec(v_index_266_);
v___y_220_ = v___x_268_;
goto v___jp_219_;
}
case 1:
{
lean_object* v_index_269_; 
v_index_269_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_index_269_);
lean_dec_ref_known(v___x_265_, 1);
v___y_258_ = v___x_264_;
v_i_259_ = v_index_269_;
goto v___jp_257_;
}
default: 
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_264_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_index_272_; 
v_index_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_index_272_);
lean_dec_ref_known(v___x_271_, 1);
v___y_258_ = v___x_264_;
v_i_259_ = v_index_272_;
goto v___jp_257_;
}
else
{
lean_dec(v___x_239_);
v___y_220_ = v___x_264_;
goto v___jp_219_;
}
}
}
}
}
}
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_i_218_, v___x_221_);
lean_dec(v_i_218_);
v_acc_217_ = v___y_220_;
v_i_218_ = v___x_222_;
goto _start;
}
v___jp_224_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_i_218_, v___x_225_);
lean_dec(v_i_218_);
v_i_218_ = v___x_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_spec__4___boxed(lean_object* v_numHaves_298_, lean_object* v_b_299_, lean_object* v_acc_300_, lean_object* v_i_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_spec__4(v_numHaves_298_, v_b_299_, v_acc_300_, v_i_301_);
lean_dec_ref(v_b_299_);
lean_dec(v_numHaves_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object* v_numHaves_303_, lean_object* v_init_304_, lean_object* v_b_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_spec__4(v_numHaves_303_, v_b_305_, v_init_304_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object* v_numHaves_308_, lean_object* v_init_309_, lean_object* v_b_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_308_, v_init_309_, v_b_310_);
lean_dec_ref(v_b_310_);
lean_dec(v_numHaves_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(lean_object* v_numHaves_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__2, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2);
v___x_316_ = l_Lean_Expr_collectLooseBVars(v_a_313_, v___x_314_);
v___x_317_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_312_, v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_318_, v_a_319_);
lean_dec(v_numHaves_318_);
return v_res_320_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_321_, lean_object* v_t_322_){
_start:
{
if (lean_obj_tag(v_t_322_) == 0)
{
lean_object* v_k_323_; lean_object* v_l_324_; lean_object* v_r_325_; uint8_t v___x_326_; 
v_k_323_ = lean_ctor_get(v_t_322_, 1);
v_l_324_ = lean_ctor_get(v_t_322_, 3);
v_r_325_ = lean_ctor_get(v_t_322_, 4);
v___x_326_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_321_, v_k_323_);
switch(v___x_326_)
{
case 0:
{
v_t_322_ = v_l_324_;
goto _start;
}
case 1:
{
uint8_t v___x_328_; 
v___x_328_ = 1;
return v___x_328_;
}
default: 
{
v_t_322_ = v_r_325_;
goto _start;
}
}
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_331_, lean_object* v_t_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_331_, v_t_332_);
lean_dec(v_t_332_);
lean_dec(v_k_331_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_335_, lean_object* v___x_336_, lean_object* v_n_337_, lean_object* v_j_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_zero_340_; uint8_t v_isZero_341_; 
v_zero_340_ = lean_unsigned_to_nat(0u);
v_isZero_341_ = lean_nat_dec_eq(v_j_338_, v_zero_340_);
if (v_isZero_341_ == 1)
{
lean_dec(v_j_338_);
return v_a_339_;
}
else
{
lean_object* v_one_342_; lean_object* v_n_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_one_342_ = lean_unsigned_to_nat(1u);
v_n_343_ = lean_nat_sub(v_j_338_, v_one_342_);
v___x_344_ = lean_nat_sub(v_n_337_, v_j_338_);
lean_dec(v_j_338_);
v___x_345_ = lean_array_fget_borrowed(v_fvars_335_, v___x_344_);
v___x_346_ = l_Lean_Expr_fvarId_x21(v___x_345_);
v___x_347_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_346_, v___x_336_);
lean_dec(v___x_346_);
if (v___x_347_ == 0)
{
lean_dec(v___x_344_);
v_j_338_ = v_n_343_;
goto _start;
}
else
{
lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v_i_352_; lean_object* v___y_358_; lean_object* v___y_369_; lean_object* v_i_370_; lean_object* v___x_386_; 
v___x_349_ = lean_box(0);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_339_, v___x_344_);
switch(lean_obj_tag(v___x_386_))
{
case 0:
{
lean_dec_ref_known(v___x_386_, 3);
lean_dec(v___x_344_);
v_j_338_ = v_n_343_;
goto _start;
}
case 1:
{
lean_object* v_index_388_; lean_object* v_size_389_; lean_object* v_keyArray_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_index_388_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_index_388_);
lean_dec_ref_known(v___x_386_, 1);
v_size_389_ = lean_ctor_get(v_a_339_, 0);
v_keyArray_390_ = lean_ctor_get(v_a_339_, 1);
v___x_391_ = lean_nat_add(v_size_389_, v_one_342_);
v___x_392_ = lean_array_get_size(v_keyArray_390_);
v___x_393_ = lean_nat_dec_lt(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v___x_391_);
lean_dec(v_index_388_);
goto v___jp_375_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_394_ = lean_unsigned_to_nat(4u);
v___x_395_ = lean_nat_mul(v___x_391_, v___x_394_);
v___x_396_ = lean_unsigned_to_nat(3u);
v___x_397_ = lean_nat_mul(v___x_392_, v___x_396_);
v___x_398_ = lean_nat_dec_le(v___x_395_, v___x_397_);
lean_dec(v___x_397_);
lean_dec(v___x_395_);
if (v___x_398_ == 0)
{
lean_dec(v___x_391_);
lean_dec(v_index_388_);
goto v___jp_375_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_339_, v___x_391_, v_index_388_, v___x_344_, v___x_349_);
lean_dec(v_index_388_);
v_j_338_ = v_n_343_;
v_a_339_ = v___x_399_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_401_; lean_object* v_keyArray_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_size_401_ = lean_ctor_get(v_a_339_, 0);
v_keyArray_402_ = lean_ctor_get(v_a_339_, 1);
v___x_403_ = lean_nat_add(v_size_401_, v_one_342_);
v___x_404_ = lean_array_get_size(v_keyArray_402_);
v___x_405_ = lean_nat_dec_lt(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v___x_403_);
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_a_339_);
lean_dec_ref(v_a_339_);
v___y_358_ = v___x_406_;
goto v___jp_357_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_407_ = lean_unsigned_to_nat(4u);
v___x_408_ = lean_nat_mul(v___x_403_, v___x_407_);
lean_dec(v___x_403_);
v___x_409_ = lean_unsigned_to_nat(3u);
v___x_410_ = lean_nat_mul(v___x_404_, v___x_409_);
v___x_411_ = lean_nat_dec_le(v___x_408_, v___x_410_);
lean_dec(v___x_410_);
lean_dec(v___x_408_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_a_339_);
lean_dec_ref(v_a_339_);
v___y_358_ = v___x_412_;
goto v___jp_357_;
}
else
{
v___y_358_ = v_a_339_;
goto v___jp_357_;
}
}
}
}
v___jp_350_:
{
lean_object* v_size_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_size_353_ = lean_ctor_get(v___y_351_, 0);
v___x_354_ = lean_nat_add(v_size_353_, v_one_342_);
v___x_355_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_351_, v___x_354_, v_i_352_, v___x_344_, v___x_349_);
lean_dec(v_i_352_);
v_j_338_ = v_n_343_;
v_a_339_ = v___x_355_;
goto _start;
}
v___jp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v___y_358_, v___x_344_);
switch(lean_obj_tag(v___x_359_))
{
case 0:
{
lean_object* v_index_360_; lean_object* v_size_361_; lean_object* v___x_362_; 
v_index_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_index_360_);
lean_dec_ref_known(v___x_359_, 3);
v_size_361_ = lean_ctor_get(v___y_358_, 0);
lean_inc(v_size_361_);
v___x_362_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_358_, v_size_361_, v_index_360_, v___x_344_, v___x_349_);
lean_dec(v_index_360_);
v_j_338_ = v_n_343_;
v_a_339_ = v___x_362_;
goto _start;
}
case 1:
{
lean_object* v_index_364_; 
v_index_364_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_index_364_);
lean_dec_ref_known(v___x_359_, 1);
v___y_351_ = v___y_358_;
v_i_352_ = v_index_364_;
goto v___jp_350_;
}
default: 
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_358_, v_zero_340_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_index_366_; 
v_index_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_index_366_);
lean_dec_ref_known(v___x_365_, 1);
v___y_351_ = v___y_358_;
v_i_352_ = v_index_366_;
goto v___jp_350_;
}
else
{
lean_dec(v___x_344_);
v_j_338_ = v_n_343_;
v_a_339_ = v___y_358_;
goto _start;
}
}
}
}
v___jp_368_:
{
lean_object* v_size_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_size_371_ = lean_ctor_get(v___y_369_, 0);
v___x_372_ = lean_nat_add(v_size_371_, v_one_342_);
v___x_373_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_369_, v___x_372_, v_i_370_, v___x_344_, v___x_349_);
lean_dec(v_i_370_);
v_j_338_ = v_n_343_;
v_a_339_ = v___x_373_;
goto _start;
}
v___jp_375_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_a_339_);
lean_dec_ref(v_a_339_);
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v___x_376_, v___x_344_);
switch(lean_obj_tag(v___x_377_))
{
case 0:
{
lean_object* v_index_378_; lean_object* v_size_379_; lean_object* v___x_380_; 
v_index_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_index_378_);
lean_dec_ref_known(v___x_377_, 3);
v_size_379_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_size_379_);
v___x_380_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_376_, v_size_379_, v_index_378_, v___x_344_, v___x_349_);
lean_dec(v_index_378_);
v_j_338_ = v_n_343_;
v_a_339_ = v___x_380_;
goto _start;
}
case 1:
{
lean_object* v_index_382_; 
v_index_382_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_index_382_);
lean_dec_ref_known(v___x_377_, 1);
v___y_369_ = v___x_376_;
v_i_370_ = v_index_382_;
goto v___jp_368_;
}
default: 
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_376_, v_zero_340_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_index_384_; 
v_index_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_index_384_);
lean_dec_ref_known(v___x_383_, 1);
v___y_369_ = v___x_376_;
v_i_370_ = v_index_384_;
goto v___jp_368_;
}
else
{
lean_dec(v___x_344_);
v_j_338_ = v_n_343_;
v_a_339_ = v___x_376_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_413_, lean_object* v___x_414_, lean_object* v_n_415_, lean_object* v_j_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_413_, v___x_414_, v_n_415_, v_j_416_, v_a_417_);
lean_dec(v_n_415_);
lean_dec(v___x_414_);
lean_dec_ref(v_fvars_413_);
return v_res_418_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v_cellCount_419_; lean_object* v___x_420_; 
v_cellCount_419_ = lean_unsigned_to_nat(16u);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_419_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_422_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set(v___x_424_, 2, v___x_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_427_, lean_object* v___x_428_, lean_object* v_fvars_429_, lean_object* v_info_430_, lean_object* v_bodyDeps_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc_ref(v_body_427_);
v___x_437_ = lean_infer_type(v_body_427_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc_n(v_a_438_, 2);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = l_Lean_Meta_getLevel(v_a_438_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_467_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_467_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_467_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_467_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_fvarSet_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_haveInfo_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_461_; 
v___x_444_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_428_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
lean_inc(v_a_438_);
v___x_447_ = l_Lean_collectFVars(v___x_446_, v_a_438_);
v_fvarSet_448_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_fvarSet_448_);
lean_dec_ref(v___x_447_);
v___x_449_ = lean_array_get_size(v_fvars_429_);
v___x_450_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_429_, v_fvarSet_448_, v___x_449_, v___x_449_, v___x_444_);
lean_dec(v_fvarSet_448_);
v_haveInfo_451_ = lean_ctor_get(v_info_430_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_info_430_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_462_ = lean_ctor_get(v_info_430_, 5);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_info_430_, 4);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_info_430_, 3);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_info_430_, 2);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_info_430_, 1);
lean_dec(v_unused_466_);
v___x_453_ = v_info_430_;
v_isShared_454_ = v_isSharedCheck_461_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_haveInfo_451_);
lean_dec(v_info_430_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_461_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 5, v_a_440_);
lean_ctor_set(v___x_453_, 4, v_a_438_);
lean_ctor_set(v___x_453_, 3, v_body_427_);
lean_ctor_set(v___x_453_, 2, v___x_450_);
lean_ctor_set(v___x_453_, 1, v_bodyDeps_431_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_haveInfo_451_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_bodyDeps_431_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_body_427_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v_a_438_);
lean_ctor_set(v_reuseFailAlloc_460_, 5, v_a_440_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_456_);
v___x_458_ = v___x_442_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_a_438_);
lean_dec_ref(v_bodyDeps_431_);
lean_dec_ref(v_info_430_);
lean_dec(v___x_428_);
lean_dec_ref(v_body_427_);
v_a_468_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_439_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_439_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec_ref(v_bodyDeps_431_);
lean_dec_ref(v_info_430_);
lean_dec(v___x_428_);
lean_dec_ref(v_body_427_);
v_a_476_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_437_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_437_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_484_, lean_object* v___x_485_, lean_object* v_fvars_486_, lean_object* v_info_487_, lean_object* v_bodyDeps_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_484_, v___x_485_, v_fvars_486_, v_info_487_, v_bodyDeps_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec_ref(v_fvars_486_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg(lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; lean_object* v_ngen_498_; lean_object* v_namePrefix_499_; lean_object* v_idx_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_529_; 
v___x_497_ = lean_st_ref_get(v___y_495_);
v_ngen_498_ = lean_ctor_get(v___x_497_, 2);
lean_inc_ref(v_ngen_498_);
lean_dec(v___x_497_);
v_namePrefix_499_ = lean_ctor_get(v_ngen_498_, 0);
v_idx_500_ = lean_ctor_get(v_ngen_498_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_ngen_498_);
if (v_isSharedCheck_529_ == 0)
{
v___x_502_ = v_ngen_498_;
v_isShared_503_ = v_isSharedCheck_529_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_idx_500_);
lean_inc(v_namePrefix_499_);
lean_dec(v_ngen_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_529_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v_env_505_; lean_object* v_nextMacroScope_506_; lean_object* v_auxDeclNGen_507_; lean_object* v_traceState_508_; lean_object* v_cache_509_; lean_object* v_messages_510_; lean_object* v_infoState_511_; lean_object* v_snapshotTasks_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_527_; 
v___x_504_ = lean_st_ref_take(v___y_495_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
v_nextMacroScope_506_ = lean_ctor_get(v___x_504_, 1);
v_auxDeclNGen_507_ = lean_ctor_get(v___x_504_, 3);
v_traceState_508_ = lean_ctor_get(v___x_504_, 4);
v_cache_509_ = lean_ctor_get(v___x_504_, 5);
v_messages_510_ = lean_ctor_get(v___x_504_, 6);
v_infoState_511_ = lean_ctor_get(v___x_504_, 7);
v_snapshotTasks_512_ = lean_ctor_get(v___x_504_, 8);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_504_, 2);
lean_dec(v_unused_528_);
v___x_514_ = v___x_504_;
v_isShared_515_ = v_isSharedCheck_527_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snapshotTasks_512_);
lean_inc(v_infoState_511_);
lean_inc(v_messages_510_);
lean_inc(v_cache_509_);
lean_inc(v_traceState_508_);
lean_inc(v_auxDeclNGen_507_);
lean_inc(v_nextMacroScope_506_);
lean_inc(v_env_505_);
lean_dec(v___x_504_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_527_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_r_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_idx_500_);
lean_inc(v_namePrefix_499_);
v_r_516_ = l_Lean_Name_num___override(v_namePrefix_499_, v_idx_500_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_idx_500_, v___x_517_);
lean_dec(v_idx_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_518_);
v___x_520_ = v___x_502_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_namePrefix_499_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_526_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 2, v___x_520_);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_env_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_nextMacroScope_506_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_auxDeclNGen_507_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_traceState_508_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_cache_509_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_messages_510_);
lean_ctor_set(v_reuseFailAlloc_525_, 7, v_infoState_511_);
lean_ctor_set(v_reuseFailAlloc_525_, 8, v_snapshotTasks_512_);
v___x_522_ = v_reuseFailAlloc_525_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_st_ref_put(v___y_495_, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_r_516_);
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg___boxed(lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg(v___y_530_);
lean_dec(v___y_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v___x_538_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg(v___y_536_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_553_, lean_object* v_numHaves_554_, lean_object* v_info_555_, lean_object* v_lctx_556_, lean_object* v_fvars_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_563_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; 
v___x_563_ = lean_box(1);
if (lean_obj_tag(v_e_553_) == 8)
{
uint8_t v_nondep_573_; 
v_nondep_573_ = lean_ctor_get_uint8(v_e_553_, sizeof(void*)*4 + 8);
if (v_nondep_573_ == 1)
{
lean_object* v_declName_574_; lean_object* v_type_575_; lean_object* v_value_576_; lean_object* v_body_577_; lean_object* v_t_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_declName_574_ = lean_ctor_get(v_e_553_, 0);
lean_inc(v_declName_574_);
v_type_575_ = lean_ctor_get(v_e_553_, 1);
lean_inc_ref(v_type_575_);
v_value_576_ = lean_ctor_get(v_e_553_, 2);
lean_inc_ref(v_value_576_);
v_body_577_ = lean_ctor_get(v_e_553_, 3);
lean_inc_ref(v_body_577_);
lean_dec_ref_known(v_e_553_, 4);
v_t_578_ = lean_expr_instantiate_rev(v_type_575_, v_fvars_557_);
lean_inc_ref(v_t_578_);
v___x_579_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_579_, 0, v_t_578_);
lean_inc_ref(v_lctx_556_);
v___x_580_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_556_, v___x_579_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v_haveInfo_584_; lean_object* v_bodyDeps_585_; lean_object* v_bodyTypeDeps_586_; lean_object* v_body_587_; lean_object* v_bodyType_588_; lean_object* v_level_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_610_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v_haveInfo_584_ = lean_ctor_get(v_info_555_, 0);
v_bodyDeps_585_ = lean_ctor_get(v_info_555_, 1);
v_bodyTypeDeps_586_ = lean_ctor_get(v_info_555_, 2);
v_body_587_ = lean_ctor_get(v_info_555_, 3);
v_bodyType_588_ = lean_ctor_get(v_info_555_, 4);
v_level_589_ = lean_ctor_get(v_info_555_, 5);
v_isSharedCheck_610_ = !lean_is_exclusive(v_info_555_);
if (v_isSharedCheck_610_ == 0)
{
v___x_591_ = v_info_555_;
v_isShared_592_ = v_isSharedCheck_610_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_level_589_);
lean_inc(v_bodyType_588_);
lean_inc(v_body_587_);
lean_inc(v_bodyTypeDeps_586_);
lean_inc(v_bodyDeps_585_);
lean_inc(v_haveInfo_584_);
lean_dec(v_info_555_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_610_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_typeBackDeps_593_; lean_object* v_valueBackDeps_594_; lean_object* v_v_595_; lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v_typeBackDeps_593_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_554_, v_type_575_);
lean_inc_ref(v_value_576_);
v_valueBackDeps_594_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_554_, v_value_576_);
v_v_595_ = lean_expr_instantiate_rev(v_value_576_, v_fvars_557_);
lean_dec_ref(v_value_576_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = 0;
lean_inc(v_a_583_);
v___x_598_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v_a_583_);
lean_ctor_set(v___x_598_, 2, v_declName_574_);
lean_ctor_set(v___x_598_, 3, v_t_578_);
lean_ctor_set(v___x_598_, 4, v_v_595_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*5, v_nondep_573_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*5 + 1, v___x_597_);
lean_inc_ref(v___x_598_);
v___x_599_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_599_, 0, v_typeBackDeps_593_);
lean_ctor_set(v___x_599_, 1, v_valueBackDeps_594_);
lean_ctor_set(v___x_599_, 2, v___x_598_);
lean_ctor_set(v___x_599_, 3, v_a_581_);
v___x_600_ = lean_array_push(v_haveInfo_584_, v___x_599_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_600_);
v___x_602_ = v___x_591_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_bodyDeps_585_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_bodyTypeDeps_586_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_body_587_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_bodyType_588_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v_level_589_);
v___x_602_ = v_reuseFailAlloc_609_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_603_ = l_Lean_LocalContext_addDecl(v_lctx_556_, v___x_598_);
v___x_604_ = l_Lean_mkFVar(v_a_583_);
v___x_605_ = lean_array_push(v_fvars_557_, v___x_604_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_numHaves_554_, v___x_606_);
lean_dec(v_numHaves_554_);
v_e_553_ = v_body_577_;
v_numHaves_554_ = v___x_607_;
v_info_555_ = v___x_602_;
v_lctx_556_ = v___x_603_;
v_fvars_557_ = v___x_605_;
goto _start;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_581_);
lean_dec_ref(v_t_578_);
lean_dec_ref(v_body_577_);
lean_dec_ref(v_value_576_);
lean_dec_ref(v_type_575_);
lean_dec(v_declName_574_);
lean_dec_ref(v_fvars_557_);
lean_dec_ref(v_lctx_556_);
lean_dec_ref(v_info_555_);
lean_dec(v_numHaves_554_);
v_a_611_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_582_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_582_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v_t_578_);
lean_dec_ref(v_body_577_);
lean_dec_ref(v_value_576_);
lean_dec_ref(v_type_575_);
lean_dec(v_declName_574_);
lean_dec_ref(v_fvars_557_);
lean_dec_ref(v_lctx_556_);
lean_dec_ref(v_info_555_);
lean_dec(v_numHaves_554_);
v_a_619_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_580_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_580_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
v___y_565_ = v_a_558_;
v___y_566_ = v_a_559_;
v___y_567_ = v_a_560_;
v___y_568_ = v_a_561_;
goto v___jp_564_;
}
}
else
{
v___y_565_ = v_a_558_;
v___y_566_ = v_a_559_;
v___y_567_ = v_a_560_;
v___y_568_ = v_a_561_;
goto v___jp_564_;
}
v___jp_564_:
{
lean_object* v_bodyDeps_569_; lean_object* v_body_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
lean_inc_ref(v_e_553_);
v_bodyDeps_569_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_554_, v_e_553_);
lean_dec(v_numHaves_554_);
v_body_570_ = lean_expr_instantiate_rev(v_e_553_, v_fvars_557_);
lean_dec_ref(v_e_553_);
v___f_571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_571_, 0, v_body_570_);
lean_closure_set(v___f_571_, 1, v___x_563_);
lean_closure_set(v___f_571_, 2, v_fvars_557_);
lean_closure_set(v___f_571_, 3, v_info_555_);
lean_closure_set(v___f_571_, 4, v_bodyDeps_569_);
v___x_572_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_556_, v___f_571_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_627_, lean_object* v_numHaves_628_, lean_object* v_info_629_, lean_object* v_lctx_630_, lean_object* v_fvars_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_627_, v_numHaves_628_, v_info_629_, v_lctx_630_, v_fvars_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_638_, lean_object* v_m_639_, lean_object* v_query_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_639_, v_query_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___boxed(lean_object* v_00_u03b2_642_, lean_object* v_m_643_, lean_object* v_query_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(v_00_u03b2_642_, v_m_643_, v_query_644_);
lean_dec(v_query_644_);
lean_dec_ref(v_m_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object* v_00_u03b2_646_, lean_object* v_m_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___redArg(v_m_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object* v_00_u03b2_649_, lean_object* v_m_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_00_u03b2_649_, v_m_650_);
lean_dec_ref(v_m_650_);
return v_res_651_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_652_, lean_object* v_k_653_, lean_object* v_t_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_653_, v_t_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_656_, lean_object* v_k_657_, lean_object* v_t_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_656_, v_k_657_, v_t_658_);
lean_dec(v_t_658_);
lean_dec(v_k_657_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_661_, lean_object* v___x_662_, lean_object* v_n_663_, lean_object* v_j_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_661_, v___x_662_, v_n_663_, v_j_664_, v_a_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_668_, lean_object* v___x_669_, lean_object* v_n_670_, lean_object* v_j_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_668_, v___x_669_, v_n_670_, v_j_671_, v_a_672_, v_a_673_);
lean_dec(v_n_670_);
lean_dec(v___x_669_);
lean_dec_ref(v_fvars_668_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9(lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___redArg(v___y_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9___boxed(lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__9(v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_687_, lean_object* v_m_688_, lean_object* v_query_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_m_688_, v_query_689_, v_x_690_, v_x_691_, v_x_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_695_, lean_object* v_m_696_, lean_object* v_query_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_695_, v_m_696_, v_query_697_, v_x_698_, v_x_699_, v_x_700_, v_x_701_);
lean_dec(v_query_697_);
lean_dec_ref(v_m_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2(lean_object* v_00_u03b2_703_, lean_object* v_init_704_, lean_object* v_b_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___redArg(v_init_704_, v_b_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2___boxed(lean_object* v_00_u03b2_707_, lean_object* v_init_708_, lean_object* v_b_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2(v_00_u03b2_707_, v_init_708_, v_b_709_);
lean_dec_ref(v_b_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_711_, lean_object* v_b_712_, lean_object* v_acc_713_, lean_object* v_i_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___redArg(v_b_712_, v_acc_713_, v_i_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_716_, lean_object* v_b_717_, lean_object* v_acc_718_, lean_object* v_i_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1_spec__2_spec__4(v_00_u03b2_716_, v_b_717_, v_acc_718_, v_i_719_);
lean_dec_ref(v_b_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_lctx_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_lctx_727_ = lean_ctor_get(v_a_722_, 2);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_730_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_727_);
v___x_731_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_721_, v___x_728_, v___x_730_, v_lctx_727_, v___x_729_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0_spec__0(lean_object* v_b_739_, lean_object* v_acc_740_, lean_object* v_i_741_){
_start:
{
lean_object* v_keyArray_746_; lean_object* v_valueArray_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_keyArray_746_ = lean_ctor_get(v_b_739_, 1);
v_valueArray_747_ = lean_ctor_get(v_b_739_, 2);
v___x_748_ = lean_array_get_size(v_keyArray_746_);
v___x_749_ = lean_nat_dec_lt(v_i_741_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v_i_741_);
return v_acc_740_;
}
else
{
lean_object* v___x_750_; uint8_t v_isSome_751_; 
v___x_750_ = lean_array_fget_borrowed(v_keyArray_746_, v_i_741_);
v_isSome_751_ = lean_noption_is_some(v___x_750_);
if (v_isSome_751_ == 0)
{
goto v___jp_742_;
}
else
{
lean_object* v___x_752_; uint8_t v_isSome_753_; 
v___x_752_ = lean_array_fget_borrowed(v_valueArray_747_, v_i_741_);
v_isSome_753_ = lean_noption_is_some(v___x_752_);
if (v_isSome_753_ == 0)
{
goto v___jp_742_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_inc(v___x_750_);
v_val_754_ = lean_noption_get(v___x_750_);
v___x_755_ = lean_box(v_isSome_753_);
v___x_756_ = lean_array_set(v_acc_740_, v_val_754_, v___x_755_);
lean_dec(v_val_754_);
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_i_741_, v___x_757_);
lean_dec(v_i_741_);
v_acc_740_ = v___x_756_;
v_i_741_ = v___x_758_;
goto _start;
}
}
}
v___jp_742_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_i_741_, v___x_743_);
lean_dec(v_i_741_);
v_i_741_ = v___x_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0_spec__0___boxed(lean_object* v_b_760_, lean_object* v_acc_761_, lean_object* v_i_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0_spec__0(v_b_760_, v_acc_761_, v_i_762_);
lean_dec_ref(v_b_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_init_764_, lean_object* v_b_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0_spec__0(v_b_765_, v_init_764_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_init_768_, lean_object* v_b_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_init_768_, v_b_769_);
lean_dec_ref(v_b_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_771_, lean_object* v_s_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_arr_771_, v_s_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_774_, lean_object* v_s_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_774_, v_s_775_);
lean_dec_ref(v_s_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_777_, lean_object* v_numHaves_778_, lean_object* v___x_779_, lean_object* v_a_780_, lean_object* v_b_781_){
_start:
{
lean_object* v_a_784_; uint8_t v___x_788_; 
v___x_788_ = lean_nat_dec_lt(v_a_780_, v_upperBound_777_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v_a_780_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_b_781_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_790_ = 0;
v___x_791_ = lean_nat_sub(v_numHaves_778_, v_a_780_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_sub(v___x_791_, v___x_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(v___x_790_);
v___x_795_ = lean_array_get(v___x_794_, v_b_781_, v___x_793_);
lean_dec(v___x_794_);
v___x_796_ = lean_unbox(v___x_795_);
lean_dec(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec(v___x_793_);
v_a_784_ = v_b_781_;
goto v___jp_783_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_typeBackDeps_799_; lean_object* v_valueBackDeps_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_797_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_798_ = lean_array_get_borrowed(v___x_797_, v___x_779_, v___x_793_);
lean_dec(v___x_793_);
v_typeBackDeps_799_ = lean_ctor_get(v___x_798_, 0);
v_valueBackDeps_800_ = lean_ctor_get(v___x_798_, 1);
v___x_801_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_781_, v_typeBackDeps_799_);
v___x_802_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v___x_801_, v_valueBackDeps_800_);
v_a_784_ = v___x_802_;
goto v___jp_783_;
}
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v_a_780_, v___x_785_);
lean_dec(v_a_780_);
v_a_780_ = v___x_786_;
v_b_781_ = v_a_784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_803_, lean_object* v_numHaves_804_, lean_object* v___x_805_, lean_object* v_a_806_, lean_object* v_b_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_803_, v_numHaves_804_, v___x_805_, v_a_806_, v_b_807_);
lean_dec_ref(v___x_805_);
lean_dec(v_numHaves_804_);
lean_dec(v_upperBound_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_810_, lean_object* v_init_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_haveInfo_817_; lean_object* v_numHaves_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v_used_821_; lean_object* v___x_822_; lean_object* v_used_823_; lean_object* v___x_824_; 
v_haveInfo_817_ = lean_ctor_get(v_info_810_, 0);
v_numHaves_818_ = lean_array_get_size(v_haveInfo_817_);
v___x_819_ = 0;
v___x_820_ = lean_box(v___x_819_);
v_used_821_ = lean_mk_array(v_numHaves_818_, v___x_820_);
v___x_822_ = lean_unsigned_to_nat(0u);
v_used_823_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_used_821_, v_init_811_);
v___x_824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_818_, v_numHaves_818_, v_haveInfo_817_, v___x_822_, v_used_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_825_, lean_object* v_init_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_825_, v_init_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec_ref(v_init_826_);
lean_dec_ref(v_info_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_833_, lean_object* v_numHaves_834_, lean_object* v___x_835_, lean_object* v_inst_836_, lean_object* v_R_837_, lean_object* v_a_838_, lean_object* v_b_839_, lean_object* v_c_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_833_, v_numHaves_834_, v___x_835_, v_a_838_, v_b_839_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_847_, lean_object* v_numHaves_848_, lean_object* v___x_849_, lean_object* v_inst_850_, lean_object* v_R_851_, lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v_c_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_847_, v_numHaves_848_, v___x_849_, v_inst_850_, v_R_851_, v_a_852_, v_b_853_, v_c_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v___x_849_);
lean_dec(v_numHaves_848_);
lean_dec(v_upperBound_847_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_863_, uint8_t v_keepUnused_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_bodyDeps_870_; lean_object* v_bodyTypeDeps_871_; lean_object* v___x_872_; 
v_bodyDeps_870_ = lean_ctor_get(v_info_863_, 1);
v_bodyTypeDeps_871_ = lean_ctor_get(v_info_863_, 2);
v___x_872_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_863_, v_bodyTypeDeps_871_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_872_) == 0)
{
if (v_keepUnused_864_ == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_863_, v_bodyDeps_870_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_a_873_);
lean_ctor_set(v___x_879_, 1, v_a_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_873_);
v_a_884_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_874_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_874_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_901_; 
v_a_892_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_901_ == 0)
{
v___x_894_ = v___x_872_;
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_872_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_896_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_a_892_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_897_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
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
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_a_902_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_872_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_872_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_910_, lean_object* v_keepUnused_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
uint8_t v_keepUnused_boxed_917_; lean_object* v_res_918_; 
v_keepUnused_boxed_917_ = lean_unbox(v_keepUnused_911_);
v_res_918_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_910_, v_keepUnused_boxed_917_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec_ref(v_info_910_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v___x_923_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_924_ = l_Lean_Expr_const___override(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = 0;
v___x_926_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_927_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_ctor_set(v___x_927_, 3, v___x_926_);
lean_ctor_set(v___x_927_, 4, v___x_926_);
lean_ctor_set_uint8(v___x_927_, sizeof(void*)*5, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_928_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_toApplicative_946_, lean_object* v_level_947_, lean_object* v_exprType_948_, lean_object* v_e_949_, uint8_t v___x_950_, lean_object* v_xs_951_, lean_object* v_____do__lift_952_){
_start:
{
if (lean_obj_tag(v_____do__lift_952_) == 0)
{
lean_object* v_toPure_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_proof_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_toPure_953_ = lean_ctor_get(v_toApplicative_946_, 1);
lean_inc(v_toPure_953_);
lean_dec_ref(v_toApplicative_946_);
v___x_954_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_955_ = lean_box(0);
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v_level_947_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_mkConst(v___x_954_, v___x_956_);
lean_inc_ref_n(v_e_949_, 3);
lean_inc_ref(v_exprType_948_);
v_proof_958_ = l_Lean_mkAppB(v___x_957_, v_exprType_948_, v_e_949_);
v___x_959_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_959_, 0, v_e_949_);
lean_ctor_set(v___x_959_, 1, v_exprType_948_);
lean_ctor_set(v___x_959_, 2, v_e_949_);
lean_ctor_set(v___x_959_, 3, v_e_949_);
lean_ctor_set(v___x_959_, 4, v_proof_958_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*5, v___x_950_);
v___x_960_ = lean_apply_2(v_toPure_953_, lean_box(0), v___x_959_);
return v___x_960_;
}
else
{
lean_object* v_e_961_; lean_object* v_h_962_; lean_object* v_expr_963_; lean_object* v_proof_964_; lean_object* v___x_970_; uint8_t v___x_971_; 
lean_dec(v_level_947_);
v_e_961_ = lean_ctor_get(v_____do__lift_952_, 0);
v_h_962_ = lean_ctor_get(v_____do__lift_952_, 1);
v_expr_963_ = lean_expr_abstract(v_e_961_, v_xs_951_);
v_proof_964_ = lean_expr_abstract(v_h_962_, v_xs_951_);
lean_inc_ref(v_proof_964_);
v___x_970_ = l_Lean_Expr_cleanupAnnotations(v_proof_964_);
v___x_971_ = l_Lean_Expr_isApp(v___x_970_);
if (v___x_971_ == 0)
{
lean_dec_ref(v___x_970_);
goto v___jp_965_;
}
else
{
lean_object* v_arg_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_arg_972_ = lean_ctor_get(v___x_970_, 1);
lean_inc_ref(v_arg_972_);
v___x_973_ = l_Lean_Expr_appFnCleanup___redArg(v___x_970_);
v___x_974_ = l_Lean_Expr_isApp(v___x_973_);
if (v___x_974_ == 0)
{
lean_dec_ref(v___x_973_);
lean_dec_ref(v_arg_972_);
goto v___jp_965_;
}
else
{
lean_object* v_arg_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_arg_975_ = lean_ctor_get(v___x_973_, 1);
lean_inc_ref(v_arg_975_);
v___x_976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_973_);
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_978_ = l_Lean_Expr_isConstOf(v___x_976_, v___x_977_);
lean_dec_ref(v___x_976_);
if (v___x_978_ == 0)
{
lean_dec_ref(v_arg_975_);
lean_dec_ref(v_arg_972_);
goto v___jp_965_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_980_ = lean_unsigned_to_nat(3u);
v___x_981_ = l_Lean_Expr_isAppOfArity(v_arg_975_, v___x_979_, v___x_980_);
lean_dec_ref(v_arg_975_);
if (v___x_981_ == 0)
{
lean_dec_ref(v_arg_972_);
goto v___jp_965_;
}
else
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = l_Lean_Expr_cleanupAnnotations(v_arg_972_);
v___x_983_ = l_Lean_Expr_isApp(v___x_982_);
if (v___x_983_ == 0)
{
lean_dec_ref(v___x_982_);
goto v___jp_965_;
}
else
{
lean_object* v_arg_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_arg_984_ = lean_ctor_get(v___x_982_, 1);
lean_inc_ref(v_arg_984_);
v___x_985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_982_);
v___x_986_ = l_Lean_Expr_isApp(v___x_985_);
if (v___x_986_ == 0)
{
lean_dec_ref(v___x_985_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v_arg_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_arg_987_ = lean_ctor_get(v___x_985_, 1);
lean_inc_ref(v_arg_987_);
v___x_988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_985_);
v___x_989_ = l_Lean_Expr_isConstOf(v___x_988_, v___x_977_);
lean_dec_ref(v___x_988_);
if (v___x_989_ == 0)
{
lean_dec_ref(v_arg_987_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = l_Lean_Expr_cleanupAnnotations(v_arg_987_);
v___x_991_ = l_Lean_Expr_isApp(v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v___x_990_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v_arg_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_arg_992_ = lean_ctor_get(v___x_990_, 1);
lean_inc_ref(v_arg_992_);
v___x_993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_990_);
v___x_994_ = l_Lean_Expr_isApp(v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_993_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v_arg_995_; uint8_t v___y_997_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v_arg_995_ = lean_ctor_get(v___x_993_, 1);
lean_inc_ref(v_arg_995_);
v___x_1001_ = l_Lean_Expr_appFnCleanup___redArg(v___x_993_);
v___x_1002_ = l_Lean_Expr_isApp(v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v___x_1001_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1001_);
v___x_1004_ = l_Lean_Expr_isConstOf(v___x_1003_, v___x_979_);
lean_dec_ref(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Expr_getAppFn(v_arg_984_);
if (lean_obj_tag(v___x_1005_) == 4)
{
lean_object* v_declName_1006_; 
v_declName_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_declName_1006_);
lean_dec_ref_known(v___x_1005_, 2);
if (lean_obj_tag(v_declName_1006_) == 1)
{
lean_object* v_pre_1007_; 
v_pre_1007_ = lean_ctor_get(v_declName_1006_, 0);
if (lean_obj_tag(v_pre_1007_) == 0)
{
lean_object* v_str_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_str_1008_ = lean_ctor_get(v_declName_1006_, 1);
lean_inc_ref(v_str_1008_);
lean_dec_ref_known(v_declName_1006_, 2);
v___x_1009_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_1010_ = lean_string_dec_eq(v_str_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_1012_ = lean_string_dec_eq(v_str_1008_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_1014_ = lean_string_dec_eq(v_str_1008_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_1016_ = lean_string_dec_eq(v_str_1008_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_1018_ = lean_string_dec_eq(v_str_1008_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_1020_ = lean_string_dec_eq(v_str_1008_, v___x_1019_);
lean_dec_ref(v_str_1008_);
if (v___x_1020_ == 0)
{
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
v___y_997_ = v___x_978_;
goto v___jp_996_;
}
}
else
{
lean_dec_ref(v_str_1008_);
v___y_997_ = v___x_978_;
goto v___jp_996_;
}
}
else
{
lean_dec_ref(v_str_1008_);
v___y_997_ = v___x_978_;
goto v___jp_996_;
}
}
else
{
lean_dec_ref(v_str_1008_);
v___y_997_ = v___x_978_;
goto v___jp_996_;
}
}
else
{
lean_dec_ref(v_str_1008_);
v___y_997_ = v___x_978_;
goto v___jp_996_;
}
}
else
{
lean_dec_ref(v_str_1008_);
v___y_997_ = v___x_978_;
goto v___jp_996_;
}
}
else
{
lean_dec_ref_known(v_declName_1006_, 2);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
}
else
{
lean_dec(v_declName_1006_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
}
else
{
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
}
}
v___jp_996_:
{
if (v___y_997_ == 0)
{
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_984_);
goto v___jp_965_;
}
else
{
lean_object* v_toPure_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref(v_proof_964_);
lean_dec_ref(v_e_949_);
v_toPure_998_ = lean_ctor_get(v_toApplicative_946_, 1);
lean_inc(v_toPure_998_);
lean_dec_ref(v_toApplicative_946_);
v___x_999_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_999_, 0, v_arg_992_);
lean_ctor_set(v___x_999_, 1, v_exprType_948_);
lean_ctor_set(v___x_999_, 2, v_arg_995_);
lean_ctor_set(v___x_999_, 3, v_expr_963_);
lean_ctor_set(v___x_999_, 4, v_arg_984_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*5, v___x_978_);
v___x_1000_ = lean_apply_2(v_toPure_998_, lean_box(0), v___x_999_);
return v___x_1000_;
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
v___jp_965_:
{
lean_object* v_toPure_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_toPure_966_ = lean_ctor_get(v_toApplicative_946_, 1);
lean_inc(v_toPure_966_);
lean_dec_ref(v_toApplicative_946_);
v___x_967_ = 1;
lean_inc_ref(v_expr_963_);
v___x_968_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_968_, 0, v_expr_963_);
lean_ctor_set(v___x_968_, 1, v_exprType_948_);
lean_ctor_set(v___x_968_, 2, v_e_949_);
lean_ctor_set(v___x_968_, 3, v_expr_963_);
lean_ctor_set(v___x_968_, 4, v_proof_964_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*5, v___x_967_);
v___x_969_ = lean_apply_2(v_toPure_966_, lean_box(0), v___x_968_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_toApplicative_1021_, lean_object* v_level_1022_, lean_object* v_exprType_1023_, lean_object* v_e_1024_, lean_object* v___x_1025_, lean_object* v_xs_1026_, lean_object* v_____do__lift_1027_){
_start:
{
uint8_t v___x_12297__boxed_1028_; lean_object* v_res_1029_; 
v___x_12297__boxed_1028_ = lean_unbox(v___x_1025_);
v_res_1029_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_1021_, v_level_1022_, v_exprType_1023_, v_e_1024_, v___x_12297__boxed_1028_, v_xs_1026_, v_____do__lift_1027_);
lean_dec(v_____do__lift_1027_);
lean_dec_ref(v_xs_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_1030_, lean_object* v_bodyType_1031_, lean_object* v_xs_1032_, lean_object* v_toApplicative_1033_, lean_object* v_level_1034_, lean_object* v_e_1035_, uint8_t v___x_1036_, lean_object* v_body_1037_, lean_object* v_toBind_1038_, lean_object* v_____r_1039_){
_start:
{
lean_object* v_simp_1040_; lean_object* v_exprType_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_simp_1040_ = lean_ctor_get(v_inst_1030_, 2);
lean_inc(v_simp_1040_);
lean_dec_ref(v_inst_1030_);
v_exprType_1041_ = lean_expr_abstract(v_bodyType_1031_, v_xs_1032_);
v___x_1042_ = lean_box(v___x_1036_);
v___f_1043_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1043_, 0, v_toApplicative_1033_);
lean_closure_set(v___f_1043_, 1, v_level_1034_);
lean_closure_set(v___f_1043_, 2, v_exprType_1041_);
lean_closure_set(v___f_1043_, 3, v_e_1035_);
lean_closure_set(v___f_1043_, 4, v___x_1042_);
lean_closure_set(v___f_1043_, 5, v_xs_1032_);
v___x_1044_ = lean_apply_1(v_simp_1040_, v_body_1037_);
v___x_1045_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1044_, v___f_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_1046_, lean_object* v_bodyType_1047_, lean_object* v_xs_1048_, lean_object* v_toApplicative_1049_, lean_object* v_level_1050_, lean_object* v_e_1051_, lean_object* v___x_1052_, lean_object* v_body_1053_, lean_object* v_toBind_1054_, lean_object* v_____r_1055_){
_start:
{
uint8_t v___x_12450__boxed_1056_; lean_object* v_res_1057_; 
v___x_12450__boxed_1056_ = lean_unbox(v___x_1052_);
v_res_1057_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_1046_, v_bodyType_1047_, v_xs_1048_, v_toApplicative_1049_, v_level_1050_, v_e_1051_, v___x_12450__boxed_1056_, v_body_1053_, v_toBind_1054_, v_____r_1055_);
lean_dec_ref(v_bodyType_1047_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_1066_, lean_object* v___x_1067_, lean_object* v___f_1068_, lean_object* v_body_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_options_1080_; uint8_t v_hasTrace_1081_; 
v_options_1080_ = lean_ctor_get(v___y_1074_, 2);
v_hasTrace_1081_ = lean_ctor_get_uint8(v_options_1080_, sizeof(void*)*1);
if (v_hasTrace_1081_ == 0)
{
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec_ref(v___x_1071_);
lean_dec_ref(v___x_1070_);
lean_dec_ref(v_body_1069_);
lean_dec(v___f_1068_);
lean_dec(v___x_1067_);
lean_dec(v_cls_1066_);
goto v___jp_1077_;
}
else
{
lean_object* v_inheritedTraceOptions_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_inheritedTraceOptions_1082_ = lean_ctor_get(v___y_1074_, 13);
v___x_1083_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1066_);
v___x_1084_ = l_Lean_Name_append(v___x_1083_, v_cls_1066_);
v___x_1085_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1082_, v_options_1080_, v___x_1084_);
lean_dec(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec_ref(v___x_1071_);
lean_dec_ref(v___x_1070_);
lean_dec_ref(v_body_1069_);
lean_dec(v___f_1068_);
lean_dec(v___x_1067_);
lean_dec(v_cls_1066_);
goto v___jp_1077_;
}
else
{
lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_toMonadRef_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_11852__overap_1096_; lean_object* v___x_1097_; 
v___f_1086_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1087_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1088_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1089_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1087_, v___x_1067_, v___x_1088_);
v___x_1090_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1086_, v___f_1068_, v___x_1089_);
v_toMonadRef_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc_ref(v_toMonadRef_1091_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1093_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5);
v___x_1094_ = l_Lean_MessageData_ofExpr(v_body_1069_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_11852__overap_1096_ = l_Lean_addTrace___redArg(v___x_1070_, v___x_1071_, v_toMonadRef_1091_, v___x_1092_, v_cls_1066_, v___x_1095_);
v___x_1097_ = lean_apply_5(v___x_11852__overap_1096_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, lean_box(0));
return v___x_1097_;
}
}
v___jp_1077_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_1098_, lean_object* v___x_1099_, lean_object* v___f_1100_, lean_object* v_body_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_1098_, v___x_1099_, v___f_1100_, v_body_1101_, v___x_1102_, v___x_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_1112_, lean_object* v_type_1113_, lean_object* v___y_1114_, lean_object* v_value_1115_, uint8_t v_nondep_1116_, lean_object* v_toApplicative_1117_, lean_object* v___x_1118_, uint8_t v___y_1119_, lean_object* v_us_1120_, lean_object* v_rb_1121_){
_start:
{
lean_object* v_expr_1122_; lean_object* v_exprType_1123_; lean_object* v_exprInit_1124_; lean_object* v_exprResult_1125_; lean_object* v_proof_1126_; uint8_t v_modified_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1156_; 
v_expr_1122_ = lean_ctor_get(v_rb_1121_, 0);
v_exprType_1123_ = lean_ctor_get(v_rb_1121_, 1);
v_exprInit_1124_ = lean_ctor_get(v_rb_1121_, 2);
v_exprResult_1125_ = lean_ctor_get(v_rb_1121_, 3);
v_proof_1126_ = lean_ctor_get(v_rb_1121_, 4);
v_modified_1127_ = lean_ctor_get_uint8(v_rb_1121_, sizeof(void*)*5);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_rb_1121_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1129_ = v_rb_1121_;
v_isShared_1130_ = v_isSharedCheck_1156_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_proof_1126_);
lean_inc(v_exprResult_1125_);
lean_inc(v_exprInit_1124_);
lean_inc(v_exprType_1123_);
lean_inc(v_expr_1122_);
lean_dec(v_rb_1121_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1156_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v_expr_1133_; lean_object* v___x_1134_; lean_object* v_exprType_1135_; lean_object* v___x_1136_; lean_object* v_exprInit_1137_; lean_object* v_exprResult_1138_; 
v___x_1131_ = 0;
lean_inc_ref_n(v_type_1113_, 4);
lean_inc_n(v_declName_1112_, 4);
v___x_1132_ = l_Lean_mkLambda(v_declName_1112_, v___x_1131_, v_type_1113_, v_expr_1122_);
lean_inc_ref_n(v___y_1114_, 3);
lean_inc_ref(v___x_1132_);
v_expr_1133_ = l_Lean_Expr_app___override(v___x_1132_, v___y_1114_);
v___x_1134_ = l_Lean_mkLambda(v_declName_1112_, v___x_1131_, v_type_1113_, v_exprType_1123_);
lean_inc_ref(v___x_1134_);
v_exprType_1135_ = l_Lean_Expr_app___override(v___x_1134_, v___y_1114_);
v___x_1136_ = l_Lean_mkLambda(v_declName_1112_, v___x_1131_, v_type_1113_, v_exprInit_1124_);
lean_inc_ref(v___x_1136_);
v_exprInit_1137_ = l_Lean_Expr_app___override(v___x_1136_, v_value_1115_);
v_exprResult_1138_ = l_Lean_Expr_letE___override(v_declName_1112_, v_type_1113_, v___y_1114_, v_exprResult_1125_, v_nondep_1116_);
if (v_modified_1127_ == 0)
{
lean_object* v_toPure_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_proof_1142_; lean_object* v___x_1144_; 
lean_dec_ref(v___x_1136_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_proof_1126_);
lean_dec(v_us_1120_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_type_1113_);
lean_dec(v_declName_1112_);
v_toPure_1139_ = lean_ctor_get(v_toApplicative_1117_, 1);
lean_inc(v_toPure_1139_);
lean_dec_ref(v_toApplicative_1117_);
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1141_ = l_Lean_mkConst(v___x_1140_, v___x_1118_);
lean_inc_ref(v_expr_1133_);
lean_inc_ref(v_exprType_1135_);
v_proof_1142_ = l_Lean_mkAppB(v___x_1141_, v_exprType_1135_, v_expr_1133_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v_proof_1142_);
lean_ctor_set(v___x_1129_, 3, v_exprResult_1138_);
lean_ctor_set(v___x_1129_, 2, v_exprInit_1137_);
lean_ctor_set(v___x_1129_, 1, v_exprType_1135_);
lean_ctor_set(v___x_1129_, 0, v_expr_1133_);
v___x_1144_ = v___x_1129_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_expr_1133_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_exprType_1135_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_exprInit_1137_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_exprResult_1138_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_proof_1142_);
v___x_1144_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; 
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*5, v___y_1119_);
v___x_1145_ = lean_apply_2(v_toPure_1139_, lean_box(0), v___x_1144_);
return v___x_1145_;
}
}
else
{
lean_object* v_toPure_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_proof_1151_; lean_object* v___x_1153_; 
lean_dec(v___x_1118_);
v_toPure_1147_ = lean_ctor_get(v_toApplicative_1117_, 1);
lean_inc(v_toPure_1147_);
lean_dec_ref(v_toApplicative_1117_);
lean_inc_ref(v_type_1113_);
v___x_1148_ = l_Lean_mkLambda(v_declName_1112_, v___x_1131_, v_type_1113_, v_proof_1126_);
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_1150_ = l_Lean_mkConst(v___x_1149_, v_us_1120_);
v_proof_1151_ = l_Lean_mkApp6(v___x_1150_, v_type_1113_, v___x_1134_, v___y_1114_, v___x_1136_, v___x_1132_, v___x_1148_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v_proof_1151_);
lean_ctor_set(v___x_1129_, 3, v_exprResult_1138_);
lean_ctor_set(v___x_1129_, 2, v_exprInit_1137_);
lean_ctor_set(v___x_1129_, 1, v_exprType_1135_);
lean_ctor_set(v___x_1129_, 0, v_expr_1133_);
v___x_1153_ = v___x_1129_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_expr_1133_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_exprType_1135_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_exprInit_1137_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_exprResult_1138_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_proof_1151_);
v___x_1153_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*5, v_nondep_1116_);
v___x_1154_ = lean_apply_2(v_toPure_1147_, lean_box(0), v___x_1153_);
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_1157_, lean_object* v_type_1158_, lean_object* v___y_1159_, lean_object* v_value_1160_, lean_object* v_nondep_1161_, lean_object* v_toApplicative_1162_, lean_object* v___x_1163_, lean_object* v___y_1164_, lean_object* v_us_1165_, lean_object* v_rb_1166_){
_start:
{
uint8_t v_nondep_12566__boxed_1167_; uint8_t v___y_12568__boxed_1168_; lean_object* v_res_1169_; 
v_nondep_12566__boxed_1167_ = lean_unbox(v_nondep_1161_);
v___y_12568__boxed_1168_ = lean_unbox(v___y_1164_);
v_res_1169_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_1157_, v_type_1158_, v___y_1159_, v_value_1160_, v_nondep_12566__boxed_1167_, v_toApplicative_1162_, v___x_1163_, v___y_12568__boxed_1168_, v_us_1165_, v_rb_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1170_, lean_object* v_____x_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_apply_1(v___f_1170_, v_____x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1177_, lean_object* v_declName_1178_, lean_object* v_type_1179_, lean_object* v_value_1180_, lean_object* v_us_1181_, lean_object* v___x_1182_, lean_object* v_toApplicative_1183_, uint8_t v_nondep_1184_, lean_object* v_rb_1185_){
_start:
{
lean_object* v_expr_1186_; lean_object* v_exprType_1187_; lean_object* v_exprInit_1188_; lean_object* v_exprResult_1189_; lean_object* v_proof_1190_; uint8_t v_modified_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1221_; 
v_expr_1186_ = lean_ctor_get(v_rb_1185_, 0);
v_exprType_1187_ = lean_ctor_get(v_rb_1185_, 1);
v_exprInit_1188_ = lean_ctor_get(v_rb_1185_, 2);
v_exprResult_1189_ = lean_ctor_get(v_rb_1185_, 3);
v_proof_1190_ = lean_ctor_get(v_rb_1185_, 4);
v_modified_1191_ = lean_ctor_get_uint8(v_rb_1185_, sizeof(void*)*5);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_rb_1185_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1193_ = v_rb_1185_;
v_isShared_1194_ = v_isSharedCheck_1221_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_proof_1190_);
lean_inc(v_exprResult_1189_);
lean_inc(v_exprInit_1188_);
lean_inc(v_exprType_1187_);
lean_inc(v_expr_1186_);
lean_dec(v_rb_1185_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1221_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_expr_1195_; lean_object* v_exprType_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v_exprInit_1199_; lean_object* v_exprResult_1200_; 
v_expr_1195_ = lean_expr_lower_loose_bvars(v_expr_1186_, v___x_1177_, v___x_1177_);
lean_dec_ref(v_expr_1186_);
v_exprType_1196_ = lean_expr_lower_loose_bvars(v_exprType_1187_, v___x_1177_, v___x_1177_);
lean_dec_ref(v_exprType_1187_);
v___x_1197_ = 0;
lean_inc_ref(v_type_1179_);
lean_inc(v_declName_1178_);
v___x_1198_ = l_Lean_mkLambda(v_declName_1178_, v___x_1197_, v_type_1179_, v_exprInit_1188_);
lean_inc_ref(v_value_1180_);
lean_inc_ref(v___x_1198_);
v_exprInit_1199_ = l_Lean_Expr_app___override(v___x_1198_, v_value_1180_);
v_exprResult_1200_ = lean_expr_lower_loose_bvars(v_exprResult_1189_, v___x_1177_, v___x_1177_);
lean_dec_ref(v_exprResult_1189_);
if (v_modified_1191_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_proof_1206_; lean_object* v_toPure_1207_; lean_object* v___x_1209_; 
lean_dec_ref(v___x_1198_);
lean_dec_ref(v_proof_1190_);
lean_dec(v_declName_1178_);
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1202_ = l_Lean_mkConst(v___x_1201_, v_us_1181_);
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1204_ = l_Lean_mkConst(v___x_1203_, v___x_1182_);
lean_inc_ref_n(v_expr_1195_, 3);
lean_inc_ref_n(v_exprType_1196_, 2);
v___x_1205_ = l_Lean_mkAppB(v___x_1204_, v_exprType_1196_, v_expr_1195_);
v_proof_1206_ = l_Lean_mkApp6(v___x_1202_, v_type_1179_, v_exprType_1196_, v_value_1180_, v_expr_1195_, v_expr_1195_, v___x_1205_);
v_toPure_1207_ = lean_ctor_get(v_toApplicative_1183_, 1);
lean_inc(v_toPure_1207_);
lean_dec_ref(v_toApplicative_1183_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 4, v_proof_1206_);
lean_ctor_set(v___x_1193_, 3, v_exprResult_1200_);
lean_ctor_set(v___x_1193_, 2, v_exprInit_1199_);
lean_ctor_set(v___x_1193_, 1, v_exprType_1196_);
lean_ctor_set(v___x_1193_, 0, v_expr_1195_);
v___x_1209_ = v___x_1193_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_expr_1195_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_exprType_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_exprInit_1199_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_exprResult_1200_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_proof_1206_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*5, v_nondep_1184_);
v___x_1210_ = lean_apply_2(v_toPure_1207_, lean_box(0), v___x_1209_);
return v___x_1210_;
}
}
else
{
lean_object* v_toPure_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_proof_1216_; lean_object* v___x_1218_; 
lean_dec(v___x_1182_);
v_toPure_1212_ = lean_ctor_get(v_toApplicative_1183_, 1);
lean_inc(v_toPure_1212_);
lean_dec_ref(v_toApplicative_1183_);
lean_inc_ref(v_type_1179_);
v___x_1213_ = l_Lean_mkLambda(v_declName_1178_, v___x_1197_, v_type_1179_, v_proof_1190_);
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1215_ = l_Lean_mkConst(v___x_1214_, v_us_1181_);
lean_inc_ref(v_expr_1195_);
lean_inc_ref(v_exprType_1196_);
v_proof_1216_ = l_Lean_mkApp6(v___x_1215_, v_type_1179_, v_exprType_1196_, v_value_1180_, v___x_1198_, v_expr_1195_, v___x_1213_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 4, v_proof_1216_);
lean_ctor_set(v___x_1193_, 3, v_exprResult_1200_);
lean_ctor_set(v___x_1193_, 2, v_exprInit_1199_);
lean_ctor_set(v___x_1193_, 1, v_exprType_1196_);
lean_ctor_set(v___x_1193_, 0, v_expr_1195_);
v___x_1218_ = v___x_1193_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_expr_1195_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_exprType_1196_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_exprInit_1199_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_exprResult_1200_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_proof_1216_);
v___x_1218_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; 
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*5, v_nondep_1184_);
v___x_1219_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1218_);
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1222_, lean_object* v_declName_1223_, lean_object* v_type_1224_, lean_object* v_value_1225_, lean_object* v_us_1226_, lean_object* v___x_1227_, lean_object* v_toApplicative_1228_, lean_object* v_nondep_1229_, lean_object* v_rb_1230_){
_start:
{
uint8_t v_nondep_12653__boxed_1231_; lean_object* v_res_1232_; 
v_nondep_12653__boxed_1231_ = lean_unbox(v_nondep_1229_);
v_res_1232_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1222_, v_declName_1223_, v_type_1224_, v_value_1225_, v_us_1226_, v___x_1227_, v_toApplicative_1228_, v_nondep_12653__boxed_1231_, v_rb_1230_);
lean_dec(v___x_1222_);
return v_res_1232_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1238_ = l_Lean_stringToMessageData(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1239_, lean_object* v___x_1240_, lean_object* v___f_1241_, lean_object* v_declName_1242_, lean_object* v_val_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_options_1254_; uint8_t v_hasTrace_1255_; 
v_options_1254_ = lean_ctor_get(v___y_1248_, 2);
v_hasTrace_1255_ = lean_ctor_get_uint8(v_options_1254_, sizeof(void*)*1);
if (v_hasTrace_1255_ == 0)
{
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_val_1243_);
lean_dec(v_declName_1242_);
lean_dec(v___f_1241_);
lean_dec(v___x_1240_);
lean_dec(v_cls_1239_);
goto v___jp_1251_;
}
else
{
lean_object* v_inheritedTraceOptions_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_inheritedTraceOptions_1256_ = lean_ctor_get(v___y_1248_, 13);
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1239_);
v___x_1258_ = l_Lean_Name_append(v___x_1257_, v_cls_1239_);
v___x_1259_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1256_, v_options_1254_, v___x_1258_);
lean_dec(v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_val_1243_);
lean_dec(v_declName_1242_);
lean_dec(v___f_1241_);
lean_dec(v___x_1240_);
lean_dec(v_cls_1239_);
goto v___jp_1251_;
}
else
{
lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_toMonadRef_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_12263__overap_1274_; lean_object* v___x_1275_; 
v___f_1260_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1261_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1262_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1263_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1261_, v___x_1240_, v___x_1262_);
v___x_1264_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1260_, v___f_1241_, v___x_1263_);
v_toMonadRef_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc_ref(v_toMonadRef_1265_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1267_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1268_ = l_Lean_MessageData_ofName(v_declName_1242_);
v___x_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_MessageData_ofExpr(v_val_1243_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_12263__overap_1274_ = l_Lean_addTrace___redArg(v___x_1244_, v___x_1245_, v_toMonadRef_1265_, v___x_1266_, v_cls_1239_, v___x_1273_);
v___x_1275_ = lean_apply_5(v___x_12263__overap_1274_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, lean_box(0));
return v___x_1275_;
}
}
v___jp_1251_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1276_, lean_object* v___x_1277_, lean_object* v___f_1278_, lean_object* v_declName_1279_, lean_object* v_val_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1276_, v___x_1277_, v___f_1278_, v_declName_1279_, v_val_1280_, v___x_1281_, v___x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v_res_1288_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1295_, lean_object* v___x_1296_, lean_object* v___f_1297_, lean_object* v_declName_1298_, lean_object* v_val_1299_, lean_object* v_val_x27_1300_, lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_options_1311_; uint8_t v_hasTrace_1312_; 
v_options_1311_ = lean_ctor_get(v___y_1305_, 2);
v_hasTrace_1312_ = lean_ctor_get_uint8(v_options_1311_, sizeof(void*)*1);
if (v_hasTrace_1312_ == 0)
{
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v___x_1302_);
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_val_x27_1300_);
lean_dec_ref(v_val_1299_);
lean_dec(v_declName_1298_);
lean_dec(v___f_1297_);
lean_dec(v___x_1296_);
lean_dec(v_cls_1295_);
goto v___jp_1308_;
}
else
{
lean_object* v_inheritedTraceOptions_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_inheritedTraceOptions_1313_ = lean_ctor_get(v___y_1305_, 13);
v___x_1314_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1295_);
v___x_1315_ = l_Lean_Name_append(v___x_1314_, v_cls_1295_);
v___x_1316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1313_, v_options_1311_, v___x_1315_);
lean_dec(v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v___x_1302_);
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_val_x27_1300_);
lean_dec_ref(v_val_1299_);
lean_dec(v_declName_1298_);
lean_dec(v___f_1297_);
lean_dec(v___x_1296_);
lean_dec(v_cls_1295_);
goto v___jp_1308_;
}
else
{
lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v_toMonadRef_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_11945__overap_1335_; lean_object* v___x_1336_; 
v___f_1317_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1318_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1319_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1320_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1318_, v___x_1296_, v___x_1319_);
v___x_1321_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1317_, v___f_1297_, v___x_1320_);
v_toMonadRef_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref(v_toMonadRef_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1324_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1325_ = l_Lean_MessageData_ofName(v_declName_1298_);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_MessageData_ofExpr(v_val_1299_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_MessageData_ofExpr(v_val_x27_1300_);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_11945__overap_1335_ = l_Lean_addTrace___redArg(v___x_1301_, v___x_1302_, v_toMonadRef_1322_, v___x_1323_, v_cls_1295_, v___x_1334_);
v___x_1336_ = lean_apply_5(v___x_11945__overap_1335_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
return v___x_1336_;
}
}
v___jp_1308_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1337_, lean_object* v___x_1338_, lean_object* v___f_1339_, lean_object* v_declName_1340_, lean_object* v_val_1341_, lean_object* v_val_x27_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1337_, v___x_1338_, v___f_1339_, v_declName_1340_, v_val_1341_, v_val_x27_1342_, v___x_1343_, v___x_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_toApplicative_1351_, lean_object* v_e_1352_, lean_object* v_xs_1353_, lean_object* v_h_1354_, uint8_t v_nondep_1355_, lean_object* v_toBind_1356_, lean_object* v___f_1357_, lean_object* v_____r_1358_){
_start:
{
lean_object* v_toPure_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_toPure_1359_ = lean_ctor_get(v_toApplicative_1351_, 1);
lean_inc(v_toPure_1359_);
lean_dec_ref(v_toApplicative_1351_);
v___x_1360_ = lean_expr_abstract(v_e_1352_, v_xs_1353_);
v___x_1361_ = lean_expr_abstract(v_h_1354_, v_xs_1353_);
v___x_1362_ = lean_box(v_nondep_1355_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___x_1361_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1360_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_apply_2(v_toPure_1359_, lean_box(0), v___x_1364_);
v___x_1366_ = lean_apply_4(v_toBind_1356_, lean_box(0), lean_box(0), v___x_1365_, v___f_1357_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_toApplicative_1367_, lean_object* v_e_1368_, lean_object* v_xs_1369_, lean_object* v_h_1370_, lean_object* v_nondep_1371_, lean_object* v_toBind_1372_, lean_object* v___f_1373_, lean_object* v_____r_1374_){
_start:
{
uint8_t v_nondep_12919__boxed_1375_; lean_object* v_res_1376_; 
v_nondep_12919__boxed_1375_ = lean_unbox(v_nondep_1371_);
v_res_1376_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1367_, v_e_1368_, v_xs_1369_, v_h_1370_, v_nondep_12919__boxed_1375_, v_toBind_1372_, v___f_1373_, v_____r_1374_);
lean_dec_ref(v_h_1370_);
lean_dec_ref(v_xs_1369_);
lean_dec_ref(v_e_1368_);
return v_res_1376_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1380_, lean_object* v___x_1381_, lean_object* v___f_1382_, lean_object* v_declName_1383_, lean_object* v_val_1384_, lean_object* v_e_1385_, lean_object* v___x_1386_, lean_object* v___x_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_options_1396_; uint8_t v_hasTrace_1397_; 
v_options_1396_ = lean_ctor_get(v___y_1390_, 2);
v_hasTrace_1397_ = lean_ctor_get_uint8(v_options_1396_, sizeof(void*)*1);
if (v_hasTrace_1397_ == 0)
{
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___x_1387_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_e_1385_);
lean_dec_ref(v_val_1384_);
lean_dec(v_declName_1383_);
lean_dec(v___f_1382_);
lean_dec(v___x_1381_);
lean_dec(v_cls_1380_);
goto v___jp_1393_;
}
else
{
lean_object* v_inheritedTraceOptions_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_inheritedTraceOptions_1398_ = lean_ctor_get(v___y_1390_, 13);
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1380_);
v___x_1400_ = l_Lean_Name_append(v___x_1399_, v_cls_1380_);
v___x_1401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1398_, v_options_1396_, v___x_1400_);
lean_dec(v___x_1400_);
if (v___x_1401_ == 0)
{
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___x_1387_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_e_1385_);
lean_dec_ref(v_val_1384_);
lean_dec(v_declName_1383_);
lean_dec(v___f_1382_);
lean_dec(v___x_1381_);
lean_dec(v_cls_1380_);
goto v___jp_1393_;
}
else
{
lean_object* v___f_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_toMonadRef_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_12125__overap_1420_; lean_object* v___x_1421_; 
v___f_1402_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1403_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1404_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1405_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1403_, v___x_1381_, v___x_1404_);
v___x_1406_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1402_, v___f_1382_, v___x_1405_);
v_toMonadRef_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_toMonadRef_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1410_ = l_Lean_MessageData_ofName(v_declName_1383_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_MessageData_ofExpr(v_val_1384_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_MessageData_ofExpr(v_e_1385_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_12125__overap_1420_ = l_Lean_addTrace___redArg(v___x_1386_, v___x_1387_, v_toMonadRef_1407_, v___x_1408_, v_cls_1380_, v___x_1419_);
v___x_1421_ = lean_apply_5(v___x_12125__overap_1420_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, lean_box(0));
return v___x_1421_;
}
}
v___jp_1393_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1422_, lean_object* v___x_1423_, lean_object* v___f_1424_, lean_object* v_declName_1425_, lean_object* v_val_1426_, lean_object* v_e_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1422_, v___x_1423_, v___f_1424_, v_declName_1425_, v_val_1426_, v_e_1427_, v___x_1428_, v___x_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v_res_1435_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_instMonadEIO(lean_box(0));
return v___x_1436_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
v___x_1438_ = l_StateRefT_x27_instMonad___redArg(v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1456_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1455_, v___x_1454_);
return v___x_1456_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
v___f_1458_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1459_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1458_, v___x_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_toApplicative_1460_, lean_object* v_level_1461_, lean_object* v___x_1462_, lean_object* v_type_1463_, lean_object* v_value_1464_, uint8_t v___x_1465_, lean_object* v_toBind_1466_, lean_object* v___f_1467_, lean_object* v_xs_1468_, uint8_t v_nondep_1469_, lean_object* v___f_1470_, lean_object* v_declName_1471_, lean_object* v_val_1472_, lean_object* v_inst_1473_, lean_object* v_____do__lift_1474_){
_start:
{
if (lean_obj_tag(v_____do__lift_1474_) == 0)
{
lean_object* v_toPure_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v_inst_1473_);
lean_dec_ref(v_val_1472_);
lean_dec(v_declName_1471_);
lean_dec(v___f_1470_);
lean_dec_ref(v_xs_1468_);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1460_, 1);
lean_inc(v_toPure_1475_);
lean_dec_ref(v_toApplicative_1460_);
v___x_1476_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_level_1461_);
lean_ctor_set(v___x_1477_, 1, v___x_1462_);
v___x_1478_ = l_Lean_mkConst(v___x_1476_, v___x_1477_);
lean_inc_ref(v_value_1464_);
v___x_1479_ = l_Lean_mkAppB(v___x_1478_, v_type_1463_, v_value_1464_);
v___x_1480_ = lean_box(v___x_1465_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_value_1464_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_apply_2(v_toPure_1475_, lean_box(0), v___x_1482_);
v___x_1484_ = lean_apply_4(v_toBind_1466_, lean_box(0), lean_box(0), v___x_1483_, v___f_1467_);
return v___x_1484_;
}
else
{
lean_object* v_e_1485_; lean_object* v_h_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v___f_1467_);
lean_dec_ref(v_value_1464_);
lean_dec_ref(v_type_1463_);
lean_dec(v___x_1462_);
lean_dec(v_level_1461_);
v_e_1485_ = lean_ctor_get(v_____do__lift_1474_, 0);
v_h_1486_ = lean_ctor_get(v_____do__lift_1474_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_____do__lift_1474_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1488_ = v_____do__lift_1474_;
v_isShared_1489_ = v_isSharedCheck_1547_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_h_1486_);
lean_inc(v_e_1485_);
lean_dec(v_____do__lift_1474_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1547_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v_toApplicative_1491_; lean_object* v_toFunctor_1492_; lean_object* v_toSeq_1493_; lean_object* v_toSeqLeft_1494_; lean_object* v_toSeqRight_1495_; lean_object* v___f_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; lean_object* v___f_1499_; lean_object* v___x_1501_; 
v___x_1490_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1491_ = lean_ctor_get(v___x_1490_, 0);
v_toFunctor_1492_ = lean_ctor_get(v_toApplicative_1491_, 0);
v_toSeq_1493_ = lean_ctor_get(v_toApplicative_1491_, 2);
v_toSeqLeft_1494_ = lean_ctor_get(v_toApplicative_1491_, 3);
v_toSeqRight_1495_ = lean_ctor_get(v_toApplicative_1491_, 4);
v___f_1496_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1497_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1492_, 2);
v___f_1498_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1498_, 0, v_toFunctor_1492_);
v___f_1499_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1499_, 0, v_toFunctor_1492_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 0);
lean_ctor_set(v___x_1488_, 1, v___f_1499_);
lean_ctor_set(v___x_1488_, 0, v___f_1498_);
v___x_1501_ = v___x_1488_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___f_1498_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___f_1499_);
v___x_1501_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_toApplicative_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1544_; 
lean_inc(v_toSeqRight_1495_);
v___f_1502_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1502_, 0, v_toSeqRight_1495_);
lean_inc(v_toSeqLeft_1494_);
v___f_1503_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1503_, 0, v_toSeqLeft_1494_);
lean_inc(v_toSeq_1493_);
v___f_1504_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1504_, 0, v_toSeq_1493_);
v___x_1505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1501_);
lean_ctor_set(v___x_1505_, 1, v___f_1496_);
lean_ctor_set(v___x_1505_, 2, v___f_1504_);
lean_ctor_set(v___x_1505_, 3, v___f_1503_);
lean_ctor_set(v___x_1505_, 4, v___f_1502_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___f_1497_);
v___x_1507_ = l_StateRefT_x27_instMonad___redArg(v___x_1506_);
v_toApplicative_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1507_, 1);
lean_dec(v_unused_1545_);
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1544_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_toApplicative_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1544_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_toFunctor_1512_; lean_object* v_toSeq_1513_; lean_object* v_toSeqLeft_1514_; lean_object* v_toSeqRight_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1542_; 
v_toFunctor_1512_ = lean_ctor_get(v_toApplicative_1508_, 0);
v_toSeq_1513_ = lean_ctor_get(v_toApplicative_1508_, 2);
v_toSeqLeft_1514_ = lean_ctor_get(v_toApplicative_1508_, 3);
v_toSeqRight_1515_ = lean_ctor_get(v_toApplicative_1508_, 4);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_toApplicative_1508_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_toApplicative_1508_, 1);
lean_dec(v_unused_1543_);
v___x_1517_ = v_toApplicative_1508_;
v_isShared_1518_ = v_isSharedCheck_1542_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_toSeqRight_1515_);
lean_inc(v_toSeqLeft_1514_);
lean_inc(v_toSeq_1513_);
lean_inc(v_toFunctor_1512_);
lean_dec(v_toApplicative_1508_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1542_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v_cls_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___f_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___x_1531_; 
v___x_1519_ = lean_box(v_nondep_1469_);
lean_inc(v_toBind_1466_);
lean_inc_ref(v_e_1485_);
v___f_1520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1520_, 0, v_toApplicative_1460_);
lean_closure_set(v___f_1520_, 1, v_e_1485_);
lean_closure_set(v___f_1520_, 2, v_xs_1468_);
lean_closure_set(v___f_1520_, 3, v_h_1486_);
lean_closure_set(v___f_1520_, 4, v___x_1519_);
lean_closure_set(v___f_1520_, 5, v_toBind_1466_);
lean_closure_set(v___f_1520_, 6, v___f_1470_);
v_cls_1521_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1522_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1523_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1512_);
v___f_1524_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1524_, 0, v_toFunctor_1512_);
v___f_1525_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1525_, 0, v_toFunctor_1512_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___f_1524_);
lean_ctor_set(v___x_1526_, 1, v___f_1525_);
v___f_1527_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1527_, 0, v_toSeqRight_1515_);
v___f_1528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1528_, 0, v_toSeqLeft_1514_);
v___f_1529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1529_, 0, v_toSeq_1513_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 4, v___f_1527_);
lean_ctor_set(v___x_1517_, 3, v___f_1528_);
lean_ctor_set(v___x_1517_, 2, v___f_1529_);
lean_ctor_set(v___x_1517_, 1, v___f_1522_);
lean_ctor_set(v___x_1517_, 0, v___x_1526_);
v___x_1531_ = v___x_1517_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___f_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v___f_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v___f_1528_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___f_1527_);
v___x_1531_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v___f_1523_);
lean_ctor_set(v___x_1510_, 0, v___x_1531_);
v___x_1533_ = v___x_1510_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___f_1523_);
v___x_1533_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___f_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___f_1534_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1535_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1537_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1537_, 0, v_cls_1521_);
lean_closure_set(v___f_1537_, 1, v___x_1535_);
lean_closure_set(v___f_1537_, 2, v___f_1534_);
lean_closure_set(v___f_1537_, 3, v_declName_1471_);
lean_closure_set(v___f_1537_, 4, v_val_1472_);
lean_closure_set(v___f_1537_, 5, v_e_1485_);
lean_closure_set(v___f_1537_, 6, v___x_1533_);
lean_closure_set(v___f_1537_, 7, v___x_1536_);
v___x_1538_ = lean_apply_2(v_inst_1473_, lean_box(0), v___f_1537_);
v___x_1539_ = lean_apply_4(v_toBind_1466_, lean_box(0), lean_box(0), v___x_1538_, v___f_1520_);
return v___x_1539_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object* v_toApplicative_1548_, lean_object* v_level_1549_, lean_object* v___x_1550_, lean_object* v_type_1551_, lean_object* v_value_1552_, lean_object* v___x_1553_, lean_object* v_toBind_1554_, lean_object* v___f_1555_, lean_object* v_xs_1556_, lean_object* v_nondep_1557_, lean_object* v___f_1558_, lean_object* v_declName_1559_, lean_object* v_val_1560_, lean_object* v_inst_1561_, lean_object* v_____do__lift_1562_){
_start:
{
uint8_t v___x_13106__boxed_1563_; uint8_t v_nondep_13108__boxed_1564_; lean_object* v_res_1565_; 
v___x_13106__boxed_1563_ = lean_unbox(v___x_1553_);
v_nondep_13108__boxed_1564_ = lean_unbox(v_nondep_1557_);
v_res_1565_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1548_, v_level_1549_, v___x_1550_, v_type_1551_, v_value_1552_, v___x_13106__boxed_1563_, v_toBind_1554_, v___f_1555_, v_xs_1556_, v_nondep_13108__boxed_1564_, v___f_1558_, v_declName_1559_, v_val_1560_, v_inst_1561_, v_____do__lift_1562_);
return v_res_1565_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1576_ = lean_unsigned_to_nat(8u);
v___x_1577_ = lean_unsigned_to_nat(287u);
v___x_1578_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1580_ = l_mkPanicMessageWithDecl(v___x_1579_, v___x_1578_, v___x_1577_, v___x_1576_, v___x_1575_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1581_, lean_object* v_type_1582_, lean_object* v_fst_1583_, lean_object* v___x_1584_, lean_object* v_value_1585_, uint8_t v_nondep_1586_, uint8_t v_fst_1587_, lean_object* v_toApplicative_1588_, lean_object* v___x_1589_, lean_object* v_us_1590_, lean_object* v_snd_1591_, lean_object* v_inst_1592_, lean_object* v_rb_1593_){
_start:
{
lean_object* v_expr_1594_; lean_object* v_exprType_1595_; lean_object* v_exprInit_1596_; lean_object* v_exprResult_1597_; lean_object* v_proof_1598_; uint8_t v_modified_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1650_; 
v_expr_1594_ = lean_ctor_get(v_rb_1593_, 0);
v_exprType_1595_ = lean_ctor_get(v_rb_1593_, 1);
v_exprInit_1596_ = lean_ctor_get(v_rb_1593_, 2);
v_exprResult_1597_ = lean_ctor_get(v_rb_1593_, 3);
v_proof_1598_ = lean_ctor_get(v_rb_1593_, 4);
v_modified_1599_ = lean_ctor_get_uint8(v_rb_1593_, sizeof(void*)*5);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_rb_1593_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1601_ = v_rb_1593_;
v_isShared_1602_ = v_isSharedCheck_1650_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_proof_1598_);
lean_inc(v_exprResult_1597_);
lean_inc(v_exprInit_1596_);
lean_inc(v_exprType_1595_);
lean_inc(v_expr_1594_);
lean_dec(v_rb_1593_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1650_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_expr_has_loose_bvar(v_exprType_1595_, v___x_1603_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v_expr_1607_; lean_object* v_exprType_1608_; lean_object* v___x_1609_; lean_object* v_exprInit_1610_; lean_object* v_exprResult_1611_; 
lean_dec_ref(v_inst_1592_);
v___x_1605_ = 0;
lean_inc_ref_n(v_type_1582_, 3);
lean_inc_n(v_declName_1581_, 3);
v___x_1606_ = l_Lean_mkLambda(v_declName_1581_, v___x_1605_, v_type_1582_, v_expr_1594_);
lean_inc_ref_n(v_fst_1583_, 2);
lean_inc_ref(v___x_1606_);
v_expr_1607_ = l_Lean_Expr_app___override(v___x_1606_, v_fst_1583_);
v_exprType_1608_ = lean_expr_lower_loose_bvars(v_exprType_1595_, v___x_1584_, v___x_1584_);
lean_dec_ref(v_exprType_1595_);
v___x_1609_ = l_Lean_mkLambda(v_declName_1581_, v___x_1605_, v_type_1582_, v_exprInit_1596_);
lean_inc_ref(v_value_1585_);
lean_inc_ref(v___x_1609_);
v_exprInit_1610_ = l_Lean_Expr_app___override(v___x_1609_, v_value_1585_);
v_exprResult_1611_ = l_Lean_Expr_letE___override(v_declName_1581_, v_type_1582_, v_fst_1583_, v_exprResult_1597_, v_nondep_1586_);
if (v_fst_1587_ == 0)
{
lean_dec_ref(v_snd_1591_);
lean_dec_ref(v_fst_1583_);
if (v_modified_1599_ == 0)
{
lean_object* v_toPure_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_proof_1615_; lean_object* v___x_1617_; 
lean_dec_ref(v___x_1609_);
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_proof_1598_);
lean_dec(v_us_1590_);
lean_dec_ref(v_value_1585_);
lean_dec_ref(v_type_1582_);
lean_dec(v_declName_1581_);
v_toPure_1612_ = lean_ctor_get(v_toApplicative_1588_, 1);
lean_inc(v_toPure_1612_);
lean_dec_ref(v_toApplicative_1588_);
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1614_ = l_Lean_mkConst(v___x_1613_, v___x_1589_);
lean_inc_ref(v_expr_1607_);
lean_inc_ref(v_exprType_1608_);
v_proof_1615_ = l_Lean_mkAppB(v___x_1614_, v_exprType_1608_, v_expr_1607_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v_proof_1615_);
lean_ctor_set(v___x_1601_, 3, v_exprResult_1611_);
lean_ctor_set(v___x_1601_, 2, v_exprInit_1610_);
lean_ctor_set(v___x_1601_, 1, v_exprType_1608_);
lean_ctor_set(v___x_1601_, 0, v_expr_1607_);
v___x_1617_ = v___x_1601_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_expr_1607_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_exprType_1608_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_exprInit_1610_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_exprResult_1611_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_proof_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*5, v_modified_1599_);
v___x_1617_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_apply_2(v_toPure_1612_, lean_box(0), v___x_1617_);
return v___x_1618_;
}
}
else
{
lean_object* v_toPure_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_proof_1624_; lean_object* v___x_1626_; 
lean_dec(v___x_1589_);
v_toPure_1620_ = lean_ctor_get(v_toApplicative_1588_, 1);
lean_inc(v_toPure_1620_);
lean_dec_ref(v_toApplicative_1588_);
lean_inc_ref(v_type_1582_);
v___x_1621_ = l_Lean_mkLambda(v_declName_1581_, v___x_1605_, v_type_1582_, v_proof_1598_);
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1623_ = l_Lean_mkConst(v___x_1622_, v_us_1590_);
lean_inc_ref(v_exprType_1608_);
v_proof_1624_ = l_Lean_mkApp6(v___x_1623_, v_type_1582_, v_exprType_1608_, v_value_1585_, v___x_1609_, v___x_1606_, v___x_1621_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v_proof_1624_);
lean_ctor_set(v___x_1601_, 3, v_exprResult_1611_);
lean_ctor_set(v___x_1601_, 2, v_exprInit_1610_);
lean_ctor_set(v___x_1601_, 1, v_exprType_1608_);
lean_ctor_set(v___x_1601_, 0, v_expr_1607_);
v___x_1626_ = v___x_1601_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_expr_1607_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_exprType_1608_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_exprInit_1610_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_exprResult_1611_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_proof_1624_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*5, v_nondep_1586_);
v___x_1627_ = lean_apply_2(v_toPure_1620_, lean_box(0), v___x_1626_);
return v___x_1627_;
}
}
}
else
{
lean_dec(v___x_1589_);
if (v_modified_1599_ == 0)
{
lean_object* v_toPure_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_proof_1632_; lean_object* v___x_1634_; 
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_proof_1598_);
lean_dec(v_declName_1581_);
v_toPure_1629_ = lean_ctor_get(v_toApplicative_1588_, 1);
lean_inc(v_toPure_1629_);
lean_dec_ref(v_toApplicative_1588_);
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1631_ = l_Lean_mkConst(v___x_1630_, v_us_1590_);
lean_inc_ref(v_exprType_1608_);
v_proof_1632_ = l_Lean_mkApp6(v___x_1631_, v_type_1582_, v_exprType_1608_, v_value_1585_, v_fst_1583_, v___x_1609_, v_snd_1591_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v_proof_1632_);
lean_ctor_set(v___x_1601_, 3, v_exprResult_1611_);
lean_ctor_set(v___x_1601_, 2, v_exprInit_1610_);
lean_ctor_set(v___x_1601_, 1, v_exprType_1608_);
lean_ctor_set(v___x_1601_, 0, v_expr_1607_);
v___x_1634_ = v___x_1601_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_expr_1607_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_exprType_1608_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_exprInit_1610_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_exprResult_1611_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_proof_1632_);
v___x_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*5, v_nondep_1586_);
v___x_1635_ = lean_apply_2(v_toPure_1629_, lean_box(0), v___x_1634_);
return v___x_1635_;
}
}
else
{
lean_object* v_toPure_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_proof_1641_; lean_object* v___x_1643_; 
v_toPure_1637_ = lean_ctor_get(v_toApplicative_1588_, 1);
lean_inc(v_toPure_1637_);
lean_dec_ref(v_toApplicative_1588_);
lean_inc_ref(v_type_1582_);
v___x_1638_ = l_Lean_mkLambda(v_declName_1581_, v___x_1605_, v_type_1582_, v_proof_1598_);
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1640_ = l_Lean_mkConst(v___x_1639_, v_us_1590_);
lean_inc_ref(v_exprType_1608_);
v_proof_1641_ = l_Lean_mkApp8(v___x_1640_, v_type_1582_, v_exprType_1608_, v_value_1585_, v_fst_1583_, v___x_1609_, v___x_1606_, v_snd_1591_, v___x_1638_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v_proof_1641_);
lean_ctor_set(v___x_1601_, 3, v_exprResult_1611_);
lean_ctor_set(v___x_1601_, 2, v_exprInit_1610_);
lean_ctor_set(v___x_1601_, 1, v_exprType_1608_);
lean_ctor_set(v___x_1601_, 0, v_expr_1607_);
v___x_1643_ = v___x_1601_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_expr_1607_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_exprType_1608_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_exprInit_1610_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_exprResult_1611_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_proof_1641_);
v___x_1643_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; 
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*5, v_nondep_1586_);
v___x_1644_ = lean_apply_2(v_toPure_1637_, lean_box(0), v___x_1643_);
return v___x_1644_;
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_del_object(v___x_1601_);
lean_dec_ref(v_proof_1598_);
lean_dec_ref(v_exprResult_1597_);
lean_dec_ref(v_exprInit_1596_);
lean_dec_ref(v_exprType_1595_);
lean_dec_ref(v_expr_1594_);
lean_dec_ref(v_snd_1591_);
lean_dec(v_us_1590_);
lean_dec(v___x_1589_);
lean_dec_ref(v_toApplicative_1588_);
lean_dec_ref(v_value_1585_);
lean_dec_ref(v_fst_1583_);
lean_dec_ref(v_type_1582_);
lean_dec(v_declName_1581_);
v___x_1646_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1647_ = l_instInhabitedOfMonad___redArg(v_inst_1592_, v___x_1646_);
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1649_ = l_panic___redArg(v___x_1647_, v___x_1648_);
lean_dec(v___x_1647_);
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1651_, lean_object* v_type_1652_, lean_object* v_fst_1653_, lean_object* v___x_1654_, lean_object* v_value_1655_, lean_object* v_nondep_1656_, lean_object* v_fst_1657_, lean_object* v_toApplicative_1658_, lean_object* v___x_1659_, lean_object* v_us_1660_, lean_object* v_snd_1661_, lean_object* v_inst_1662_, lean_object* v_rb_1663_){
_start:
{
uint8_t v_nondep_13324__boxed_1664_; uint8_t v_fst_13325__boxed_1665_; lean_object* v_res_1666_; 
v_nondep_13324__boxed_1664_ = lean_unbox(v_nondep_1656_);
v_fst_13325__boxed_1665_ = lean_unbox(v_fst_1657_);
v_res_1666_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1651_, v_type_1652_, v_fst_1653_, v___x_1654_, v_value_1655_, v_nondep_13324__boxed_1664_, v_fst_13325__boxed_1665_, v_toApplicative_1658_, v___x_1659_, v_us_1660_, v_snd_1661_, v_inst_1662_, v_rb_1663_);
lean_dec(v___x_1654_);
return v_res_1666_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0));
v___x_1672_ = lean_unsigned_to_nat(34u);
v___x_1673_ = lean_unsigned_to_nat(217u);
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1676_ = l_mkPanicMessageWithDecl(v___x_1675_, v___x_1674_, v___x_1673_, v___x_1672_, v___x_1671_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1677_, lean_object* v_type_1678_, lean_object* v_value_1679_, uint8_t v_nondep_1680_, lean_object* v_toApplicative_1681_, lean_object* v___x_1682_, lean_object* v_us_1683_, lean_object* v_decl_1684_, lean_object* v_x_1685_, lean_object* v_i_1686_, lean_object* v_xs_1687_, lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_info_1692_, lean_object* v_fixed_1693_, lean_object* v_used_1694_, lean_object* v_body_1695_, lean_object* v_toBind_1696_, lean_object* v_withNewLemmas_1697_, lean_object* v_val_x27_1698_, lean_object* v_val_1699_, uint8_t v___x_1700_, lean_object* v_____r_1701_){
_start:
{
uint8_t v___y_1703_; lean_object* v___y_1704_; uint8_t v___y_1720_; uint8_t v___x_1722_; 
v___x_1722_ = lean_expr_eqv(v_val_1699_, v_val_x27_1698_);
if (v___x_1722_ == 0)
{
v___y_1720_ = v_nondep_1680_;
goto v___jp_1719_;
}
else
{
v___y_1720_ = v___x_1700_;
goto v___jp_1719_;
}
v___jp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1705_ = lean_box(v_nondep_1680_);
v___x_1706_ = lean_box(v___y_1703_);
v___f_1707_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1707_, 0, v_declName_1677_);
lean_closure_set(v___f_1707_, 1, v_type_1678_);
lean_closure_set(v___f_1707_, 2, v___y_1704_);
lean_closure_set(v___f_1707_, 3, v_value_1679_);
lean_closure_set(v___f_1707_, 4, v___x_1705_);
lean_closure_set(v___f_1707_, 5, v_toApplicative_1681_);
lean_closure_set(v___f_1707_, 6, v___x_1682_);
lean_closure_set(v___f_1707_, 7, v___x_1706_);
lean_closure_set(v___f_1707_, 8, v_us_1683_);
v___x_1708_ = lean_box(0);
v___x_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_decl_1684_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_mk_empty_array_with_capacity(v___x_1710_);
lean_inc_ref(v_x_1685_);
v___x_1712_ = lean_array_push(v___x_1711_, v_x_1685_);
v___x_1713_ = lean_nat_add(v_i_1686_, v___x_1710_);
v___x_1714_ = lean_array_push(v_xs_1687_, v_x_1685_);
lean_inc_ref(v_inst_1690_);
lean_inc_ref(v_inst_1688_);
v___x_1715_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1688_, v_inst_1689_, v_inst_1690_, v_inst_1691_, v_info_1692_, v_fixed_1693_, v_used_1694_, v_body_1695_, v___x_1713_, v___x_1714_);
v___x_1716_ = lean_apply_4(v_toBind_1696_, lean_box(0), lean_box(0), v___x_1715_, v___f_1707_);
v___x_1717_ = lean_apply_3(v_withNewLemmas_1697_, lean_box(0), v___x_1712_, v___x_1716_);
v___x_1718_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1690_, v_inst_1688_, v___x_1709_, v___x_1717_);
return v___x_1718_;
}
v___jp_1719_:
{
if (v___y_1720_ == 0)
{
lean_inc_ref(v_value_1679_);
v___y_1703_ = v___y_1720_;
v___y_1704_ = v_value_1679_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_expr_abstract(v_val_x27_1698_, v_xs_1687_);
v___y_1703_ = v___y_1720_;
v___y_1704_ = v___x_1721_;
goto v___jp_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1723_ = _args[0];
lean_object* v_type_1724_ = _args[1];
lean_object* v_value_1725_ = _args[2];
lean_object* v_nondep_1726_ = _args[3];
lean_object* v_toApplicative_1727_ = _args[4];
lean_object* v___x_1728_ = _args[5];
lean_object* v_us_1729_ = _args[6];
lean_object* v_decl_1730_ = _args[7];
lean_object* v_x_1731_ = _args[8];
lean_object* v_i_1732_ = _args[9];
lean_object* v_xs_1733_ = _args[10];
lean_object* v_inst_1734_ = _args[11];
lean_object* v_inst_1735_ = _args[12];
lean_object* v_inst_1736_ = _args[13];
lean_object* v_inst_1737_ = _args[14];
lean_object* v_info_1738_ = _args[15];
lean_object* v_fixed_1739_ = _args[16];
lean_object* v_used_1740_ = _args[17];
lean_object* v_body_1741_ = _args[18];
lean_object* v_toBind_1742_ = _args[19];
lean_object* v_withNewLemmas_1743_ = _args[20];
lean_object* v_val_x27_1744_ = _args[21];
lean_object* v_val_1745_ = _args[22];
lean_object* v___x_1746_ = _args[23];
lean_object* v_____r_1747_ = _args[24];
_start:
{
uint8_t v_nondep_13580__boxed_1748_; uint8_t v___x_13587__boxed_1749_; lean_object* v_res_1750_; 
v_nondep_13580__boxed_1748_ = lean_unbox(v_nondep_1726_);
v___x_13587__boxed_1749_ = lean_unbox(v___x_1746_);
v_res_1750_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1723_, v_type_1724_, v_value_1725_, v_nondep_13580__boxed_1748_, v_toApplicative_1727_, v___x_1728_, v_us_1729_, v_decl_1730_, v_x_1731_, v_i_1732_, v_xs_1733_, v_inst_1734_, v_inst_1735_, v_inst_1736_, v_inst_1737_, v_info_1738_, v_fixed_1739_, v_used_1740_, v_body_1741_, v_toBind_1742_, v_withNewLemmas_1743_, v_val_x27_1744_, v_val_1745_, v___x_13587__boxed_1749_, v_____r_1747_);
lean_dec_ref(v_val_1745_);
lean_dec_ref(v_val_x27_1744_);
lean_dec(v_i_1732_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1751_, lean_object* v_type_1752_, lean_object* v_value_1753_, uint8_t v_nondep_1754_, lean_object* v_toApplicative_1755_, lean_object* v___x_1756_, lean_object* v_us_1757_, lean_object* v_decl_1758_, lean_object* v_x_1759_, lean_object* v_i_1760_, lean_object* v_xs_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_info_1766_, lean_object* v_fixed_1767_, lean_object* v_used_1768_, lean_object* v_body_1769_, lean_object* v_toBind_1770_, lean_object* v_withNewLemmas_1771_, lean_object* v_val_1772_, uint8_t v___x_1773_, lean_object* v_val_x27_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v_toApplicative_1776_; lean_object* v_toFunctor_1777_; lean_object* v_toSeq_1778_; lean_object* v_toSeqLeft_1779_; lean_object* v_toSeqRight_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___f_1783_; lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___f_1786_; lean_object* v___f_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_toApplicative_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1829_; 
v___x_1775_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1776_ = lean_ctor_get(v___x_1775_, 0);
v_toFunctor_1777_ = lean_ctor_get(v_toApplicative_1776_, 0);
v_toSeq_1778_ = lean_ctor_get(v_toApplicative_1776_, 2);
v_toSeqLeft_1779_ = lean_ctor_get(v_toApplicative_1776_, 3);
v_toSeqRight_1780_ = lean_ctor_get(v_toApplicative_1776_, 4);
v___f_1781_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1782_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1777_, 2);
v___f_1783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1783_, 0, v_toFunctor_1777_);
v___f_1784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1784_, 0, v_toFunctor_1777_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___f_1783_);
lean_ctor_set(v___x_1785_, 1, v___f_1784_);
lean_inc(v_toSeqRight_1780_);
v___f_1786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1786_, 0, v_toSeqRight_1780_);
lean_inc(v_toSeqLeft_1779_);
v___f_1787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1787_, 0, v_toSeqLeft_1779_);
lean_inc(v_toSeq_1778_);
v___f_1788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1788_, 0, v_toSeq_1778_);
v___x_1789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1785_);
lean_ctor_set(v___x_1789_, 1, v___f_1781_);
lean_ctor_set(v___x_1789_, 2, v___f_1788_);
lean_ctor_set(v___x_1789_, 3, v___f_1787_);
lean_ctor_set(v___x_1789_, 4, v___f_1786_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___f_1782_);
v___x_1791_ = l_StateRefT_x27_instMonad___redArg(v___x_1790_);
v_toApplicative_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1791_, 1);
lean_dec(v_unused_1830_);
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1829_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_toApplicative_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1829_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_toFunctor_1796_; lean_object* v_toSeq_1797_; lean_object* v_toSeqLeft_1798_; lean_object* v_toSeqRight_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1827_; 
v_toFunctor_1796_ = lean_ctor_get(v_toApplicative_1792_, 0);
v_toSeq_1797_ = lean_ctor_get(v_toApplicative_1792_, 2);
v_toSeqLeft_1798_ = lean_ctor_get(v_toApplicative_1792_, 3);
v_toSeqRight_1799_ = lean_ctor_get(v_toApplicative_1792_, 4);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_toApplicative_1792_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_toApplicative_1792_, 1);
lean_dec(v_unused_1828_);
v___x_1801_ = v_toApplicative_1792_;
v_isShared_1802_ = v_isSharedCheck_1827_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_toSeqRight_1799_);
lean_inc(v_toSeqLeft_1798_);
lean_inc(v_toSeq_1797_);
lean_inc(v_toFunctor_1796_);
lean_dec(v_toApplicative_1792_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1827_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___f_1805_; lean_object* v_cls_1806_; lean_object* v___f_1807_; lean_object* v___f_1808_; lean_object* v___f_1809_; lean_object* v___f_1810_; lean_object* v___x_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___x_1816_; 
v___x_1803_ = lean_box(v_nondep_1754_);
v___x_1804_ = lean_box(v___x_1773_);
lean_inc_ref(v_val_1772_);
lean_inc_ref(v_val_x27_1774_);
lean_inc(v_toBind_1770_);
lean_inc(v_inst_1763_);
lean_inc(v_declName_1751_);
v___f_1805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 25, 24);
lean_closure_set(v___f_1805_, 0, v_declName_1751_);
lean_closure_set(v___f_1805_, 1, v_type_1752_);
lean_closure_set(v___f_1805_, 2, v_value_1753_);
lean_closure_set(v___f_1805_, 3, v___x_1803_);
lean_closure_set(v___f_1805_, 4, v_toApplicative_1755_);
lean_closure_set(v___f_1805_, 5, v___x_1756_);
lean_closure_set(v___f_1805_, 6, v_us_1757_);
lean_closure_set(v___f_1805_, 7, v_decl_1758_);
lean_closure_set(v___f_1805_, 8, v_x_1759_);
lean_closure_set(v___f_1805_, 9, v_i_1760_);
lean_closure_set(v___f_1805_, 10, v_xs_1761_);
lean_closure_set(v___f_1805_, 11, v_inst_1762_);
lean_closure_set(v___f_1805_, 12, v_inst_1763_);
lean_closure_set(v___f_1805_, 13, v_inst_1764_);
lean_closure_set(v___f_1805_, 14, v_inst_1765_);
lean_closure_set(v___f_1805_, 15, v_info_1766_);
lean_closure_set(v___f_1805_, 16, v_fixed_1767_);
lean_closure_set(v___f_1805_, 17, v_used_1768_);
lean_closure_set(v___f_1805_, 18, v_body_1769_);
lean_closure_set(v___f_1805_, 19, v_toBind_1770_);
lean_closure_set(v___f_1805_, 20, v_withNewLemmas_1771_);
lean_closure_set(v___f_1805_, 21, v_val_x27_1774_);
lean_closure_set(v___f_1805_, 22, v_val_1772_);
lean_closure_set(v___f_1805_, 23, v___x_1804_);
v_cls_1806_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1807_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1808_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1796_);
v___f_1809_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1809_, 0, v_toFunctor_1796_);
v___f_1810_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1810_, 0, v_toFunctor_1796_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___f_1809_);
lean_ctor_set(v___x_1811_, 1, v___f_1810_);
v___f_1812_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1812_, 0, v_toSeqRight_1799_);
v___f_1813_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1813_, 0, v_toSeqLeft_1798_);
v___f_1814_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1814_, 0, v_toSeq_1797_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 4, v___f_1812_);
lean_ctor_set(v___x_1801_, 3, v___f_1813_);
lean_ctor_set(v___x_1801_, 2, v___f_1814_);
lean_ctor_set(v___x_1801_, 1, v___f_1807_);
lean_ctor_set(v___x_1801_, 0, v___x_1811_);
v___x_1816_ = v___x_1801_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___f_1807_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v___f_1814_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v___f_1813_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v___f_1812_);
v___x_1816_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___f_1808_);
lean_ctor_set(v___x_1794_, 0, v___x_1816_);
v___x_1818_ = v___x_1794_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___f_1808_);
v___x_1818_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___f_1819_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1821_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1822_, 0, v_cls_1806_);
lean_closure_set(v___f_1822_, 1, v___x_1820_);
lean_closure_set(v___f_1822_, 2, v___f_1819_);
lean_closure_set(v___f_1822_, 3, v_declName_1751_);
lean_closure_set(v___f_1822_, 4, v_val_1772_);
lean_closure_set(v___f_1822_, 5, v_val_x27_1774_);
lean_closure_set(v___f_1822_, 6, v___x_1818_);
lean_closure_set(v___f_1822_, 7, v___x_1821_);
v___x_1823_ = lean_apply_2(v_inst_1763_, lean_box(0), v___f_1822_);
v___x_1824_ = lean_apply_4(v_toBind_1770_, lean_box(0), lean_box(0), v___x_1823_, v___f_1805_);
return v___x_1824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1831_ = _args[0];
lean_object* v_type_1832_ = _args[1];
lean_object* v_value_1833_ = _args[2];
lean_object* v_nondep_1834_ = _args[3];
lean_object* v_toApplicative_1835_ = _args[4];
lean_object* v___x_1836_ = _args[5];
lean_object* v_us_1837_ = _args[6];
lean_object* v_decl_1838_ = _args[7];
lean_object* v_x_1839_ = _args[8];
lean_object* v_i_1840_ = _args[9];
lean_object* v_xs_1841_ = _args[10];
lean_object* v_inst_1842_ = _args[11];
lean_object* v_inst_1843_ = _args[12];
lean_object* v_inst_1844_ = _args[13];
lean_object* v_inst_1845_ = _args[14];
lean_object* v_info_1846_ = _args[15];
lean_object* v_fixed_1847_ = _args[16];
lean_object* v_used_1848_ = _args[17];
lean_object* v_body_1849_ = _args[18];
lean_object* v_toBind_1850_ = _args[19];
lean_object* v_withNewLemmas_1851_ = _args[20];
lean_object* v_val_1852_ = _args[21];
lean_object* v___x_1853_ = _args[22];
lean_object* v_val_x27_1854_ = _args[23];
_start:
{
uint8_t v_nondep_13611__boxed_1855_; uint8_t v___x_13618__boxed_1856_; lean_object* v_res_1857_; 
v_nondep_13611__boxed_1855_ = lean_unbox(v_nondep_1834_);
v___x_13618__boxed_1856_ = lean_unbox(v___x_1853_);
v_res_1857_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1831_, v_type_1832_, v_value_1833_, v_nondep_13611__boxed_1855_, v_toApplicative_1835_, v___x_1836_, v_us_1837_, v_decl_1838_, v_x_1839_, v_i_1840_, v_xs_1841_, v_inst_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_info_1846_, v_fixed_1847_, v_used_1848_, v_body_1849_, v_toBind_1850_, v_withNewLemmas_1851_, v_val_1852_, v___x_13618__boxed_1856_, v_val_x27_1854_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1858_, lean_object* v_declName_1859_, lean_object* v_type_1860_, lean_object* v_value_1861_, uint8_t v_nondep_1862_, lean_object* v_toApplicative_1863_, lean_object* v___x_1864_, lean_object* v_us_1865_, lean_object* v_inst_1866_, lean_object* v_x_1867_, lean_object* v_i_1868_, lean_object* v_xs_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_info_1873_, lean_object* v_fixed_1874_, lean_object* v_used_1875_, lean_object* v_body_1876_, lean_object* v_toBind_1877_, lean_object* v_withNewLemmas_1878_, lean_object* v_____x_1879_){
_start:
{
lean_object* v_snd_1880_; lean_object* v_fst_1881_; lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1902_; 
v_snd_1880_ = lean_ctor_get(v_____x_1879_, 1);
lean_inc(v_snd_1880_);
v_fst_1881_ = lean_ctor_get(v_____x_1879_, 0);
lean_inc(v_fst_1881_);
lean_dec_ref(v_____x_1879_);
v_fst_1882_ = lean_ctor_get(v_snd_1880_, 0);
v_snd_1883_ = lean_ctor_get(v_snd_1880_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_snd_1880_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1885_ = v_snd_1880_;
v_isShared_1886_ = v_isSharedCheck_1902_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_inc(v_fst_1882_);
lean_dec(v_snd_1880_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1902_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_box(0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 1);
lean_ctor_set(v___x_1885_, 1, v___x_1887_);
lean_ctor_set(v___x_1885_, 0, v_decl_1858_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_decl_1858_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_box(v_nondep_1862_);
lean_inc_ref_n(v_inst_1866_, 2);
v___f_1892_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1892_, 0, v_declName_1859_);
lean_closure_set(v___f_1892_, 1, v_type_1860_);
lean_closure_set(v___f_1892_, 2, v_fst_1881_);
lean_closure_set(v___f_1892_, 3, v___x_1890_);
lean_closure_set(v___f_1892_, 4, v_value_1861_);
lean_closure_set(v___f_1892_, 5, v___x_1891_);
lean_closure_set(v___f_1892_, 6, v_fst_1882_);
lean_closure_set(v___f_1892_, 7, v_toApplicative_1863_);
lean_closure_set(v___f_1892_, 8, v___x_1864_);
lean_closure_set(v___f_1892_, 9, v_us_1865_);
lean_closure_set(v___f_1892_, 10, v_snd_1883_);
lean_closure_set(v___f_1892_, 11, v_inst_1866_);
v___x_1893_ = lean_mk_empty_array_with_capacity(v___x_1890_);
lean_inc_ref(v_x_1867_);
v___x_1894_ = lean_array_push(v___x_1893_, v_x_1867_);
v___x_1895_ = lean_nat_add(v_i_1868_, v___x_1890_);
v___x_1896_ = lean_array_push(v_xs_1869_, v_x_1867_);
lean_inc_ref(v_inst_1871_);
v___x_1897_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1866_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_info_1873_, v_fixed_1874_, v_used_1875_, v_body_1876_, v___x_1895_, v___x_1896_);
v___x_1898_ = lean_apply_4(v_toBind_1877_, lean_box(0), lean_box(0), v___x_1897_, v___f_1892_);
v___x_1899_ = lean_apply_3(v_withNewLemmas_1878_, lean_box(0), v___x_1894_, v___x_1898_);
v___x_1900_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1871_, v_inst_1866_, v___x_1889_, v___x_1899_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1903_ = _args[0];
lean_object* v_declName_1904_ = _args[1];
lean_object* v_type_1905_ = _args[2];
lean_object* v_value_1906_ = _args[3];
lean_object* v_nondep_1907_ = _args[4];
lean_object* v_toApplicative_1908_ = _args[5];
lean_object* v___x_1909_ = _args[6];
lean_object* v_us_1910_ = _args[7];
lean_object* v_inst_1911_ = _args[8];
lean_object* v_x_1912_ = _args[9];
lean_object* v_i_1913_ = _args[10];
lean_object* v_xs_1914_ = _args[11];
lean_object* v_inst_1915_ = _args[12];
lean_object* v_inst_1916_ = _args[13];
lean_object* v_inst_1917_ = _args[14];
lean_object* v_info_1918_ = _args[15];
lean_object* v_fixed_1919_ = _args[16];
lean_object* v_used_1920_ = _args[17];
lean_object* v_body_1921_ = _args[18];
lean_object* v_toBind_1922_ = _args[19];
lean_object* v_withNewLemmas_1923_ = _args[20];
lean_object* v_____x_1924_ = _args[21];
_start:
{
uint8_t v_nondep_13553__boxed_1925_; lean_object* v_res_1926_; 
v_nondep_13553__boxed_1925_ = lean_unbox(v_nondep_1907_);
v_res_1926_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1903_, v_declName_1904_, v_type_1905_, v_value_1906_, v_nondep_13553__boxed_1925_, v_toApplicative_1908_, v___x_1909_, v_us_1910_, v_inst_1911_, v_x_1912_, v_i_1913_, v_xs_1914_, v_inst_1915_, v_inst_1916_, v_inst_1917_, v_info_1918_, v_fixed_1919_, v_used_1920_, v_body_1921_, v_toBind_1922_, v_withNewLemmas_1923_, v_____x_1924_);
lean_dec(v_i_1913_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1927_ = _args[0];
lean_object* v_declName_1928_ = _args[1];
lean_object* v_type_1929_ = _args[2];
lean_object* v_value_1930_ = _args[3];
lean_object* v_us_1931_ = _args[4];
lean_object* v___x_1932_ = _args[5];
lean_object* v_toApplicative_1933_ = _args[6];
lean_object* v_nondep_1934_ = _args[7];
lean_object* v_i_1935_ = _args[8];
lean_object* v_xs_1936_ = _args[9];
lean_object* v_inst_1937_ = _args[10];
lean_object* v_inst_1938_ = _args[11];
lean_object* v_inst_1939_ = _args[12];
lean_object* v_inst_1940_ = _args[13];
lean_object* v_info_1941_ = _args[14];
lean_object* v_fixed_1942_ = _args[15];
lean_object* v_used_1943_ = _args[16];
lean_object* v_body_1944_ = _args[17];
lean_object* v_toBind_1945_ = _args[18];
lean_object* v_____r_1946_ = _args[19];
_start:
{
uint8_t v_nondep_13536__boxed_1947_; lean_object* v_res_1948_; 
v_nondep_13536__boxed_1947_ = lean_unbox(v_nondep_1934_);
v_res_1948_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1927_, v_declName_1928_, v_type_1929_, v_value_1930_, v_us_1931_, v___x_1932_, v_toApplicative_1933_, v_nondep_13536__boxed_1947_, v_i_1935_, v_xs_1936_, v_inst_1937_, v_inst_1938_, v_inst_1939_, v_inst_1940_, v_info_1941_, v_fixed_1942_, v_used_1943_, v_body_1944_, v_toBind_1945_, v_____r_1946_);
lean_dec(v_i_1935_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_info_1953_, lean_object* v_fixed_1954_, lean_object* v_used_1955_, lean_object* v_e_1956_, lean_object* v_i_1957_, lean_object* v_xs_1958_){
_start:
{
lean_object* v_haveInfo_1964_; lean_object* v_body_1965_; lean_object* v_bodyType_1966_; lean_object* v_level_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_haveInfo_1964_ = lean_ctor_get(v_info_1953_, 0);
v_body_1965_ = lean_ctor_get(v_info_1953_, 3);
v_bodyType_1966_ = lean_ctor_get(v_info_1953_, 4);
v_level_1967_ = lean_ctor_get(v_info_1953_, 5);
v___x_1968_ = lean_array_get_size(v_haveInfo_1964_);
v___x_1969_ = lean_nat_dec_lt(v_i_1957_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v_toApplicative_1970_; lean_object* v_toBind_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2032_; 
lean_inc(v_level_1967_);
lean_inc_ref(v_bodyType_1966_);
lean_inc_ref(v_body_1965_);
lean_dec(v_i_1957_);
lean_dec_ref(v_used_1955_);
lean_dec_ref(v_fixed_1954_);
lean_dec_ref(v_info_1953_);
lean_dec_ref(v_inst_1951_);
v_toApplicative_1970_ = lean_ctor_get(v_inst_1949_, 0);
v_toBind_1971_ = lean_ctor_get(v_inst_1949_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_inst_1949_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1973_ = v_inst_1949_;
v_isShared_1974_ = v_isSharedCheck_2032_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_toBind_1971_);
lean_inc(v_toApplicative_1970_);
lean_dec(v_inst_1949_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2032_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v_toApplicative_1976_; lean_object* v_toFunctor_1977_; lean_object* v_toSeq_1978_; lean_object* v_toSeqLeft_1979_; lean_object* v_toSeqRight_1980_; lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1975_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1976_ = lean_ctor_get(v___x_1975_, 0);
v_toFunctor_1977_ = lean_ctor_get(v_toApplicative_1976_, 0);
v_toSeq_1978_ = lean_ctor_get(v_toApplicative_1976_, 2);
v_toSeqLeft_1979_ = lean_ctor_get(v_toApplicative_1976_, 3);
v_toSeqRight_1980_ = lean_ctor_get(v_toApplicative_1976_, 4);
v___f_1981_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1982_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1977_, 2);
v___f_1983_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1983_, 0, v_toFunctor_1977_);
v___f_1984_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1984_, 0, v_toFunctor_1977_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___f_1983_);
lean_ctor_set(v___x_1985_, 1, v___f_1984_);
lean_inc(v_toSeqRight_1980_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toSeqRight_1980_);
lean_inc(v_toSeqLeft_1979_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toSeqLeft_1979_);
lean_inc(v_toSeq_1978_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toSeq_1978_);
v___x_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1985_);
lean_ctor_set(v___x_1989_, 1, v___f_1981_);
lean_ctor_set(v___x_1989_, 2, v___f_1988_);
lean_ctor_set(v___x_1989_, 3, v___f_1987_);
lean_ctor_set(v___x_1989_, 4, v___f_1986_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v___f_1982_);
lean_ctor_set(v___x_1973_, 0, v___x_1989_);
v___x_1991_ = v___x_1973_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___f_1982_);
v___x_1991_ = v_reuseFailAlloc_2031_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v_toApplicative_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2029_; 
v___x_1992_ = l_StateRefT_x27_instMonad___redArg(v___x_1991_);
v_toApplicative_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_1992_, 1);
lean_dec(v_unused_2030_);
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2029_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_toApplicative_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2029_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_toFunctor_1997_; lean_object* v_toSeq_1998_; lean_object* v_toSeqLeft_1999_; lean_object* v_toSeqRight_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2027_; 
v_toFunctor_1997_ = lean_ctor_get(v_toApplicative_1993_, 0);
v_toSeq_1998_ = lean_ctor_get(v_toApplicative_1993_, 2);
v_toSeqLeft_1999_ = lean_ctor_get(v_toApplicative_1993_, 3);
v_toSeqRight_2000_ = lean_ctor_get(v_toApplicative_1993_, 4);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_toApplicative_1993_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_toApplicative_1993_, 1);
lean_dec(v_unused_2028_);
v___x_2002_ = v_toApplicative_1993_;
v_isShared_2003_ = v_isSharedCheck_2027_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_toSeqRight_2000_);
lean_inc(v_toSeqLeft_1999_);
lean_inc(v_toSeq_1998_);
lean_inc(v_toFunctor_1997_);
lean_dec(v_toApplicative_1993_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2027_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v_cls_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___f_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___x_2016_; 
v___x_2004_ = lean_box(v___x_1969_);
lean_inc(v_toBind_1971_);
lean_inc_ref(v_body_1965_);
v___f_2005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_2005_, 0, v_inst_1952_);
lean_closure_set(v___f_2005_, 1, v_bodyType_1966_);
lean_closure_set(v___f_2005_, 2, v_xs_1958_);
lean_closure_set(v___f_2005_, 3, v_toApplicative_1970_);
lean_closure_set(v___f_2005_, 4, v_level_1967_);
lean_closure_set(v___f_2005_, 5, v_e_1956_);
lean_closure_set(v___f_2005_, 6, v___x_2004_);
lean_closure_set(v___f_2005_, 7, v_body_1965_);
lean_closure_set(v___f_2005_, 8, v_toBind_1971_);
v_cls_2006_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_2007_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_2008_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1997_);
v___f_2009_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2009_, 0, v_toFunctor_1997_);
v___f_2010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2010_, 0, v_toFunctor_1997_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___f_2009_);
lean_ctor_set(v___x_2011_, 1, v___f_2010_);
v___f_2012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2012_, 0, v_toSeqRight_2000_);
v___f_2013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2013_, 0, v_toSeqLeft_1999_);
v___f_2014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2014_, 0, v_toSeq_1998_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v___f_2012_);
lean_ctor_set(v___x_2002_, 3, v___f_2013_);
lean_ctor_set(v___x_2002_, 2, v___f_2014_);
lean_ctor_set(v___x_2002_, 1, v___f_2007_);
lean_ctor_set(v___x_2002_, 0, v___x_2011_);
v___x_2016_ = v___x_2002_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___f_2007_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v___f_2014_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v___f_2013_);
lean_ctor_set(v_reuseFailAlloc_2026_, 4, v___f_2012_);
v___x_2016_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___f_2008_);
lean_ctor_set(v___x_1995_, 0, v___x_2016_);
v___x_2018_ = v___x_1995_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___f_2008_);
v___x_2018_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___f_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___f_2019_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_2021_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_2022_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_2022_, 0, v_cls_2006_);
lean_closure_set(v___f_2022_, 1, v___x_2020_);
lean_closure_set(v___f_2022_, 2, v___f_2019_);
lean_closure_set(v___f_2022_, 3, v_body_1965_);
lean_closure_set(v___f_2022_, 4, v___x_2018_);
lean_closure_set(v___f_2022_, 5, v___x_2021_);
v___x_2023_ = lean_apply_2(v_inst_1950_, lean_box(0), v___f_2022_);
v___x_2024_ = lean_apply_4(v_toBind_1971_, lean_box(0), lean_box(0), v___x_2023_, v___f_2005_);
return v___x_2024_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_e_1956_) == 8)
{
uint8_t v_nondep_2033_; 
v_nondep_2033_ = lean_ctor_get_uint8(v_e_1956_, sizeof(void*)*4 + 8);
if (v_nondep_2033_ == 1)
{
lean_object* v_declName_2034_; lean_object* v_type_2035_; lean_object* v_value_2036_; lean_object* v_body_2037_; lean_object* v_hinfo_2038_; lean_object* v_decl_2039_; lean_object* v_level_2040_; lean_object* v_x_2041_; lean_object* v_val_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v_us_2045_; uint8_t v___y_2047_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_declName_2034_ = lean_ctor_get(v_e_1956_, 0);
lean_inc(v_declName_2034_);
v_type_2035_ = lean_ctor_get(v_e_1956_, 1);
lean_inc_ref(v_type_2035_);
v_value_2036_ = lean_ctor_get(v_e_1956_, 2);
lean_inc_ref(v_value_2036_);
v_body_2037_ = lean_ctor_get(v_e_1956_, 3);
lean_inc_ref(v_body_2037_);
lean_dec_ref_known(v_e_1956_, 4);
v_hinfo_2038_ = lean_array_fget_borrowed(v_haveInfo_1964_, v_i_1957_);
v_decl_2039_ = lean_ctor_get(v_hinfo_2038_, 2);
v_level_2040_ = lean_ctor_get(v_hinfo_2038_, 3);
lean_inc_ref(v_decl_2039_);
v_x_2041_ = l_Lean_LocalDecl_toExpr(v_decl_2039_);
v_val_2042_ = l_Lean_LocalDecl_value(v_decl_2039_, v_nondep_2033_);
v___x_2043_ = lean_box(0);
lean_inc(v_level_1967_);
v___x_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_level_1967_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_inc_ref(v___x_2044_);
lean_inc(v_level_2040_);
v_us_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_2045_, 0, v_level_2040_);
lean_ctor_set(v_us_2045_, 1, v___x_2044_);
v___x_2074_ = lean_array_get_size(v_used_1955_);
v___x_2075_ = lean_nat_dec_lt(v_i_1957_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_inc_ref(v_decl_2039_);
goto v___jp_2057_;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_array_fget_borrowed(v_used_1955_, v_i_1957_);
v___x_2077_ = lean_unbox(v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v_toApplicative_2078_; lean_object* v_toBind_2079_; lean_object* v___x_2080_; lean_object* v_toApplicative_2081_; lean_object* v_toFunctor_2082_; lean_object* v_toSeq_2083_; lean_object* v_toSeqLeft_2084_; lean_object* v_toSeqRight_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v_toApplicative_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_x_2041_);
v_toApplicative_2078_ = lean_ctor_get(v_inst_1949_, 0);
lean_inc_ref(v_toApplicative_2078_);
v_toBind_2079_ = lean_ctor_get(v_inst_1949_, 1);
lean_inc(v_toBind_2079_);
v___x_2080_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_2081_ = lean_ctor_get(v___x_2080_, 0);
v_toFunctor_2082_ = lean_ctor_get(v_toApplicative_2081_, 0);
v_toSeq_2083_ = lean_ctor_get(v_toApplicative_2081_, 2);
v_toSeqLeft_2084_ = lean_ctor_get(v_toApplicative_2081_, 3);
v_toSeqRight_2085_ = lean_ctor_get(v_toApplicative_2081_, 4);
v___f_2086_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_2087_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_2082_, 2);
v___f_2088_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2088_, 0, v_toFunctor_2082_);
v___f_2089_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2089_, 0, v_toFunctor_2082_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___f_2088_);
lean_ctor_set(v___x_2090_, 1, v___f_2089_);
lean_inc(v_toSeqRight_2085_);
v___f_2091_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2091_, 0, v_toSeqRight_2085_);
lean_inc(v_toSeqLeft_2084_);
v___f_2092_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2092_, 0, v_toSeqLeft_2084_);
lean_inc(v_toSeq_2083_);
v___f_2093_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2093_, 0, v_toSeq_2083_);
v___x_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2090_);
lean_ctor_set(v___x_2094_, 1, v___f_2086_);
lean_ctor_set(v___x_2094_, 2, v___f_2093_);
lean_ctor_set(v___x_2094_, 3, v___f_2092_);
lean_ctor_set(v___x_2094_, 4, v___f_2091_);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___f_2087_);
v___x_2096_ = l_StateRefT_x27_instMonad___redArg(v___x_2095_);
v_toApplicative_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2096_, 1);
lean_dec(v_unused_2134_);
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2133_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_toApplicative_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2133_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_toFunctor_2101_; lean_object* v_toSeq_2102_; lean_object* v_toSeqLeft_2103_; lean_object* v_toSeqRight_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2131_; 
v_toFunctor_2101_ = lean_ctor_get(v_toApplicative_2097_, 0);
v_toSeq_2102_ = lean_ctor_get(v_toApplicative_2097_, 2);
v_toSeqLeft_2103_ = lean_ctor_get(v_toApplicative_2097_, 3);
v_toSeqRight_2104_ = lean_ctor_get(v_toApplicative_2097_, 4);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_toApplicative_2097_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v_toApplicative_2097_, 1);
lean_dec(v_unused_2132_);
v___x_2106_ = v_toApplicative_2097_;
v_isShared_2107_ = v_isSharedCheck_2131_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_toSeqRight_2104_);
lean_inc(v_toSeqLeft_2103_);
lean_inc(v_toSeq_2102_);
lean_inc(v_toFunctor_2101_);
lean_dec(v_toApplicative_2097_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2131_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___f_2109_; lean_object* v_cls_2110_; lean_object* v___f_2111_; lean_object* v___f_2112_; lean_object* v___f_2113_; lean_object* v___f_2114_; lean_object* v___x_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; lean_object* v___x_2120_; 
v___x_2108_ = lean_box(v_nondep_2033_);
lean_inc(v_toBind_2079_);
lean_inc(v_inst_1950_);
lean_inc(v_declName_2034_);
v___f_2109_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2109_, 0, v___x_2043_);
lean_closure_set(v___f_2109_, 1, v_declName_2034_);
lean_closure_set(v___f_2109_, 2, v_type_2035_);
lean_closure_set(v___f_2109_, 3, v_value_2036_);
lean_closure_set(v___f_2109_, 4, v_us_2045_);
lean_closure_set(v___f_2109_, 5, v___x_2044_);
lean_closure_set(v___f_2109_, 6, v_toApplicative_2078_);
lean_closure_set(v___f_2109_, 7, v___x_2108_);
lean_closure_set(v___f_2109_, 8, v_i_1957_);
lean_closure_set(v___f_2109_, 9, v_xs_1958_);
lean_closure_set(v___f_2109_, 10, v_inst_1949_);
lean_closure_set(v___f_2109_, 11, v_inst_1950_);
lean_closure_set(v___f_2109_, 12, v_inst_1951_);
lean_closure_set(v___f_2109_, 13, v_inst_1952_);
lean_closure_set(v___f_2109_, 14, v_info_1953_);
lean_closure_set(v___f_2109_, 15, v_fixed_1954_);
lean_closure_set(v___f_2109_, 16, v_used_1955_);
lean_closure_set(v___f_2109_, 17, v_body_2037_);
lean_closure_set(v___f_2109_, 18, v_toBind_2079_);
v_cls_2110_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_2111_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_2112_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_2101_);
v___f_2113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2113_, 0, v_toFunctor_2101_);
v___f_2114_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2114_, 0, v_toFunctor_2101_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___f_2113_);
lean_ctor_set(v___x_2115_, 1, v___f_2114_);
v___f_2116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2116_, 0, v_toSeqRight_2104_);
v___f_2117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2117_, 0, v_toSeqLeft_2103_);
v___f_2118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2118_, 0, v_toSeq_2102_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 4, v___f_2116_);
lean_ctor_set(v___x_2106_, 3, v___f_2117_);
lean_ctor_set(v___x_2106_, 2, v___f_2118_);
lean_ctor_set(v___x_2106_, 1, v___f_2111_);
lean_ctor_set(v___x_2106_, 0, v___x_2115_);
v___x_2120_ = v___x_2106_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___f_2111_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v___f_2118_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v___f_2117_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v___f_2116_);
v___x_2120_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___f_2112_);
lean_ctor_set(v___x_2099_, 0, v___x_2120_);
v___x_2122_ = v___x_2099_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___f_2112_);
v___x_2122_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___f_2123_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_2125_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_2126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_2126_, 0, v_cls_2110_);
lean_closure_set(v___f_2126_, 1, v___x_2124_);
lean_closure_set(v___f_2126_, 2, v___f_2123_);
lean_closure_set(v___f_2126_, 3, v_declName_2034_);
lean_closure_set(v___f_2126_, 4, v_val_2042_);
lean_closure_set(v___f_2126_, 5, v___x_2122_);
lean_closure_set(v___f_2126_, 6, v___x_2125_);
v___x_2127_ = lean_apply_2(v_inst_1950_, lean_box(0), v___f_2126_);
v___x_2128_ = lean_apply_4(v_toBind_2079_, lean_box(0), lean_box(0), v___x_2127_, v___f_2109_);
return v___x_2128_;
}
}
}
}
}
else
{
lean_inc_ref(v_decl_2039_);
goto v___jp_2057_;
}
}
v___jp_2046_:
{
lean_object* v_toApplicative_2048_; lean_object* v_toBind_2049_; lean_object* v_withNewLemmas_2050_; lean_object* v_dsimp_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_toApplicative_2048_ = lean_ctor_get(v_inst_1949_, 0);
lean_inc_ref(v_toApplicative_2048_);
v_toBind_2049_ = lean_ctor_get(v_inst_1949_, 1);
lean_inc_n(v_toBind_2049_, 2);
v_withNewLemmas_2050_ = lean_ctor_get(v_inst_1952_, 0);
lean_inc(v_withNewLemmas_2050_);
v_dsimp_2051_ = lean_ctor_get(v_inst_1952_, 1);
lean_inc(v_dsimp_2051_);
v___x_2052_ = lean_box(v_nondep_2033_);
v___x_2053_ = lean_box(v___y_2047_);
lean_inc_ref(v_val_2042_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 24, 23);
lean_closure_set(v___f_2054_, 0, v_declName_2034_);
lean_closure_set(v___f_2054_, 1, v_type_2035_);
lean_closure_set(v___f_2054_, 2, v_value_2036_);
lean_closure_set(v___f_2054_, 3, v___x_2052_);
lean_closure_set(v___f_2054_, 4, v_toApplicative_2048_);
lean_closure_set(v___f_2054_, 5, v___x_2044_);
lean_closure_set(v___f_2054_, 6, v_us_2045_);
lean_closure_set(v___f_2054_, 7, v_decl_2039_);
lean_closure_set(v___f_2054_, 8, v_x_2041_);
lean_closure_set(v___f_2054_, 9, v_i_1957_);
lean_closure_set(v___f_2054_, 10, v_xs_1958_);
lean_closure_set(v___f_2054_, 11, v_inst_1949_);
lean_closure_set(v___f_2054_, 12, v_inst_1950_);
lean_closure_set(v___f_2054_, 13, v_inst_1951_);
lean_closure_set(v___f_2054_, 14, v_inst_1952_);
lean_closure_set(v___f_2054_, 15, v_info_1953_);
lean_closure_set(v___f_2054_, 16, v_fixed_1954_);
lean_closure_set(v___f_2054_, 17, v_used_1955_);
lean_closure_set(v___f_2054_, 18, v_body_2037_);
lean_closure_set(v___f_2054_, 19, v_toBind_2049_);
lean_closure_set(v___f_2054_, 20, v_withNewLemmas_2050_);
lean_closure_set(v___f_2054_, 21, v_val_2042_);
lean_closure_set(v___f_2054_, 22, v___x_2053_);
v___x_2055_ = lean_apply_1(v_dsimp_2051_, v_val_2042_);
v___x_2056_ = lean_apply_4(v_toBind_2049_, lean_box(0), lean_box(0), v___x_2055_, v___f_2054_);
return v___x_2056_;
}
v___jp_2057_:
{
uint8_t v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2058_ = 0;
v___x_2059_ = lean_array_get_size(v_fixed_1954_);
v___x_2060_ = lean_nat_dec_lt(v_i_1957_, v___x_2059_);
if (v___x_2060_ == 0)
{
v___y_2047_ = v___x_2058_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = lean_array_fget_borrowed(v_fixed_1954_, v_i_1957_);
v___x_2062_ = lean_unbox(v___x_2061_);
if (v___x_2062_ == 0)
{
lean_object* v_toApplicative_2063_; lean_object* v_toBind_2064_; lean_object* v_withNewLemmas_2065_; lean_object* v_simp_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_inc(v___x_2061_);
lean_inc(v_level_2040_);
v_toApplicative_2063_ = lean_ctor_get(v_inst_1949_, 0);
lean_inc_ref_n(v_toApplicative_2063_, 2);
v_toBind_2064_ = lean_ctor_get(v_inst_1949_, 1);
lean_inc_n(v_toBind_2064_, 3);
v_withNewLemmas_2065_ = lean_ctor_get(v_inst_1952_, 0);
lean_inc(v_withNewLemmas_2065_);
v_simp_2066_ = lean_ctor_get(v_inst_1952_, 2);
lean_inc(v_simp_2066_);
v___x_2067_ = lean_box(v_nondep_2033_);
lean_inc(v_inst_1950_);
lean_inc_ref(v_xs_1958_);
lean_inc_ref(v_value_2036_);
lean_inc_ref(v_type_2035_);
lean_inc(v_declName_2034_);
v___f_2068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_2068_, 0, v_decl_2039_);
lean_closure_set(v___f_2068_, 1, v_declName_2034_);
lean_closure_set(v___f_2068_, 2, v_type_2035_);
lean_closure_set(v___f_2068_, 3, v_value_2036_);
lean_closure_set(v___f_2068_, 4, v___x_2067_);
lean_closure_set(v___f_2068_, 5, v_toApplicative_2063_);
lean_closure_set(v___f_2068_, 6, v___x_2044_);
lean_closure_set(v___f_2068_, 7, v_us_2045_);
lean_closure_set(v___f_2068_, 8, v_inst_1949_);
lean_closure_set(v___f_2068_, 9, v_x_2041_);
lean_closure_set(v___f_2068_, 10, v_i_1957_);
lean_closure_set(v___f_2068_, 11, v_xs_1958_);
lean_closure_set(v___f_2068_, 12, v_inst_1950_);
lean_closure_set(v___f_2068_, 13, v_inst_1951_);
lean_closure_set(v___f_2068_, 14, v_inst_1952_);
lean_closure_set(v___f_2068_, 15, v_info_1953_);
lean_closure_set(v___f_2068_, 16, v_fixed_1954_);
lean_closure_set(v___f_2068_, 17, v_used_1955_);
lean_closure_set(v___f_2068_, 18, v_body_2037_);
lean_closure_set(v___f_2068_, 19, v_toBind_2064_);
lean_closure_set(v___f_2068_, 20, v_withNewLemmas_2065_);
v___f_2069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_2069_, 0, v___f_2068_);
v___x_2070_ = lean_box(v_nondep_2033_);
lean_inc_ref(v_val_2042_);
lean_inc_ref(v___f_2069_);
v___f_2071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_2071_, 0, v_toApplicative_2063_);
lean_closure_set(v___f_2071_, 1, v_level_2040_);
lean_closure_set(v___f_2071_, 2, v___x_2043_);
lean_closure_set(v___f_2071_, 3, v_type_2035_);
lean_closure_set(v___f_2071_, 4, v_value_2036_);
lean_closure_set(v___f_2071_, 5, v___x_2061_);
lean_closure_set(v___f_2071_, 6, v_toBind_2064_);
lean_closure_set(v___f_2071_, 7, v___f_2069_);
lean_closure_set(v___f_2071_, 8, v_xs_1958_);
lean_closure_set(v___f_2071_, 9, v___x_2070_);
lean_closure_set(v___f_2071_, 10, v___f_2069_);
lean_closure_set(v___f_2071_, 11, v_declName_2034_);
lean_closure_set(v___f_2071_, 12, v_val_2042_);
lean_closure_set(v___f_2071_, 13, v_inst_1950_);
v___x_2072_ = lean_apply_1(v_simp_2066_, v_val_2042_);
v___x_2073_ = lean_apply_4(v_toBind_2064_, lean_box(0), lean_box(0), v___x_2072_, v___f_2071_);
return v___x_2073_;
}
else
{
v___y_2047_ = v___x_2058_;
goto v___jp_2046_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1956_, 4);
lean_dec_ref(v_xs_1958_);
lean_dec(v_i_1957_);
lean_dec_ref(v_used_1955_);
lean_dec_ref(v_fixed_1954_);
lean_dec_ref(v_info_1953_);
lean_dec_ref(v_inst_1952_);
lean_dec_ref(v_inst_1951_);
lean_dec(v_inst_1950_);
goto v___jp_1959_;
}
}
else
{
lean_dec_ref(v_xs_1958_);
lean_dec(v_i_1957_);
lean_dec_ref(v_e_1956_);
lean_dec_ref(v_used_1955_);
lean_dec_ref(v_fixed_1954_);
lean_dec_ref(v_info_1953_);
lean_dec_ref(v_inst_1952_);
lean_dec_ref(v_inst_1951_);
lean_dec(v_inst_1950_);
goto v___jp_1959_;
}
}
v___jp_1959_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1960_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1961_ = l_instInhabitedOfMonad___redArg(v_inst_1949_, v___x_1960_);
v___x_1962_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1963_ = l_panic___redArg(v___x_1961_, v___x_1962_);
lean_dec(v___x_1961_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_2135_, lean_object* v_declName_2136_, lean_object* v_type_2137_, lean_object* v_value_2138_, lean_object* v_us_2139_, lean_object* v___x_2140_, lean_object* v_toApplicative_2141_, uint8_t v_nondep_2142_, lean_object* v_i_2143_, lean_object* v_xs_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_info_2149_, lean_object* v_fixed_2150_, lean_object* v_used_2151_, lean_object* v_body_2152_, lean_object* v_toBind_2153_, lean_object* v_____r_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v_x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2155_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_2156_ = l_Lean_mkConst(v___x_2155_, v___x_2135_);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_box(v_nondep_2142_);
v___f_2159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_2159_, 0, v___x_2157_);
lean_closure_set(v___f_2159_, 1, v_declName_2136_);
lean_closure_set(v___f_2159_, 2, v_type_2137_);
lean_closure_set(v___f_2159_, 3, v_value_2138_);
lean_closure_set(v___f_2159_, 4, v_us_2139_);
lean_closure_set(v___f_2159_, 5, v___x_2140_);
lean_closure_set(v___f_2159_, 6, v_toApplicative_2141_);
lean_closure_set(v___f_2159_, 7, v___x_2158_);
v___x_2160_ = lean_nat_add(v_i_2143_, v___x_2157_);
v___x_2161_ = lean_array_push(v_xs_2144_, v_x_2156_);
v___x_2162_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2145_, v_inst_2146_, v_inst_2147_, v_inst_2148_, v_info_2149_, v_fixed_2150_, v_used_2151_, v_body_2152_, v___x_2160_, v___x_2161_);
v___x_2163_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v___x_2162_, v___f_2159_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_info_2169_, lean_object* v_fixed_2170_, lean_object* v_used_2171_, lean_object* v_e_2172_, lean_object* v_i_2173_, lean_object* v_xs_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2165_, v_inst_2166_, v_inst_2167_, v_inst_2168_, v_info_2169_, v_fixed_2170_, v_used_2171_, v_e_2172_, v_i_2173_, v_xs_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_2176_){
_start:
{
switch(v_x_2176_)
{
case 0:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_unsigned_to_nat(0u);
return v___x_2177_;
}
case 1:
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
return v___x_2178_;
}
default: 
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_unsigned_to_nat(2u);
return v___x_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2180_){
_start:
{
uint8_t v_x_boxed_2181_; lean_object* v_res_2182_; 
v_x_boxed_2181_ = lean_unbox(v_x_2180_);
v_res_2182_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2183_){
_start:
{
lean_inc(v_k_2183_);
return v_k_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2184_);
lean_dec(v_k_2184_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2186_, lean_object* v_ctorIdx_2187_, uint8_t v_t_2188_, lean_object* v_h_2189_, lean_object* v_k_2190_){
_start:
{
lean_inc(v_k_2190_);
return v_k_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2191_, lean_object* v_ctorIdx_2192_, lean_object* v_t_2193_, lean_object* v_h_2194_, lean_object* v_k_2195_){
_start:
{
uint8_t v_t_boxed_2196_; lean_object* v_res_2197_; 
v_t_boxed_2196_ = lean_unbox(v_t_2193_);
v_res_2197_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2191_, v_ctorIdx_2192_, v_t_boxed_2196_, v_h_2194_, v_k_2195_);
lean_dec(v_k_2195_);
lean_dec(v_ctorIdx_2192_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2198_){
_start:
{
lean_inc(v_no_2198_);
return v_no_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2199_);
lean_dec(v_no_2199_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2201_, uint8_t v_t_2202_, lean_object* v_h_2203_, lean_object* v_no_2204_){
_start:
{
lean_inc(v_no_2204_);
return v_no_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2205_, lean_object* v_t_2206_, lean_object* v_h_2207_, lean_object* v_no_2208_){
_start:
{
uint8_t v_t_boxed_2209_; lean_object* v_res_2210_; 
v_t_boxed_2209_ = lean_unbox(v_t_2206_);
v_res_2210_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2205_, v_t_boxed_2209_, v_h_2207_, v_no_2208_);
lean_dec(v_no_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2211_){
_start:
{
lean_inc(v_singlePass_2211_);
return v_singlePass_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2212_);
lean_dec(v_singlePass_2212_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2214_, uint8_t v_t_2215_, lean_object* v_h_2216_, lean_object* v_singlePass_2217_){
_start:
{
lean_inc(v_singlePass_2217_);
return v_singlePass_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2218_, lean_object* v_t_2219_, lean_object* v_h_2220_, lean_object* v_singlePass_2221_){
_start:
{
uint8_t v_t_boxed_2222_; lean_object* v_res_2223_; 
v_t_boxed_2222_ = lean_unbox(v_t_2219_);
v_res_2223_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2218_, v_t_boxed_2222_, v_h_2220_, v_singlePass_2221_);
lean_dec(v_singlePass_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2224_){
_start:
{
lean_inc(v_twoPasses_2224_);
return v_twoPasses_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2225_);
lean_dec(v_twoPasses_2225_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2227_, uint8_t v_t_2228_, lean_object* v_h_2229_, lean_object* v_twoPasses_2230_){
_start:
{
lean_inc(v_twoPasses_2230_);
return v_twoPasses_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2231_, lean_object* v_t_2232_, lean_object* v_h_2233_, lean_object* v_twoPasses_2234_){
_start:
{
uint8_t v_t_boxed_2235_; lean_object* v_res_2236_; 
v_t_boxed_2235_ = lean_unbox(v_t_2232_);
v_res_2236_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2231_, v_t_boxed_2235_, v_h_2233_, v_twoPasses_2234_);
lean_dec(v_twoPasses_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2237_, lean_object* v_b_2238_, lean_object* v_c_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
lean_inc(v___y_2243_);
lean_inc_ref(v___y_2242_);
lean_inc(v___y_2241_);
lean_inc_ref(v___y_2240_);
v___x_2245_ = lean_apply_7(v_k_2237_, v_b_2238_, v_c_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, lean_box(0));
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2246_, lean_object* v_b_2247_, lean_object* v_c_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2246_, v_b_2247_, v_c_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2255_, lean_object* v_k_2256_, uint8_t v_cleanupAnnotations_2257_, uint8_t v_preserveNondepLet_2258_, uint8_t v_nondepLetOnly_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___f_2265_; uint8_t v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2265_, 0, v_k_2256_);
v___x_2266_ = 0;
v___x_2267_ = 1;
v___x_2268_ = lean_box(0);
v___x_2269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2255_, v___x_2266_, v___x_2267_, v_preserveNondepLet_2258_, v_nondepLetOnly_2259_, v___x_2268_, v___f_2265_, v_cleanupAnnotations_2257_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2269_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2269_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2286_, lean_object* v_k_2287_, lean_object* v_cleanupAnnotations_2288_, lean_object* v_preserveNondepLet_2289_, lean_object* v_nondepLetOnly_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2296_; uint8_t v_preserveNondepLet_boxed_2297_; uint8_t v_nondepLetOnly_boxed_2298_; lean_object* v_res_2299_; 
v_cleanupAnnotations_boxed_2296_ = lean_unbox(v_cleanupAnnotations_2288_);
v_preserveNondepLet_boxed_2297_ = lean_unbox(v_preserveNondepLet_2289_);
v_nondepLetOnly_boxed_2298_ = lean_unbox(v_nondepLetOnly_2290_);
v_res_2299_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2286_, v_k_2287_, v_cleanupAnnotations_boxed_2296_, v_preserveNondepLet_boxed_2297_, v_nondepLetOnly_boxed_2298_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2300_, lean_object* v_e_2301_, lean_object* v_k_2302_, uint8_t v_cleanupAnnotations_2303_, uint8_t v_preserveNondepLet_2304_, uint8_t v_nondepLetOnly_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2301_, v_k_2302_, v_cleanupAnnotations_2303_, v_preserveNondepLet_2304_, v_nondepLetOnly_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2312_, lean_object* v_e_2313_, lean_object* v_k_2314_, lean_object* v_cleanupAnnotations_2315_, lean_object* v_preserveNondepLet_2316_, lean_object* v_nondepLetOnly_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2323_; uint8_t v_preserveNondepLet_boxed_2324_; uint8_t v_nondepLetOnly_boxed_2325_; lean_object* v_res_2326_; 
v_cleanupAnnotations_boxed_2323_ = lean_unbox(v_cleanupAnnotations_2315_);
v_preserveNondepLet_boxed_2324_ = lean_unbox(v_preserveNondepLet_2316_);
v_nondepLetOnly_boxed_2325_ = lean_unbox(v_nondepLetOnly_2317_);
v_res_2326_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2312_, v_e_2313_, v_k_2314_, v_cleanupAnnotations_boxed_2323_, v_preserveNondepLet_boxed_2324_, v_nondepLetOnly_boxed_2325_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2327_, lean_object* v_a_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_snd_2333_; lean_object* v_fst_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2389_; 
v_snd_2333_ = lean_ctor_get(v_a_2328_, 1);
v_fst_2334_ = lean_ctor_get(v_a_2328_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2328_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2336_ = v_a_2328_;
v_isShared_2337_ = v_isSharedCheck_2389_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snd_2333_);
lean_inc(v_fst_2334_);
lean_dec(v_a_2328_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2389_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v_fst_2338_; lean_object* v_snd_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2388_; 
v_fst_2338_ = lean_ctor_get(v_snd_2333_, 0);
v_snd_2339_ = lean_ctor_get(v_snd_2333_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_snd_2333_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2341_ = v_snd_2333_;
v_isShared_2342_ = v_isSharedCheck_2388_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snd_2339_);
lean_inc(v_fst_2338_);
lean_dec(v_snd_2333_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2388_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = lean_nat_dec_lt(v___x_2343_, v_snd_2339_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2346_; 
if (v_isShared_2342_ == 0)
{
v___x_2346_ = v___x_2341_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_fst_2338_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_snd_2339_);
v___x_2346_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2346_);
v___x_2348_ = v___x_2336_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_fst_2334_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
else
{
lean_object* v_fvarSet_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v_fvarSet_2352_ = lean_ctor_get(v_fst_2334_, 1);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_sub(v_snd_2339_, v___x_2353_);
lean_dec(v_snd_2339_);
v___x_2355_ = l_Lean_instInhabitedExpr;
v___x_2356_ = lean_array_get_borrowed(v___x_2355_, v_xs_2327_, v___x_2354_);
v___x_2357_ = l_Lean_Expr_fvarId_x21(v___x_2356_);
v___x_2358_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2357_, v_fvarSet_2352_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2360_; 
lean_dec(v___x_2357_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2354_);
v___x_2360_ = v___x_2341_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_fst_2338_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v___x_2354_);
v___x_2360_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2360_);
v___x_2362_ = v___x_2336_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_fst_2334_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
v_a_2328_ = v___x_2362_;
goto _start;
}
}
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_FVarId_getDecl___redArg(v___x_2357_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l_Lean_LocalDecl_type(v_a_2367_);
v___x_2369_ = l_Lean_collectFVars(v_fst_2334_, v___x_2368_);
v___x_2370_ = l_Lean_LocalDecl_value(v_a_2367_, v___x_2358_);
lean_dec(v_a_2367_);
v___x_2371_ = l_Lean_collectFVars(v___x_2369_, v___x_2370_);
lean_inc(v___x_2356_);
v___x_2372_ = lean_array_push(v_fst_2338_, v___x_2356_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2354_);
lean_ctor_set(v___x_2341_, 0, v___x_2372_);
v___x_2374_ = v___x_2341_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2354_);
v___x_2374_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2374_);
lean_ctor_set(v___x_2336_, 0, v___x_2371_);
v___x_2376_ = v___x_2336_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
v_a_2328_ = v___x_2376_;
goto _start;
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v___x_2354_);
lean_del_object(v___x_2341_);
lean_dec(v_fst_2338_);
lean_del_object(v___x_2336_);
lean_dec(v_fst_2334_);
v_a_2380_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2366_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2366_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2390_, lean_object* v_a_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2390_, v_a_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_xs_2390_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2397_, lean_object* v_e_2398_, lean_object* v_xs_2399_, lean_object* v_body_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v_s_2409_; lean_object* v_i_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2406_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2407_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2397_);
lean_ctor_set(v___x_2408_, 2, v___x_2407_);
lean_inc_ref(v_body_2400_);
v_s_2409_ = l_Lean_collectFVars(v___x_2408_, v_body_2400_);
v_i_2410_ = lean_array_get_size(v_xs_2399_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2407_);
lean_ctor_set(v___x_2411_, 1, v_i_2410_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v_s_2409_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2399_, v___x_2412_, v___y_2401_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2429_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2429_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2429_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_snd_2418_; lean_object* v_fst_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v_snd_2418_ = lean_ctor_get(v_a_2414_, 1);
lean_inc(v_snd_2418_);
lean_dec(v_a_2414_);
v_fst_2419_ = lean_ctor_get(v_snd_2418_, 0);
lean_inc(v_fst_2419_);
lean_dec(v_snd_2418_);
v___x_2420_ = lean_array_get_size(v_fst_2419_);
v___x_2421_ = lean_nat_dec_eq(v___x_2420_, v_i_2410_);
if (v___x_2421_ == 0)
{
uint8_t v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; 
lean_del_object(v___x_2416_);
lean_dec_ref(v_e_2398_);
v___x_2422_ = 1;
v___x_2423_ = l_Array_reverse___redArg(v_fst_2419_);
v___x_2424_ = 1;
v___x_2425_ = l_Lean_Meta_mkLetFVars(v___x_2423_, v_body_2400_, v___x_2422_, v___x_2421_, v___x_2424_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec_ref(v___x_2423_);
return v___x_2425_;
}
else
{
lean_object* v___x_2427_; 
lean_dec(v_fst_2419_);
lean_dec_ref(v_body_2400_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_e_2398_);
v___x_2427_ = v___x_2416_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_e_2398_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v_body_2400_);
lean_dec_ref(v_e_2398_);
v_a_2430_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2413_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2413_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2438_, lean_object* v_e_2439_, lean_object* v_xs_2440_, lean_object* v_body_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2438_, v_e_2439_, v_xs_2440_, v_body_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v_xs_2440_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; lean_object* v___f_2455_; uint8_t v___x_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2454_ = lean_box(1);
lean_inc_ref(v_e_2448_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2455_, 0, v___x_2454_);
lean_closure_set(v___f_2455_, 1, v_e_2448_);
v___x_2456_ = 0;
v___x_2457_ = 1;
v___x_2458_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2448_, v___f_2455_, v___x_2456_, v___x_2457_, v___x_2456_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Meta_zetaUnused(v_e_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2466_, lean_object* v_inst_2467_, lean_object* v_a_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2466_, v_a_2468_, v___y_2469_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2475_, lean_object* v_inst_2476_, lean_object* v_a_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2475_, v_inst_2476_, v_a_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v_xs_2475_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2488_, lean_object* v_source_2489_, lean_object* v_result_2490_, uint8_t v_keepUnused_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
uint8_t v_modified_2497_; 
v_modified_2497_ = lean_ctor_get_uint8(v_result_2490_, sizeof(void*)*5);
if (v_modified_2497_ == 0)
{
if (v_keepUnused_2491_ == 0)
{
lean_object* v_exprType_2498_; lean_object* v___x_2499_; 
v_exprType_2498_ = lean_ctor_get(v_result_2490_, 1);
lean_inc_ref(v_exprType_2498_);
lean_dec_ref(v_result_2490_);
lean_inc_ref(v_source_2489_);
v___x_2499_ = l_Lean_Meta_zetaUnused(v_source_2489_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2518_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2518_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2518_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_expr_eqv(v_a_2500_, v_source_2489_);
lean_dec_ref(v_source_2489_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_u_2488_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lean_mkConst(v___x_2505_, v___x_2507_);
lean_inc(v_a_2500_);
v___x_2509_ = l_Lean_mkAppB(v___x_2508_, v_exprType_2498_, v_a_2500_);
v___x_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2500_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2510_);
v___x_2512_ = v___x_2502_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_dec(v_a_2500_);
lean_dec_ref(v_exprType_2498_);
lean_dec(v_u_2488_);
v___x_2514_ = lean_box(0);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2514_);
v___x_2516_ = v___x_2502_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v_exprType_2498_);
lean_dec_ref(v_source_2489_);
lean_dec(v_u_2488_);
v_a_2519_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2499_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2499_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
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
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec_ref(v_result_2490_);
lean_dec_ref(v_source_2489_);
lean_dec(v_u_2488_);
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
else
{
lean_object* v_expr_2529_; lean_object* v_exprType_2530_; lean_object* v_exprInit_2531_; lean_object* v_exprResult_2532_; lean_object* v_proof_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_proof_2541_; 
v_expr_2529_ = lean_ctor_get(v_result_2490_, 0);
lean_inc_ref(v_expr_2529_);
v_exprType_2530_ = lean_ctor_get(v_result_2490_, 1);
lean_inc_ref_n(v_exprType_2530_, 3);
v_exprInit_2531_ = lean_ctor_get(v_result_2490_, 2);
lean_inc_ref(v_exprInit_2531_);
v_exprResult_2532_ = lean_ctor_get(v_result_2490_, 3);
lean_inc_ref_n(v_exprResult_2532_, 2);
v_proof_2533_ = lean_ctor_get(v_result_2490_, 4);
lean_inc_ref(v_proof_2533_);
lean_dec_ref(v_result_2490_);
v___x_2534_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_u_2488_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
lean_inc_ref(v___x_2536_);
v___x_2537_ = l_Lean_mkConst(v___x_2534_, v___x_2536_);
lean_inc_ref(v___x_2537_);
v___x_2538_ = l_Lean_mkApp3(v___x_2537_, v_exprType_2530_, v_exprInit_2531_, v_expr_2529_);
v___x_2539_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2533_, v___x_2538_);
lean_inc_ref(v_source_2489_);
v___x_2540_ = l_Lean_mkApp3(v___x_2537_, v_exprType_2530_, v_source_2489_, v_exprResult_2532_);
v_proof_2541_ = l_Lean_Meta_mkExpectedPropHint(v___x_2539_, v___x_2540_);
if (v_keepUnused_2491_ == 0)
{
lean_object* v___x_2542_; 
lean_inc_ref(v_exprResult_2532_);
v___x_2542_ = l_Lean_Meta_zetaUnused(v_exprResult_2532_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2562_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2562_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2562_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_expr_eqv(v_a_2543_, v_exprResult_2532_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2536_);
v___x_2549_ = l_Lean_mkConst(v___x_2548_, v___x_2536_);
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2551_ = l_Lean_mkConst(v___x_2550_, v___x_2536_);
lean_inc_n(v_a_2543_, 2);
lean_inc_ref(v_exprType_2530_);
v___x_2552_ = l_Lean_mkAppB(v___x_2551_, v_exprType_2530_, v_a_2543_);
v___x_2553_ = l_Lean_mkApp6(v___x_2549_, v_exprType_2530_, v_source_2489_, v_exprResult_2532_, v_a_2543_, v_proof_2541_, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_a_2543_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2554_);
v___x_2556_ = v___x_2545_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_dec(v_a_2543_);
lean_dec_ref_known(v___x_2536_, 2);
lean_dec_ref(v_exprType_2530_);
lean_dec_ref(v_source_2489_);
v___x_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_exprResult_2532_);
lean_ctor_set(v___x_2558_, 1, v_proof_2541_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2558_);
v___x_2560_ = v___x_2545_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_proof_2541_);
lean_dec_ref_known(v___x_2536_, 2);
lean_dec_ref(v_exprResult_2532_);
lean_dec_ref(v_exprType_2530_);
lean_dec_ref(v_source_2489_);
v_a_2563_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2542_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2542_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2536_, 2);
lean_dec_ref(v_exprType_2530_);
lean_dec_ref(v_source_2489_);
v___x_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_exprResult_2532_);
lean_ctor_set(v___x_2571_, 1, v_proof_2541_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2573_, lean_object* v_source_2574_, lean_object* v_result_2575_, lean_object* v_keepUnused_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v_keepUnused_boxed_2582_; lean_object* v_res_2583_; 
v_keepUnused_boxed_2582_ = lean_unbox(v_keepUnused_2576_);
v_res_2583_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2573_, v_source_2574_, v_result_2575_, v_keepUnused_boxed_2582_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2584_, lean_object* v_e_2585_, lean_object* v_inst_2586_, uint8_t v_zetaUnusedMode_2587_, uint8_t v___x_2588_, uint8_t v___x_2589_, lean_object* v_r_2590_){
_start:
{
uint8_t v___y_2592_; 
switch(v_zetaUnusedMode_2587_)
{
case 0:
{
v___y_2592_ = v___x_2588_;
goto v___jp_2591_;
}
case 1:
{
v___y_2592_ = v___x_2588_;
goto v___jp_2591_;
}
default: 
{
v___y_2592_ = v___x_2589_;
goto v___jp_2591_;
}
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_box(v___y_2592_);
v___x_2594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2594_, 0, v_level_2584_);
lean_closure_set(v___x_2594_, 1, v_e_2585_);
lean_closure_set(v___x_2594_, 2, v_r_2590_);
lean_closure_set(v___x_2594_, 3, v___x_2593_);
v___x_2595_ = lean_apply_2(v_inst_2586_, lean_box(0), v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2596_, lean_object* v_e_2597_, lean_object* v_inst_2598_, lean_object* v_zetaUnusedMode_2599_, lean_object* v___x_2600_, lean_object* v___x_2601_, lean_object* v_r_2602_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2603_; uint8_t v___x_363__boxed_2604_; uint8_t v___x_364__boxed_2605_; lean_object* v_res_2606_; 
v_zetaUnusedMode_boxed_2603_ = lean_unbox(v_zetaUnusedMode_2599_);
v___x_363__boxed_2604_ = lean_unbox(v___x_2600_);
v___x_364__boxed_2605_ = lean_unbox(v___x_2601_);
v_res_2606_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2596_, v_e_2597_, v_inst_2598_, v_zetaUnusedMode_boxed_2603_, v___x_363__boxed_2604_, v___x_364__boxed_2605_, v_r_2602_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_info_2612_, lean_object* v_e_2613_, lean_object* v___x_2614_, lean_object* v_toBind_2615_, lean_object* v___f_2616_, lean_object* v_____x_2617_){
_start:
{
lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_fst_2618_ = lean_ctor_get(v_____x_2617_, 0);
lean_inc(v_fst_2618_);
v_snd_2619_ = lean_ctor_get(v_____x_2617_, 1);
lean_inc(v_snd_2619_);
lean_dec_ref(v_____x_2617_);
v___x_2620_ = lean_mk_empty_array_with_capacity(v___x_2607_);
v___x_2621_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2608_, v_inst_2609_, v_inst_2610_, v_inst_2611_, v_info_2612_, v_fst_2618_, v_snd_2619_, v_e_2613_, v___x_2614_, v___x_2620_);
v___x_2622_ = lean_apply_4(v_toBind_2615_, lean_box(0), lean_box(0), v___x_2621_, v___f_2616_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_info_2628_, lean_object* v_e_2629_, lean_object* v___x_2630_, lean_object* v_toBind_2631_, lean_object* v___f_2632_, lean_object* v_____x_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2623_, v_inst_2624_, v_inst_2625_, v_inst_2626_, v_inst_2627_, v_info_2628_, v_e_2629_, v___x_2630_, v_toBind_2631_, v___f_2632_, v_____x_2633_);
lean_dec(v___x_2623_);
return v_res_2634_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2637_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2638_ = lean_unsigned_to_nat(2u);
v___x_2639_ = lean_unsigned_to_nat(456u);
v___x_2640_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2642_ = l_mkPanicMessageWithDecl(v___x_2641_, v___x_2640_, v___x_2639_, v___x_2638_, v___x_2637_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2643_, lean_object* v_inst_2644_, uint8_t v_zetaUnusedMode_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_toBind_2649_, lean_object* v_info_2650_){
_start:
{
lean_object* v_haveInfo_2651_; lean_object* v_level_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v_haveInfo_2651_ = lean_ctor_get(v_info_2650_, 0);
v_level_2652_ = lean_ctor_get(v_info_2650_, 5);
v___x_2653_ = lean_array_get_size(v_haveInfo_2651_);
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_nat_dec_eq(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___f_2660_; lean_object* v___f_2661_; uint8_t v___y_2663_; 
v___x_2656_ = 1;
v___x_2657_ = lean_box(v_zetaUnusedMode_2645_);
v___x_2658_ = lean_box(v___x_2656_);
v___x_2659_ = lean_box(v___x_2655_);
lean_inc_n(v_inst_2644_, 2);
lean_inc_ref(v_e_2643_);
lean_inc(v_level_2652_);
v___f_2660_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2660_, 0, v_level_2652_);
lean_closure_set(v___f_2660_, 1, v_e_2643_);
lean_closure_set(v___f_2660_, 2, v_inst_2644_);
lean_closure_set(v___f_2660_, 3, v___x_2657_);
lean_closure_set(v___f_2660_, 4, v___x_2658_);
lean_closure_set(v___f_2660_, 5, v___x_2659_);
lean_inc(v_toBind_2649_);
lean_inc_ref(v_info_2650_);
v___f_2661_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2661_, 0, v___x_2653_);
lean_closure_set(v___f_2661_, 1, v_inst_2646_);
lean_closure_set(v___f_2661_, 2, v_inst_2644_);
lean_closure_set(v___f_2661_, 3, v_inst_2647_);
lean_closure_set(v___f_2661_, 4, v_inst_2648_);
lean_closure_set(v___f_2661_, 5, v_info_2650_);
lean_closure_set(v___f_2661_, 6, v_e_2643_);
lean_closure_set(v___f_2661_, 7, v___x_2654_);
lean_closure_set(v___f_2661_, 8, v_toBind_2649_);
lean_closure_set(v___f_2661_, 9, v___f_2660_);
switch(v_zetaUnusedMode_2645_)
{
case 0:
{
v___y_2663_ = v___x_2656_;
goto v___jp_2662_;
}
case 2:
{
v___y_2663_ = v___x_2656_;
goto v___jp_2662_;
}
default: 
{
v___y_2663_ = v___x_2655_;
goto v___jp_2662_;
}
}
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_box(v___y_2663_);
v___x_2665_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2665_, 0, v_info_2650_);
lean_closure_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_apply_2(v_inst_2644_, lean_box(0), v___x_2665_);
v___x_2667_ = lean_apply_4(v_toBind_2649_, lean_box(0), lean_box(0), v___x_2666_, v___f_2661_);
return v___x_2667_;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v_info_2650_);
lean_dec(v_toBind_2649_);
lean_dec_ref(v_inst_2648_);
lean_dec_ref(v_inst_2647_);
lean_dec(v_inst_2644_);
lean_dec_ref(v_e_2643_);
v___x_2668_ = lean_box(0);
v___x_2669_ = l_instInhabitedOfMonad___redArg(v_inst_2646_, v___x_2668_);
v___x_2670_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2671_ = l_panic___redArg(v___x_2669_, v___x_2670_);
lean_dec(v___x_2669_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2672_, lean_object* v_inst_2673_, lean_object* v_zetaUnusedMode_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_toBind_2678_, lean_object* v_info_2679_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2680_; lean_object* v_res_2681_; 
v_zetaUnusedMode_boxed_2680_ = lean_unbox(v_zetaUnusedMode_2674_);
v_res_2681_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2672_, v_inst_2673_, v_zetaUnusedMode_boxed_2680_, v_inst_2675_, v_inst_2676_, v_inst_2677_, v_toBind_2678_, v_info_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_e_2686_, uint8_t v_zetaUnusedMode_2687_){
_start:
{
lean_object* v_toBind_2688_; lean_object* v___x_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_toBind_2688_ = lean_ctor_get(v_inst_2682_, 1);
lean_inc_n(v_toBind_2688_, 2);
v___x_2689_ = lean_box(v_zetaUnusedMode_2687_);
lean_inc(v_inst_2683_);
lean_inc_ref(v_e_2686_);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2690_, 0, v_e_2686_);
lean_closure_set(v___f_2690_, 1, v_inst_2683_);
lean_closure_set(v___f_2690_, 2, v___x_2689_);
lean_closure_set(v___f_2690_, 3, v_inst_2682_);
lean_closure_set(v___f_2690_, 4, v_inst_2684_);
lean_closure_set(v___f_2690_, 5, v_inst_2685_);
lean_closure_set(v___f_2690_, 6, v_toBind_2688_);
v___x_2691_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2691_, 0, v_e_2686_);
v___x_2692_ = lean_apply_2(v_inst_2683_, lean_box(0), v___x_2691_);
v___x_2693_ = lean_apply_4(v_toBind_2688_, lean_box(0), lean_box(0), v___x_2692_, v___f_2690_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_e_2698_, lean_object* v_zetaUnusedMode_2699_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2700_; lean_object* v_res_2701_; 
v_zetaUnusedMode_boxed_2700_ = lean_unbox(v_zetaUnusedMode_2699_);
v_res_2701_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2694_, v_inst_2695_, v_inst_2696_, v_inst_2697_, v_e_2698_, v_zetaUnusedMode_boxed_2700_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_e_2707_, uint8_t v_zetaUnusedMode_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_e_2707_, v_zetaUnusedMode_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_e_2715_, lean_object* v_zetaUnusedMode_2716_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2717_; lean_object* v_res_2718_; 
v_zetaUnusedMode_boxed_2717_ = lean_unbox(v_zetaUnusedMode_2716_);
v_res_2718_ = l_Lean_Meta_simpHaveTelescope(v_m_2710_, v_inst_2711_, v_inst_2712_, v_inst_2713_, v_inst_2714_, v_e_2715_, v_zetaUnusedMode_boxed_2717_);
return v_res_2718_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MonadSimp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HaveTelescope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MonadSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedHaveInfo_default = _init_l_Lean_Meta_instInhabitedHaveInfo_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedHaveInfo_default);
l_Lean_Meta_instInhabitedHaveInfo = _init_l_Lean_Meta_instInhabitedHaveInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedHaveInfo);
l_Lean_Meta_instInhabitedHaveTelescopeInfo_default = _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default);
l_Lean_Meta_instInhabitedHaveTelescopeInfo = _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedHaveTelescopeInfo);
l_Lean_Meta_instInhabitedSimpHaveResult_default = _init_l_Lean_Meta_instInhabitedSimpHaveResult_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpHaveResult_default);
l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult = _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult();
lean_mark_persistent(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_HaveTelescope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_MonadSimp(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectLooseBVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_HaveTelescope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MonadSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLooseBVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HaveTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_HaveTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_HaveTelescope(builtin);
}
#ifdef __cplusplus
}
#endif
