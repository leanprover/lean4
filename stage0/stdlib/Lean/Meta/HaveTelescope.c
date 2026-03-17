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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withExistingLocalDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_collectLooseBVars(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveInfo_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveInfo;
static const lean_array_object l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0_value;
static const lean_string_object l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2 = (const lean_object*)&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedHaveTelescopeInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_getHaveTelescopeInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getHaveTelescopeInfo___closed__0 = (const lean_object*)&l_Lean_Meta_getHaveTelescopeInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_getHaveTelescopeInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "_have_telescope_info_dummy_"};
static const lean_object* l_Lean_Meta_getHaveTelescopeInfo___closed__1 = (const lean_object*)&l_Lean_Meta_getHaveTelescopeInfo___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getHaveTelescopeInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getHaveTelescopeInfo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 236, 171, 204, 19, 216, 21, 195)}};
static const lean_object* l_Lean_Meta_getHaveTelescopeInfo___closed__2 = (const lean_object*)&l_Lean_Meta_getHaveTelescopeInfo___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getHaveTelescopeInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getHaveTelescopeInfo___closed__3;
static lean_once_cell_t l_Lean_Meta_getHaveTelescopeInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getHaveTelescopeInfo___closed__4;
static lean_once_cell_t l_Lean_Meta_getHaveTelescopeInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getHaveTelescopeInfo___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
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
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "have telescope; simplifying body "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "have telescope; fixed "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "have telescope; non-fixed "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__15 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__15_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__15_value)} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__16 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__16_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__16_value)} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__0, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__0_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_box(0);
v___x_8_ = l_Lean_instInhabitedLocalDecl_default;
v___x_9_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_10_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__2, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__2_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__2);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveInfo(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_instInhabitedHaveInfo_default;
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
v___x_19_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2));
v___x_20_ = l_Lean_Expr_const___override(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_21_ = lean_box(0);
v___x_22_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3);
v___x_23_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_24_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_25_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_23_);
lean_ctor_set(v___x_25_, 2, v___x_23_);
lean_ctor_set(v___x_25_, 3, v___x_22_);
lean_ctor_set(v___x_25_, 4, v___x_22_);
lean_ctor_set(v___x_25_, 5, v___x_21_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default;
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(lean_object* v_lctx_28_, lean_object* v_x_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_keyedConfig_35_; uint8_t v_trackZetaDelta_36_; lean_object* v_zetaDeltaSet_37_; lean_object* v_localInstances_38_; lean_object* v_defEqCtx_x3f_39_; lean_object* v_synthPendingDepth_40_; lean_object* v_canUnfold_x3f_41_; uint8_t v_univApprox_42_; uint8_t v_inTypeClassResolution_43_; uint8_t v_cacheInferType_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_keyedConfig_35_ = lean_ctor_get(v___y_30_, 0);
v_trackZetaDelta_36_ = lean_ctor_get_uint8(v___y_30_, sizeof(void*)*7);
v_zetaDeltaSet_37_ = lean_ctor_get(v___y_30_, 1);
v_localInstances_38_ = lean_ctor_get(v___y_30_, 3);
v_defEqCtx_x3f_39_ = lean_ctor_get(v___y_30_, 4);
v_synthPendingDepth_40_ = lean_ctor_get(v___y_30_, 5);
v_canUnfold_x3f_41_ = lean_ctor_get(v___y_30_, 6);
v_univApprox_42_ = lean_ctor_get_uint8(v___y_30_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_43_ = lean_ctor_get_uint8(v___y_30_, sizeof(void*)*7 + 2);
v_cacheInferType_44_ = lean_ctor_get_uint8(v___y_30_, sizeof(void*)*7 + 3);
v_isSharedCheck_52_ = !lean_is_exclusive(v___y_30_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v___y_30_, 2);
lean_dec(v_unused_53_);
v___x_46_ = v___y_30_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_canUnfold_x3f_41_);
lean_inc(v_synthPendingDepth_40_);
lean_inc(v_defEqCtx_x3f_39_);
lean_inc(v_localInstances_38_);
lean_inc(v_zetaDeltaSet_37_);
lean_inc(v_keyedConfig_35_);
lean_dec(v___y_30_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 2, v_lctx_28_);
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_keyedConfig_35_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_zetaDeltaSet_37_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_lctx_28_);
lean_ctor_set(v_reuseFailAlloc_51_, 3, v_localInstances_38_);
lean_ctor_set(v_reuseFailAlloc_51_, 4, v_defEqCtx_x3f_39_);
lean_ctor_set(v_reuseFailAlloc_51_, 5, v_synthPendingDepth_40_);
lean_ctor_set(v_reuseFailAlloc_51_, 6, v_canUnfold_x3f_41_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*7, v_trackZetaDelta_36_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*7 + 1, v_univApprox_42_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*7 + 2, v_inTypeClassResolution_43_);
lean_ctor_set_uint8(v_reuseFailAlloc_51_, sizeof(void*)*7 + 3, v_cacheInferType_44_);
v___x_49_ = v_reuseFailAlloc_51_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; 
v___x_50_ = lean_apply_5(v_x_29_, v___x_49_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object* v_lctx_54_, lean_object* v_x_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_54_, v_x_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object* v_00_u03b1_62_, lean_object* v_lctx_63_, lean_object* v_x_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_63_, v_x_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(lean_object* v_00_u03b1_71_, lean_object* v_lctx_72_, lean_object* v_x_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(v_00_u03b1_71_, v_lctx_72_, v_x_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
return v_x_80_;
}
else
{
lean_object* v_key_82_; lean_object* v_value_83_; lean_object* v_tail_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_107_; 
v_key_82_ = lean_ctor_get(v_x_81_, 0);
v_value_83_ = lean_ctor_get(v_x_81_, 1);
v_tail_84_ = lean_ctor_get(v_x_81_, 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_107_ == 0)
{
v___x_86_ = v_x_81_;
v_isShared_87_ = v_isSharedCheck_107_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_tail_84_);
lean_inc(v_value_83_);
lean_inc(v_key_82_);
lean_dec(v_x_81_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_107_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v_fold_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_88_ = lean_array_get_size(v_x_80_);
v___x_89_ = lean_uint64_of_nat(v_key_82_);
v___x_90_ = 32ULL;
v___x_91_ = lean_uint64_shift_right(v___x_89_, v___x_90_);
v_fold_92_ = lean_uint64_xor(v___x_89_, v___x_91_);
v___x_93_ = 16ULL;
v___x_94_ = lean_uint64_shift_right(v_fold_92_, v___x_93_);
v___x_95_ = lean_uint64_xor(v_fold_92_, v___x_94_);
v___x_96_ = lean_uint64_to_usize(v___x_95_);
v___x_97_ = lean_usize_of_nat(v___x_88_);
v___x_98_ = ((size_t)1ULL);
v___x_99_ = lean_usize_sub(v___x_97_, v___x_98_);
v___x_100_ = lean_usize_land(v___x_96_, v___x_99_);
v___x_101_ = lean_array_uget_borrowed(v_x_80_, v___x_100_);
lean_inc(v___x_101_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 2, v___x_101_);
v___x_103_ = v___x_86_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_key_82_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_value_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v___x_101_);
v___x_103_ = v_reuseFailAlloc_106_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_array_uset(v_x_80_, v___x_100_, v___x_103_);
v_x_80_ = v___x_104_;
v_x_81_ = v_tail_84_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(lean_object* v_i_108_, lean_object* v_source_109_, lean_object* v_target_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_array_get_size(v_source_109_);
v___x_112_ = lean_nat_dec_lt(v_i_108_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_source_109_);
lean_dec(v_i_108_);
return v_target_110_;
}
else
{
lean_object* v_es_113_; lean_object* v___x_114_; lean_object* v_source_115_; lean_object* v_target_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_es_113_ = lean_array_fget(v_source_109_, v_i_108_);
v___x_114_ = lean_box(0);
v_source_115_ = lean_array_fset(v_source_109_, v_i_108_, v___x_114_);
v_target_116_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_target_110_, v_es_113_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_i_108_, v___x_117_);
lean_dec(v_i_108_);
v_i_108_ = v___x_118_;
v_source_109_ = v_source_115_;
v_target_110_ = v_target_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(lean_object* v_data_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_nbuckets_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_121_ = lean_array_get_size(v_data_120_);
v___x_122_ = lean_unsigned_to_nat(2u);
v_nbuckets_123_ = lean_nat_mul(v___x_121_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_box(0);
v___x_126_ = lean_mk_array(v_nbuckets_123_, v___x_125_);
v___x_127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v___x_124_, v_data_120_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object* v_a_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
else
{
lean_object* v_key_131_; lean_object* v_tail_132_; uint8_t v___x_133_; 
v_key_131_ = lean_ctor_get(v_x_129_, 0);
v_tail_132_ = lean_ctor_get(v_x_129_, 2);
v___x_133_ = lean_nat_dec_eq(v_key_131_, v_a_128_);
if (v___x_133_ == 0)
{
v_x_129_ = v_tail_132_;
goto _start;
}
else
{
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object* v_a_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_135_, v_x_136_);
lean_dec(v_x_136_);
lean_dec(v_a_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object* v_m_139_, lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
lean_object* v_size_142_; lean_object* v_buckets_143_; lean_object* v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v_fold_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v_bkt_157_; uint8_t v___x_158_; 
v_size_142_ = lean_ctor_get(v_m_139_, 0);
v_buckets_143_ = lean_ctor_get(v_m_139_, 1);
v___x_144_ = lean_array_get_size(v_buckets_143_);
v___x_145_ = lean_uint64_of_nat(v_a_140_);
v___x_146_ = 32ULL;
v___x_147_ = lean_uint64_shift_right(v___x_145_, v___x_146_);
v_fold_148_ = lean_uint64_xor(v___x_145_, v___x_147_);
v___x_149_ = 16ULL;
v___x_150_ = lean_uint64_shift_right(v_fold_148_, v___x_149_);
v___x_151_ = lean_uint64_xor(v_fold_148_, v___x_150_);
v___x_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = lean_usize_of_nat(v___x_144_);
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_sub(v___x_153_, v___x_154_);
v___x_156_ = lean_usize_land(v___x_152_, v___x_155_);
v_bkt_157_ = lean_array_uget_borrowed(v_buckets_143_, v___x_156_);
v___x_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_140_, v_bkt_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_179_; 
lean_inc_ref(v_buckets_143_);
lean_inc(v_size_142_);
v_isSharedCheck_179_ = !lean_is_exclusive(v_m_139_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_180_ = lean_ctor_get(v_m_139_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_m_139_, 0);
lean_dec(v_unused_181_);
v___x_160_ = v_m_139_;
v_isShared_161_ = v_isSharedCheck_179_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_m_139_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_179_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v_size_x27_163_; lean_object* v___x_164_; lean_object* v_buckets_x27_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v_size_x27_163_ = lean_nat_add(v_size_142_, v___x_162_);
lean_dec(v_size_142_);
lean_inc(v_bkt_157_);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v_a_140_);
lean_ctor_set(v___x_164_, 1, v_b_141_);
lean_ctor_set(v___x_164_, 2, v_bkt_157_);
v_buckets_x27_165_ = lean_array_uset(v_buckets_143_, v___x_156_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(4u);
v___x_167_ = lean_nat_mul(v_size_x27_163_, v___x_166_);
v___x_168_ = lean_unsigned_to_nat(3u);
v___x_169_ = lean_nat_div(v___x_167_, v___x_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_array_get_size(v_buckets_x27_165_);
v___x_171_ = lean_nat_dec_le(v___x_169_, v___x_170_);
lean_dec(v___x_169_);
if (v___x_171_ == 0)
{
lean_object* v_val_172_; lean_object* v___x_174_; 
v_val_172_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_buckets_x27_165_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_val_172_);
lean_ctor_set(v___x_160_, 0, v_size_x27_163_);
v___x_174_ = v___x_160_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_size_x27_163_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_val_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v___x_177_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_buckets_x27_165_);
lean_ctor_set(v___x_160_, 0, v_size_x27_163_);
v___x_177_ = v___x_160_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_size_x27_163_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_buckets_x27_165_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_dec(v_b_141_);
lean_dec(v_a_140_);
return v_m_139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object* v_numHaves_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
return v_x_183_;
}
else
{
lean_object* v_key_185_; lean_object* v_tail_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_key_185_ = lean_ctor_get(v_x_184_, 0);
v_tail_186_ = lean_ctor_get(v_x_184_, 2);
v___x_187_ = lean_nat_sub(v_numHaves_182_, v_key_185_);
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_sub(v___x_187_, v___x_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_x_183_, v___x_189_, v___x_190_);
v_x_183_ = v___x_191_;
v_x_184_ = v_tail_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object* v_numHaves_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_193_, v_x_194_, v_x_195_);
lean_dec(v_x_195_);
lean_dec(v_numHaves_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object* v_numHaves_197_, lean_object* v_as_198_, size_t v_i_199_, size_t v_stop_200_, lean_object* v_b_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_eq(v_i_199_, v_stop_200_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; size_t v___x_205_; size_t v___x_206_; 
v___x_203_ = lean_array_uget_borrowed(v_as_198_, v_i_199_);
v___x_204_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_197_, v_b_201_, v___x_203_);
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_add(v_i_199_, v___x_205_);
v_i_199_ = v___x_206_;
v_b_201_ = v___x_204_;
goto _start;
}
else
{
return v_b_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object* v_numHaves_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_stop_211_, lean_object* v_b_212_){
_start:
{
size_t v_i_boxed_213_; size_t v_stop_boxed_214_; lean_object* v_res_215_; 
v_i_boxed_213_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_211_);
lean_dec(v_stop_211_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_208_, v_as_209_, v_i_boxed_213_, v_stop_boxed_214_, v_b_212_);
lean_dec_ref(v_as_209_);
lean_dec(v_numHaves_208_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(lean_object* v_numHaves_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_buckets_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_220_ = l_Lean_Expr_collectLooseBVars(v_a_217_, v___x_218_);
v_buckets_221_ = lean_ctor_get(v___x_220_, 1);
lean_inc_ref(v_buckets_221_);
lean_dec_ref(v___x_220_);
v___x_222_ = lean_array_get_size(v_buckets_221_);
v___x_223_ = lean_nat_dec_lt(v___x_218_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v_buckets_221_);
return v___x_219_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = lean_nat_dec_le(v___x_222_, v___x_222_);
if (v___x_224_ == 0)
{
if (v___x_223_ == 0)
{
lean_dec_ref(v_buckets_221_);
return v___x_219_;
}
else
{
size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v___x_225_ = ((size_t)0ULL);
v___x_226_ = lean_usize_of_nat(v___x_222_);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_216_, v_buckets_221_, v___x_225_, v___x_226_, v___x_219_);
lean_dec_ref(v_buckets_221_);
return v___x_227_;
}
}
else
{
size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; 
v___x_228_ = ((size_t)0ULL);
v___x_229_ = lean_usize_of_nat(v___x_222_);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_216_, v_buckets_221_, v___x_228_, v___x_229_, v___x_219_);
lean_dec_ref(v_buckets_221_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_231_, v_a_232_);
lean_dec(v_numHaves_231_);
return v_res_233_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_234_, lean_object* v_t_235_){
_start:
{
if (lean_obj_tag(v_t_235_) == 0)
{
lean_object* v_k_236_; lean_object* v_l_237_; lean_object* v_r_238_; uint8_t v___x_239_; 
v_k_236_ = lean_ctor_get(v_t_235_, 1);
v_l_237_ = lean_ctor_get(v_t_235_, 3);
v_r_238_ = lean_ctor_get(v_t_235_, 4);
v___x_239_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_234_, v_k_236_);
switch(v___x_239_)
{
case 0:
{
v_t_235_ = v_l_237_;
goto _start;
}
case 1:
{
uint8_t v___x_241_; 
v___x_241_ = 1;
return v___x_241_;
}
default: 
{
v_t_235_ = v_r_238_;
goto _start;
}
}
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 0;
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_244_, lean_object* v_t_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_244_, v_t_245_);
lean_dec(v_t_245_);
lean_dec(v_k_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_248_, lean_object* v___x_249_, lean_object* v_n_250_, lean_object* v_j_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_zero_253_; uint8_t v_isZero_254_; 
v_zero_253_ = lean_unsigned_to_nat(0u);
v_isZero_254_ = lean_nat_dec_eq(v_j_251_, v_zero_253_);
if (v_isZero_254_ == 1)
{
lean_dec(v_j_251_);
return v_a_252_;
}
else
{
lean_object* v_one_255_; lean_object* v_n_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_one_255_ = lean_unsigned_to_nat(1u);
v_n_256_ = lean_nat_sub(v_j_251_, v_one_255_);
v___x_257_ = lean_nat_sub(v_n_250_, v_j_251_);
lean_dec(v_j_251_);
v___x_258_ = lean_array_fget_borrowed(v_fvars_248_, v___x_257_);
v___x_259_ = l_Lean_Expr_fvarId_x21(v___x_258_);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_259_, v___x_249_);
lean_dec(v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v___x_257_);
v_j_251_ = v_n_256_;
goto _start;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_box(0);
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_252_, v___x_257_, v___x_262_);
v_j_251_ = v_n_256_;
v_a_252_ = v___x_263_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_265_, lean_object* v___x_266_, lean_object* v_n_267_, lean_object* v_j_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_265_, v___x_266_, v_n_267_, v_j_268_, v_a_269_);
lean_dec(v_n_267_);
lean_dec(v___x_266_);
lean_dec_ref(v_fvars_265_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = lean_unsigned_to_nat(16u);
v___x_273_ = lean_mk_array(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_279_, lean_object* v___x_280_, lean_object* v_fvars_281_, lean_object* v_info_282_, lean_object* v_bodyDeps_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; 
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
lean_inc(v___y_285_);
lean_inc_ref(v___y_284_);
lean_inc_ref(v_body_279_);
v___x_289_ = lean_infer_type(v_body_279_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref(v___x_289_);
lean_inc(v_a_290_);
v___x_291_ = l_Lean_Meta_getLevel(v_a_290_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_319_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_319_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_319_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_319_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_fvarSet_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_haveInfo_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_280_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
lean_inc(v_a_290_);
v___x_299_ = l_Lean_collectFVars(v___x_298_, v_a_290_);
v_fvarSet_300_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_fvarSet_300_);
lean_dec_ref(v___x_299_);
v___x_301_ = lean_array_get_size(v_fvars_281_);
v___x_302_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_281_, v_fvarSet_300_, v___x_301_, v___x_301_, v___x_296_);
lean_dec(v_fvarSet_300_);
v_haveInfo_303_ = lean_ctor_get(v_info_282_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v_info_282_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_314_ = lean_ctor_get(v_info_282_, 5);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_info_282_, 4);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_info_282_, 3);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_info_282_, 2);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_info_282_, 1);
lean_dec(v_unused_318_);
v___x_305_ = v_info_282_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_haveInfo_303_);
lean_dec(v_info_282_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 5, v_a_292_);
lean_ctor_set(v___x_305_, 4, v_a_290_);
lean_ctor_set(v___x_305_, 3, v_body_279_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
lean_ctor_set(v___x_305_, 1, v_bodyDeps_283_);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_haveInfo_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_bodyDeps_283_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_body_279_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_a_290_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_a_292_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_308_);
v___x_310_ = v___x_294_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec(v_a_290_);
lean_dec_ref(v_bodyDeps_283_);
lean_dec_ref(v_info_282_);
lean_dec(v___x_280_);
lean_dec_ref(v_body_279_);
v_a_320_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_291_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_291_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec_ref(v_bodyDeps_283_);
lean_dec_ref(v_info_282_);
lean_dec(v___x_280_);
lean_dec_ref(v_body_279_);
v_a_328_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_289_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_289_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_336_, lean_object* v___x_337_, lean_object* v_fvars_338_, lean_object* v_info_339_, lean_object* v_bodyDeps_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_336_, v___x_337_, v_fvars_338_, v_info_339_, v_bodyDeps_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec_ref(v_fvars_338_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; lean_object* v_ngen_350_; lean_object* v_namePrefix_351_; lean_object* v_idx_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_381_; 
v___x_349_ = lean_st_ref_get(v___y_347_);
v_ngen_350_ = lean_ctor_get(v___x_349_, 2);
lean_inc_ref(v_ngen_350_);
lean_dec(v___x_349_);
v_namePrefix_351_ = lean_ctor_get(v_ngen_350_, 0);
v_idx_352_ = lean_ctor_get(v_ngen_350_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_ngen_350_);
if (v_isSharedCheck_381_ == 0)
{
v___x_354_ = v_ngen_350_;
v_isShared_355_ = v_isSharedCheck_381_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_idx_352_);
lean_inc(v_namePrefix_351_);
lean_dec(v_ngen_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_381_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v_env_357_; lean_object* v_nextMacroScope_358_; lean_object* v_auxDeclNGen_359_; lean_object* v_traceState_360_; lean_object* v_cache_361_; lean_object* v_messages_362_; lean_object* v_infoState_363_; lean_object* v_snapshotTasks_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_379_; 
v___x_356_ = lean_st_ref_take(v___y_347_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
v_nextMacroScope_358_ = lean_ctor_get(v___x_356_, 1);
v_auxDeclNGen_359_ = lean_ctor_get(v___x_356_, 3);
v_traceState_360_ = lean_ctor_get(v___x_356_, 4);
v_cache_361_ = lean_ctor_get(v___x_356_, 5);
v_messages_362_ = lean_ctor_get(v___x_356_, 6);
v_infoState_363_ = lean_ctor_get(v___x_356_, 7);
v_snapshotTasks_364_ = lean_ctor_get(v___x_356_, 8);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_356_, 2);
lean_dec(v_unused_380_);
v___x_366_ = v___x_356_;
v_isShared_367_ = v_isSharedCheck_379_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snapshotTasks_364_);
lean_inc(v_infoState_363_);
lean_inc(v_messages_362_);
lean_inc(v_cache_361_);
lean_inc(v_traceState_360_);
lean_inc(v_auxDeclNGen_359_);
lean_inc(v_nextMacroScope_358_);
lean_inc(v_env_357_);
lean_dec(v___x_356_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_379_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_r_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
lean_inc(v_idx_352_);
lean_inc(v_namePrefix_351_);
v_r_368_ = l_Lean_Name_num___override(v_namePrefix_351_, v_idx_352_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_idx_352_, v___x_369_);
lean_dec(v_idx_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_370_);
v___x_372_ = v___x_354_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_namePrefix_351_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_378_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 2, v___x_372_);
v___x_374_ = v___x_366_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_env_357_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_nextMacroScope_358_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_auxDeclNGen_359_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_traceState_360_);
lean_ctor_set(v_reuseFailAlloc_377_, 5, v_cache_361_);
lean_ctor_set(v_reuseFailAlloc_377_, 6, v_messages_362_);
lean_ctor_set(v_reuseFailAlloc_377_, 7, v_infoState_363_);
lean_ctor_set(v_reuseFailAlloc_377_, 8, v_snapshotTasks_364_);
v___x_374_ = v_reuseFailAlloc_377_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_st_ref_set(v___y_347_, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_r_368_);
return v___x_376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_382_);
lean_dec(v___y_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v___x_390_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_388_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_405_, lean_object* v_numHaves_406_, lean_object* v_info_407_, lean_object* v_lctx_408_, lean_object* v_fvars_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; 
v___x_415_ = lean_box(1);
if (lean_obj_tag(v_e_405_) == 8)
{
uint8_t v_nondep_425_; 
v_nondep_425_ = lean_ctor_get_uint8(v_e_405_, sizeof(void*)*4 + 8);
if (v_nondep_425_ == 1)
{
lean_object* v_declName_426_; lean_object* v_type_427_; lean_object* v_value_428_; lean_object* v_body_429_; lean_object* v_t_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_declName_426_ = lean_ctor_get(v_e_405_, 0);
lean_inc(v_declName_426_);
v_type_427_ = lean_ctor_get(v_e_405_, 1);
lean_inc_ref(v_type_427_);
v_value_428_ = lean_ctor_get(v_e_405_, 2);
lean_inc_ref(v_value_428_);
v_body_429_ = lean_ctor_get(v_e_405_, 3);
lean_inc_ref(v_body_429_);
lean_dec_ref(v_e_405_);
v_t_430_ = lean_expr_instantiate_rev(v_type_427_, v_fvars_409_);
lean_inc_ref(v_t_430_);
v___x_431_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_431_, 0, v_t_430_);
lean_inc(v_a_413_);
lean_inc_ref(v_a_412_);
lean_inc(v_a_411_);
lean_inc_ref(v_a_410_);
lean_inc_ref(v_lctx_408_);
v___x_432_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_408_, v___x_431_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v_haveInfo_436_; lean_object* v_bodyDeps_437_; lean_object* v_bodyTypeDeps_438_; lean_object* v_body_439_; lean_object* v_bodyType_440_; lean_object* v_level_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_462_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v___x_434_);
v_haveInfo_436_ = lean_ctor_get(v_info_407_, 0);
v_bodyDeps_437_ = lean_ctor_get(v_info_407_, 1);
v_bodyTypeDeps_438_ = lean_ctor_get(v_info_407_, 2);
v_body_439_ = lean_ctor_get(v_info_407_, 3);
v_bodyType_440_ = lean_ctor_get(v_info_407_, 4);
v_level_441_ = lean_ctor_get(v_info_407_, 5);
v_isSharedCheck_462_ = !lean_is_exclusive(v_info_407_);
if (v_isSharedCheck_462_ == 0)
{
v___x_443_ = v_info_407_;
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_level_441_);
lean_inc(v_bodyType_440_);
lean_inc(v_body_439_);
lean_inc(v_bodyTypeDeps_438_);
lean_inc(v_bodyDeps_437_);
lean_inc(v_haveInfo_436_);
lean_dec(v_info_407_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_typeBackDeps_445_; lean_object* v_valueBackDeps_446_; lean_object* v_v_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v_typeBackDeps_445_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_406_, v_type_427_);
lean_inc_ref(v_value_428_);
v_valueBackDeps_446_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_406_, v_value_428_);
v_v_447_ = lean_expr_instantiate_rev(v_value_428_, v_fvars_409_);
lean_dec_ref(v_value_428_);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = 0;
lean_inc(v_a_435_);
v___x_450_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v_a_435_);
lean_ctor_set(v___x_450_, 2, v_declName_426_);
lean_ctor_set(v___x_450_, 3, v_t_430_);
lean_ctor_set(v___x_450_, 4, v_v_447_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5, v_nondep_425_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5 + 1, v___x_449_);
lean_inc_ref(v___x_450_);
v___x_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_451_, 0, v_typeBackDeps_445_);
lean_ctor_set(v___x_451_, 1, v_valueBackDeps_446_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
lean_ctor_set(v___x_451_, 3, v_a_433_);
v___x_452_ = lean_array_push(v_haveInfo_436_, v___x_451_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_452_);
v___x_454_ = v___x_443_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_bodyDeps_437_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_bodyTypeDeps_438_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_body_439_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_bodyType_440_);
lean_ctor_set(v_reuseFailAlloc_461_, 5, v_level_441_);
v___x_454_ = v_reuseFailAlloc_461_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = l_Lean_LocalContext_addDecl(v_lctx_408_, v___x_450_);
v___x_456_ = l_Lean_mkFVar(v_a_435_);
v___x_457_ = lean_array_push(v_fvars_409_, v___x_456_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v_numHaves_406_, v___x_458_);
lean_dec(v_numHaves_406_);
v_e_405_ = v_body_429_;
v_numHaves_406_ = v___x_459_;
v_info_407_ = v___x_454_;
v_lctx_408_ = v___x_455_;
v_fvars_409_ = v___x_457_;
goto _start;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_433_);
lean_dec_ref(v_t_430_);
lean_dec_ref(v_body_429_);
lean_dec_ref(v_value_428_);
lean_dec_ref(v_type_427_);
lean_dec(v_declName_426_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec_ref(v_fvars_409_);
lean_dec_ref(v_lctx_408_);
lean_dec_ref(v_info_407_);
lean_dec(v_numHaves_406_);
v_a_463_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_434_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_434_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_t_430_);
lean_dec_ref(v_body_429_);
lean_dec_ref(v_value_428_);
lean_dec_ref(v_type_427_);
lean_dec(v_declName_426_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec_ref(v_fvars_409_);
lean_dec_ref(v_lctx_408_);
lean_dec_ref(v_info_407_);
lean_dec(v_numHaves_406_);
v_a_471_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_432_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_432_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
v___y_417_ = v_a_410_;
v___y_418_ = v_a_411_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
goto v___jp_416_;
}
}
else
{
v___y_417_ = v_a_410_;
v___y_418_ = v_a_411_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
goto v___jp_416_;
}
v___jp_416_:
{
lean_object* v_bodyDeps_421_; lean_object* v_body_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
lean_inc_ref(v_e_405_);
v_bodyDeps_421_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_406_, v_e_405_);
lean_dec(v_numHaves_406_);
v_body_422_ = lean_expr_instantiate_rev(v_e_405_, v_fvars_409_);
lean_dec_ref(v_e_405_);
v___f_423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_423_, 0, v_body_422_);
lean_closure_set(v___f_423_, 1, v___x_415_);
lean_closure_set(v___f_423_, 2, v_fvars_409_);
lean_closure_set(v___f_423_, 3, v_info_407_);
lean_closure_set(v___f_423_, 4, v_bodyDeps_421_);
v___x_424_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_408_, v___f_423_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_479_, lean_object* v_numHaves_480_, lean_object* v_info_481_, lean_object* v_lctx_482_, lean_object* v_fvars_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_479_, v_numHaves_480_, v_info_481_, v_lctx_482_, v_fvars_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_490_, lean_object* v_m_491_, lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_491_, v_a_492_, v_b_493_);
return v___x_494_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_495_, lean_object* v_k_496_, lean_object* v_t_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_496_, v_t_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_499_, lean_object* v_k_500_, lean_object* v_t_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_499_, v_k_500_, v_t_501_);
lean_dec(v_t_501_);
lean_dec(v_k_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_504_, lean_object* v___x_505_, lean_object* v_n_506_, lean_object* v_j_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_504_, v___x_505_, v_n_506_, v_j_507_, v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_511_, lean_object* v___x_512_, lean_object* v_n_513_, lean_object* v_j_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_511_, v___x_512_, v_n_513_, v_j_514_, v_a_515_, v_a_516_);
lean_dec(v_n_513_);
lean_dec(v___x_512_);
lean_dec_ref(v_fvars_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_530_, lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_531_, v_x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_534_, lean_object* v_a_535_, lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_534_, v_a_535_, v_x_536_);
lean_dec(v_x_536_);
lean_dec(v_a_535_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_539_, lean_object* v_data_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_542_, lean_object* v_i_543_, lean_object* v_source_544_, lean_object* v_target_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_543_, v_source_544_, v_target_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_548_, v_x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Meta_getHaveTelescopeInfo___closed__3(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(0);
v___x_557_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__2));
v___x_558_ = l_Lean_Expr_const___override(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Meta_getHaveTelescopeInfo___closed__4(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__2));
v___x_560_ = l_Lean_Level_param___override(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Meta_getHaveTelescopeInfo___closed__5(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_561_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__4, &l_Lean_Meta_getHaveTelescopeInfo___closed__4_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__4);
v___x_562_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__3, &l_Lean_Meta_getHaveTelescopeInfo___closed__3_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__3);
v___x_563_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_564_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__0));
v___x_565_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_563_);
lean_ctor_set(v___x_565_, 2, v___x_563_);
lean_ctor_set(v___x_565_, 3, v___x_562_);
lean_ctor_set(v___x_565_, 4, v___x_562_);
lean_ctor_set(v___x_565_, 5, v___x_561_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_lctx_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_lctx_572_ = lean_ctor_get(v_a_567_, 2);
lean_inc_ref(v_lctx_572_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__0));
v___x_575_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__5, &l_Lean_Meta_getHaveTelescopeInfo___closed__5_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__5);
v___x_576_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_566_, v___x_573_, v___x_575_, v_lctx_572_, v___x_574_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
return v_x_584_;
}
else
{
lean_object* v_key_586_; lean_object* v_tail_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_key_586_ = lean_ctor_get(v_x_585_, 0);
v_tail_587_ = lean_ctor_get(v_x_585_, 2);
v___x_588_ = 1;
v___x_589_ = lean_box(v___x_588_);
v___x_590_ = lean_array_set(v_x_584_, v_key_586_, v___x_589_);
v_x_584_ = v___x_590_;
v_x_585_ = v_tail_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_595_, size_t v_i_596_, size_t v_stop_597_, lean_object* v_b_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_usize_dec_eq(v_i_596_, v_stop_597_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; 
v___x_600_ = lean_array_uget_borrowed(v_as_595_, v_i_596_);
v___x_601_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_598_, v___x_600_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_596_, v___x_602_);
v_i_596_ = v___x_603_;
v_b_598_ = v___x_601_;
goto _start;
}
else
{
return v_b_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_605_, lean_object* v_i_606_, lean_object* v_stop_607_, lean_object* v_b_608_){
_start:
{
size_t v_i_boxed_609_; size_t v_stop_boxed_610_; lean_object* v_res_611_; 
v_i_boxed_609_ = lean_unbox_usize(v_i_606_);
lean_dec(v_i_606_);
v_stop_boxed_610_ = lean_unbox_usize(v_stop_607_);
lean_dec(v_stop_607_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_605_, v_i_boxed_609_, v_stop_boxed_610_, v_b_608_);
lean_dec_ref(v_as_605_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_612_, lean_object* v_s_613_){
_start:
{
lean_object* v_buckets_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_buckets_614_ = lean_ctor_get(v_s_613_, 1);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_get_size(v_buckets_614_);
v___x_617_ = lean_nat_dec_lt(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
return v_arr_612_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_le(v___x_616_, v___x_616_);
if (v___x_618_ == 0)
{
if (v___x_617_ == 0)
{
return v_arr_612_;
}
else
{
size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v___x_619_ = ((size_t)0ULL);
v___x_620_ = lean_usize_of_nat(v___x_616_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_614_, v___x_619_, v___x_620_, v_arr_612_);
return v___x_621_;
}
}
else
{
size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v___x_622_ = ((size_t)0ULL);
v___x_623_ = lean_usize_of_nat(v___x_616_);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_614_, v___x_622_, v___x_623_, v_arr_612_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_625_, lean_object* v_s_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_625_, v_s_626_);
lean_dec_ref(v_s_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_628_, lean_object* v_numHaves_629_, lean_object* v___x_630_, lean_object* v_a_631_, lean_object* v_b_632_){
_start:
{
lean_object* v_a_635_; uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_lt(v_a_631_, v_upperBound_628_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec(v_a_631_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_b_632_);
return v___x_640_;
}
else
{
uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_641_ = 0;
v___x_642_ = lean_nat_sub(v_numHaves_629_, v_a_631_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_sub(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(v___x_641_);
v___x_646_ = lean_array_get_borrowed(v___x_645_, v_b_632_, v___x_644_);
v___x_647_ = lean_unbox(v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v___x_644_);
v_a_635_ = v_b_632_;
goto v___jp_634_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_typeBackDeps_650_; lean_object* v_valueBackDeps_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_649_ = lean_array_get_borrowed(v___x_648_, v___x_630_, v___x_644_);
lean_dec(v___x_644_);
v_typeBackDeps_650_ = lean_ctor_get(v___x_649_, 0);
v_valueBackDeps_651_ = lean_ctor_get(v___x_649_, 1);
v___x_652_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_632_, v_typeBackDeps_650_);
v___x_653_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_652_, v_valueBackDeps_651_);
v_a_635_ = v___x_653_;
goto v___jp_634_;
}
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_add(v_a_631_, v___x_636_);
lean_dec(v_a_631_);
v_a_631_ = v___x_637_;
v_b_632_ = v_a_635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_654_, lean_object* v_numHaves_655_, lean_object* v___x_656_, lean_object* v_a_657_, lean_object* v_b_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_654_, v_numHaves_655_, v___x_656_, v_a_657_, v_b_658_);
lean_dec_ref(v___x_656_);
lean_dec(v_numHaves_655_);
lean_dec(v_upperBound_654_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_661_, lean_object* v_init_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_haveInfo_668_; lean_object* v_numHaves_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v_used_672_; lean_object* v___x_673_; lean_object* v_used_674_; lean_object* v___x_675_; 
v_haveInfo_668_ = lean_ctor_get(v_info_661_, 0);
v_numHaves_669_ = lean_array_get_size(v_haveInfo_668_);
v___x_670_ = 0;
v___x_671_ = lean_box(v___x_670_);
v_used_672_ = lean_mk_array(v_numHaves_669_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(0u);
v_used_674_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_672_, v_init_662_);
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_669_, v_numHaves_669_, v_haveInfo_668_, v___x_673_, v_used_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_676_, lean_object* v_init_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_676_, v_init_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec_ref(v_init_677_);
lean_dec_ref(v_info_676_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_684_, lean_object* v_numHaves_685_, lean_object* v___x_686_, lean_object* v_inst_687_, lean_object* v_R_688_, lean_object* v_a_689_, lean_object* v_b_690_, lean_object* v_c_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_684_, v_numHaves_685_, v___x_686_, v_a_689_, v_b_690_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_698_, lean_object* v_numHaves_699_, lean_object* v___x_700_, lean_object* v_inst_701_, lean_object* v_R_702_, lean_object* v_a_703_, lean_object* v_b_704_, lean_object* v_c_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_698_, v_numHaves_699_, v___x_700_, v_inst_701_, v_R_702_, v_a_703_, v_b_704_, v_c_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___x_700_);
lean_dec(v_numHaves_699_);
lean_dec(v_upperBound_698_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_714_, uint8_t v_keepUnused_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_bodyDeps_721_; lean_object* v_bodyTypeDeps_722_; lean_object* v___x_723_; 
v_bodyDeps_721_ = lean_ctor_get(v_info_714_, 1);
v_bodyTypeDeps_722_ = lean_ctor_get(v_info_714_, 2);
v___x_723_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_714_, v_bodyTypeDeps_722_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
if (lean_obj_tag(v___x_723_) == 0)
{
if (v_keepUnused_715_ == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_714_, v_bodyDeps_721_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_a_724_);
lean_ctor_set(v___x_730_, 1, v_a_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_a_724_);
v_a_735_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_725_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_725_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_752_; 
v_a_743_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_752_ == 0)
{
v___x_745_ = v___x_723_;
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_723_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_a_743_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_748_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_723_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_723_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_761_, lean_object* v_keepUnused_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
uint8_t v_keepUnused_boxed_768_; lean_object* v_res_769_; 
v_keepUnused_boxed_768_ = lean_unbox(v_keepUnused_762_);
v_res_769_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_761_, v_keepUnused_boxed_768_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec_ref(v_info_761_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0(void){
_start:
{
uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = 0;
v___x_771_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3);
v___x_772_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
lean_ctor_set(v___x_772_, 3, v___x_771_);
lean_ctor_set(v___x_772_, 4, v___x_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*5, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_toApplicative_791_, lean_object* v_level_792_, lean_object* v_exprType_793_, lean_object* v_e_794_, uint8_t v___x_795_, lean_object* v_xs_796_, lean_object* v_____do__lift_797_){
_start:
{
if (lean_obj_tag(v_____do__lift_797_) == 0)
{
lean_object* v_toPure_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_proof_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_toPure_798_ = lean_ctor_get(v_toApplicative_791_, 1);
lean_inc(v_toPure_798_);
lean_dec_ref(v_toApplicative_791_);
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v_level_792_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_mkConst(v___x_799_, v___x_801_);
lean_inc_ref(v_e_794_);
lean_inc_ref(v_exprType_793_);
v_proof_803_ = l_Lean_mkAppB(v___x_802_, v_exprType_793_, v_e_794_);
lean_inc_ref_n(v_e_794_, 2);
v___x_804_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_804_, 0, v_e_794_);
lean_ctor_set(v___x_804_, 1, v_exprType_793_);
lean_ctor_set(v___x_804_, 2, v_e_794_);
lean_ctor_set(v___x_804_, 3, v_e_794_);
lean_ctor_set(v___x_804_, 4, v_proof_803_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*5, v___x_795_);
v___x_805_ = lean_apply_2(v_toPure_798_, lean_box(0), v___x_804_);
return v___x_805_;
}
else
{
lean_object* v_e_806_; lean_object* v_h_807_; lean_object* v_expr_808_; lean_object* v_proof_809_; lean_object* v___x_815_; uint8_t v___x_816_; 
lean_dec(v_level_792_);
v_e_806_ = lean_ctor_get(v_____do__lift_797_, 0);
v_h_807_ = lean_ctor_get(v_____do__lift_797_, 1);
v_expr_808_ = lean_expr_abstract(v_e_806_, v_xs_796_);
v_proof_809_ = lean_expr_abstract(v_h_807_, v_xs_796_);
lean_inc_ref(v_proof_809_);
v___x_815_ = l_Lean_Expr_cleanupAnnotations(v_proof_809_);
v___x_816_ = l_Lean_Expr_isApp(v___x_815_);
if (v___x_816_ == 0)
{
lean_dec_ref(v___x_815_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_arg_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc_ref(v_arg_817_);
v___x_818_ = l_Lean_Expr_appFnCleanup___redArg(v___x_815_);
v___x_819_ = l_Lean_Expr_isApp(v___x_818_);
if (v___x_819_ == 0)
{
lean_dec_ref(v___x_818_);
lean_dec_ref(v_arg_817_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_arg_820_ = lean_ctor_get(v___x_818_, 1);
lean_inc_ref(v_arg_820_);
v___x_821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_818_);
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_823_ = l_Lean_Expr_isConstOf(v___x_821_, v___x_822_);
lean_dec_ref(v___x_821_);
if (v___x_823_ == 0)
{
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
goto v___jp_810_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_825_ = lean_unsigned_to_nat(3u);
v___x_826_ = l_Lean_Expr_isAppOfArity(v_arg_820_, v___x_824_, v___x_825_);
lean_dec_ref(v_arg_820_);
if (v___x_826_ == 0)
{
lean_dec_ref(v_arg_817_);
goto v___jp_810_;
}
else
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = l_Lean_Expr_cleanupAnnotations(v_arg_817_);
v___x_828_ = l_Lean_Expr_isApp(v___x_827_);
if (v___x_828_ == 0)
{
lean_dec_ref(v___x_827_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_arg_829_ = lean_ctor_get(v___x_827_, 1);
lean_inc_ref(v_arg_829_);
v___x_830_ = l_Lean_Expr_appFnCleanup___redArg(v___x_827_);
v___x_831_ = l_Lean_Expr_isApp(v___x_830_);
if (v___x_831_ == 0)
{
lean_dec_ref(v___x_830_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_arg_832_ = lean_ctor_get(v___x_830_, 1);
lean_inc_ref(v_arg_832_);
v___x_833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_830_);
v___x_834_ = l_Lean_Expr_isConstOf(v___x_833_, v___x_822_);
lean_dec_ref(v___x_833_);
if (v___x_834_ == 0)
{
lean_dec_ref(v_arg_832_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = l_Lean_Expr_cleanupAnnotations(v_arg_832_);
v___x_836_ = l_Lean_Expr_isApp(v___x_835_);
if (v___x_836_ == 0)
{
lean_dec_ref(v___x_835_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_arg_837_ = lean_ctor_get(v___x_835_, 1);
lean_inc_ref(v_arg_837_);
v___x_838_ = l_Lean_Expr_appFnCleanup___redArg(v___x_835_);
v___x_839_ = l_Lean_Expr_isApp(v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v___x_838_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_840_; uint8_t v___y_842_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_arg_840_ = lean_ctor_get(v___x_838_, 1);
lean_inc_ref(v_arg_840_);
v___x_846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_838_);
v___x_847_ = l_Lean_Expr_isApp(v___x_846_);
if (v___x_847_ == 0)
{
lean_dec_ref(v___x_846_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_846_);
v___x_849_ = l_Lean_Expr_isConstOf(v___x_848_, v___x_824_);
lean_dec_ref(v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Expr_getAppFn(v_arg_829_);
if (lean_obj_tag(v___x_850_) == 4)
{
lean_object* v_declName_851_; 
v_declName_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_declName_851_);
lean_dec_ref(v___x_850_);
if (lean_obj_tag(v_declName_851_) == 1)
{
lean_object* v_pre_852_; 
v_pre_852_ = lean_ctor_get(v_declName_851_, 0);
if (lean_obj_tag(v_pre_852_) == 0)
{
lean_object* v_str_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_str_853_ = lean_ctor_get(v_declName_851_, 1);
lean_inc_ref(v_str_853_);
lean_dec_ref(v_declName_851_);
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_855_ = lean_string_dec_eq(v_str_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_857_ = lean_string_dec_eq(v_str_853_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_859_ = lean_string_dec_eq(v_str_853_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_861_ = lean_string_dec_eq(v_str_853_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_863_ = lean_string_dec_eq(v_str_853_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_865_ = lean_string_dec_eq(v_str_853_, v___x_864_);
lean_dec_ref(v_str_853_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
v___y_842_ = v___x_823_;
goto v___jp_841_;
}
}
else
{
lean_dec_ref(v_str_853_);
v___y_842_ = v___x_823_;
goto v___jp_841_;
}
}
else
{
lean_dec_ref(v_str_853_);
v___y_842_ = v___x_823_;
goto v___jp_841_;
}
}
else
{
lean_dec_ref(v_str_853_);
v___y_842_ = v___x_823_;
goto v___jp_841_;
}
}
else
{
lean_dec_ref(v_str_853_);
v___y_842_ = v___x_823_;
goto v___jp_841_;
}
}
else
{
lean_dec_ref(v_str_853_);
v___y_842_ = v___x_823_;
goto v___jp_841_;
}
}
else
{
lean_dec_ref(v_declName_851_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
}
else
{
lean_dec(v_declName_851_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
}
else
{
lean_dec_ref(v___x_850_);
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
}
}
v___jp_841_:
{
if (v___y_842_ == 0)
{
lean_dec_ref(v_arg_840_);
lean_dec_ref(v_arg_837_);
lean_dec_ref(v_arg_829_);
goto v___jp_810_;
}
else
{
lean_object* v_toPure_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v_proof_809_);
lean_dec_ref(v_e_794_);
v_toPure_843_ = lean_ctor_get(v_toApplicative_791_, 1);
lean_inc(v_toPure_843_);
lean_dec_ref(v_toApplicative_791_);
v___x_844_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_844_, 0, v_arg_837_);
lean_ctor_set(v___x_844_, 1, v_exprType_793_);
lean_ctor_set(v___x_844_, 2, v_arg_840_);
lean_ctor_set(v___x_844_, 3, v_expr_808_);
lean_ctor_set(v___x_844_, 4, v_arg_829_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*5, v___x_823_);
v___x_845_ = lean_apply_2(v_toPure_843_, lean_box(0), v___x_844_);
return v___x_845_;
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
v___jp_810_:
{
lean_object* v_toPure_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_toPure_811_ = lean_ctor_get(v_toApplicative_791_, 1);
lean_inc(v_toPure_811_);
lean_dec_ref(v_toApplicative_791_);
v___x_812_ = 1;
lean_inc_ref(v_expr_808_);
v___x_813_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_813_, 0, v_expr_808_);
lean_ctor_set(v___x_813_, 1, v_exprType_793_);
lean_ctor_set(v___x_813_, 2, v_e_794_);
lean_ctor_set(v___x_813_, 3, v_expr_808_);
lean_ctor_set(v___x_813_, 4, v_proof_809_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*5, v___x_812_);
v___x_814_ = lean_apply_2(v_toPure_811_, lean_box(0), v___x_813_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_toApplicative_866_, lean_object* v_level_867_, lean_object* v_exprType_868_, lean_object* v_e_869_, lean_object* v___x_870_, lean_object* v_xs_871_, lean_object* v_____do__lift_872_){
_start:
{
uint8_t v___x_10293__boxed_873_; lean_object* v_res_874_; 
v___x_10293__boxed_873_ = lean_unbox(v___x_870_);
v_res_874_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_866_, v_level_867_, v_exprType_868_, v_e_869_, v___x_10293__boxed_873_, v_xs_871_, v_____do__lift_872_);
lean_dec(v_____do__lift_872_);
lean_dec_ref(v_xs_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_875_, lean_object* v_bodyType_876_, lean_object* v_xs_877_, lean_object* v_toApplicative_878_, lean_object* v_level_879_, lean_object* v_e_880_, uint8_t v___x_881_, lean_object* v_body_882_, lean_object* v_toBind_883_, lean_object* v_____r_884_){
_start:
{
lean_object* v_simp_885_; lean_object* v_exprType_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_simp_885_ = lean_ctor_get(v_inst_875_, 2);
lean_inc(v_simp_885_);
lean_dec_ref(v_inst_875_);
v_exprType_886_ = lean_expr_abstract(v_bodyType_876_, v_xs_877_);
v___x_887_ = lean_box(v___x_881_);
v___f_888_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_888_, 0, v_toApplicative_878_);
lean_closure_set(v___f_888_, 1, v_level_879_);
lean_closure_set(v___f_888_, 2, v_exprType_886_);
lean_closure_set(v___f_888_, 3, v_e_880_);
lean_closure_set(v___f_888_, 4, v___x_887_);
lean_closure_set(v___f_888_, 5, v_xs_877_);
v___x_889_ = lean_apply_1(v_simp_885_, v_body_882_);
v___x_890_ = lean_apply_4(v_toBind_883_, lean_box(0), lean_box(0), v___x_889_, v___f_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_891_, lean_object* v_bodyType_892_, lean_object* v_xs_893_, lean_object* v_toApplicative_894_, lean_object* v_level_895_, lean_object* v_e_896_, lean_object* v___x_897_, lean_object* v_body_898_, lean_object* v_toBind_899_, lean_object* v_____r_900_){
_start:
{
uint8_t v___x_10446__boxed_901_; lean_object* v_res_902_; 
v___x_10446__boxed_901_ = lean_unbox(v___x_897_);
v_res_902_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_891_, v_bodyType_892_, v_xs_893_, v_toApplicative_894_, v_level_895_, v_e_896_, v___x_10446__boxed_901_, v_body_898_, v_toBind_899_, v_____r_900_);
lean_dec_ref(v_bodyType_892_);
return v_res_902_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_cls_910_, lean_object* v___x_911_, lean_object* v___f_912_, lean_object* v_body_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_9821__overap_919_; lean_object* v___x_920_; 
lean_inc(v_cls_910_);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
v___x_9821__overap_919_ = l_Lean_isTracingEnabledFor___redArg(v___x_907_, v___x_908_, v___x_909_, v_cls_910_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_920_ = lean_apply_5(v___x_9821__overap_919_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_941_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_941_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_941_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_941_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
uint8_t v___x_925_; 
v___x_925_ = lean_unbox(v_a_921_);
lean_dec(v_a_921_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_body_913_);
lean_dec(v___f_912_);
lean_dec(v___x_911_);
lean_dec(v_cls_910_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___x_926_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_toMonadRef_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_9836__overap_939_; lean_object* v___x_940_; 
lean_del_object(v___x_923_);
v___f_930_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_931_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_932_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_930_, v___x_911_, v___x_931_);
v___x_933_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_930_, v___f_912_, v___x_932_);
v_toMonadRef_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_toMonadRef_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_936_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2);
v___x_937_ = l_Lean_MessageData_ofExpr(v_body_913_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_9836__overap_939_ = l_Lean_addTrace___redArg(v___x_907_, v___x_908_, v_toMonadRef_934_, v___x_935_, v_cls_910_, v___x_938_);
v___x_940_ = lean_apply_5(v___x_9836__overap_939_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_940_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_body_913_);
lean_dec(v___f_912_);
lean_dec(v___x_911_);
lean_dec(v_cls_910_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v_a_942_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_920_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_920_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v___x_950_, lean_object* v___x_951_, lean_object* v___x_952_, lean_object* v_cls_953_, lean_object* v___x_954_, lean_object* v___f_955_, lean_object* v_body_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v___x_950_, v___x_951_, v___x_952_, v_cls_953_, v___x_954_, v___f_955_, v_body_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_965_, lean_object* v_type_966_, lean_object* v___y_967_, lean_object* v_value_968_, uint8_t v_nondep_969_, lean_object* v_toApplicative_970_, lean_object* v___x_971_, uint8_t v___y_972_, lean_object* v_us_973_, lean_object* v_rb_974_){
_start:
{
lean_object* v_expr_975_; lean_object* v_exprType_976_; lean_object* v_exprInit_977_; lean_object* v_exprResult_978_; lean_object* v_proof_979_; uint8_t v_modified_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1009_; 
v_expr_975_ = lean_ctor_get(v_rb_974_, 0);
v_exprType_976_ = lean_ctor_get(v_rb_974_, 1);
v_exprInit_977_ = lean_ctor_get(v_rb_974_, 2);
v_exprResult_978_ = lean_ctor_get(v_rb_974_, 3);
v_proof_979_ = lean_ctor_get(v_rb_974_, 4);
v_modified_980_ = lean_ctor_get_uint8(v_rb_974_, sizeof(void*)*5);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_rb_974_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_982_ = v_rb_974_;
v_isShared_983_ = v_isSharedCheck_1009_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_proof_979_);
lean_inc(v_exprResult_978_);
lean_inc(v_exprInit_977_);
lean_inc(v_exprType_976_);
lean_inc(v_expr_975_);
lean_dec(v_rb_974_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1009_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v_expr_986_; lean_object* v___x_987_; lean_object* v_exprType_988_; lean_object* v___x_989_; lean_object* v_exprInit_990_; lean_object* v_exprResult_991_; 
v___x_984_ = 0;
lean_inc_ref(v_type_966_);
lean_inc(v_declName_965_);
v___x_985_ = l_Lean_mkLambda(v_declName_965_, v___x_984_, v_type_966_, v_expr_975_);
lean_inc_ref(v___y_967_);
lean_inc_ref(v___x_985_);
v_expr_986_ = l_Lean_Expr_app___override(v___x_985_, v___y_967_);
lean_inc_ref(v_type_966_);
lean_inc(v_declName_965_);
v___x_987_ = l_Lean_mkLambda(v_declName_965_, v___x_984_, v_type_966_, v_exprType_976_);
lean_inc_ref(v___y_967_);
lean_inc_ref(v___x_987_);
v_exprType_988_ = l_Lean_Expr_app___override(v___x_987_, v___y_967_);
lean_inc_ref(v_type_966_);
lean_inc(v_declName_965_);
v___x_989_ = l_Lean_mkLambda(v_declName_965_, v___x_984_, v_type_966_, v_exprInit_977_);
lean_inc_ref(v___x_989_);
v_exprInit_990_ = l_Lean_Expr_app___override(v___x_989_, v_value_968_);
lean_inc_ref(v___y_967_);
lean_inc_ref(v_type_966_);
lean_inc(v_declName_965_);
v_exprResult_991_ = l_Lean_Expr_letE___override(v_declName_965_, v_type_966_, v___y_967_, v_exprResult_978_, v_nondep_969_);
if (v_modified_980_ == 0)
{
lean_object* v_toPure_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_proof_995_; lean_object* v___x_997_; 
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v_proof_979_);
lean_dec(v_us_973_);
lean_dec_ref(v___y_967_);
lean_dec_ref(v_type_966_);
lean_dec(v_declName_965_);
v_toPure_992_ = lean_ctor_get(v_toApplicative_970_, 1);
lean_inc(v_toPure_992_);
lean_dec_ref(v_toApplicative_970_);
v___x_993_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_994_ = l_Lean_mkConst(v___x_993_, v___x_971_);
lean_inc_ref(v_expr_986_);
lean_inc_ref(v_exprType_988_);
v_proof_995_ = l_Lean_mkAppB(v___x_994_, v_exprType_988_, v_expr_986_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v_proof_995_);
lean_ctor_set(v___x_982_, 3, v_exprResult_991_);
lean_ctor_set(v___x_982_, 2, v_exprInit_990_);
lean_ctor_set(v___x_982_, 1, v_exprType_988_);
lean_ctor_set(v___x_982_, 0, v_expr_986_);
v___x_997_ = v___x_982_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_expr_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_exprType_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_exprInit_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_exprResult_991_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_proof_995_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; 
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*5, v___y_972_);
v___x_998_ = lean_apply_2(v_toPure_992_, lean_box(0), v___x_997_);
return v___x_998_;
}
}
else
{
lean_object* v_toPure_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_proof_1004_; lean_object* v___x_1006_; 
lean_dec(v___x_971_);
v_toPure_1000_ = lean_ctor_get(v_toApplicative_970_, 1);
lean_inc(v_toPure_1000_);
lean_dec_ref(v_toApplicative_970_);
lean_inc_ref(v_type_966_);
v___x_1001_ = l_Lean_mkLambda(v_declName_965_, v___x_984_, v_type_966_, v_proof_979_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_1003_ = l_Lean_mkConst(v___x_1002_, v_us_973_);
v_proof_1004_ = l_Lean_mkApp6(v___x_1003_, v_type_966_, v___x_987_, v___y_967_, v___x_989_, v___x_985_, v___x_1001_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v_proof_1004_);
lean_ctor_set(v___x_982_, 3, v_exprResult_991_);
lean_ctor_set(v___x_982_, 2, v_exprInit_990_);
lean_ctor_set(v___x_982_, 1, v_exprType_988_);
lean_ctor_set(v___x_982_, 0, v_expr_986_);
v___x_1006_ = v___x_982_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_expr_986_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_exprType_988_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_exprInit_990_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_exprResult_991_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_proof_1004_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*5, v_nondep_969_);
v___x_1007_ = lean_apply_2(v_toPure_1000_, lean_box(0), v___x_1006_);
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_1010_, lean_object* v_type_1011_, lean_object* v___y_1012_, lean_object* v_value_1013_, lean_object* v_nondep_1014_, lean_object* v_toApplicative_1015_, lean_object* v___x_1016_, lean_object* v___y_1017_, lean_object* v_us_1018_, lean_object* v_rb_1019_){
_start:
{
uint8_t v_nondep_10577__boxed_1020_; uint8_t v___y_10579__boxed_1021_; lean_object* v_res_1022_; 
v_nondep_10577__boxed_1020_ = lean_unbox(v_nondep_1014_);
v___y_10579__boxed_1021_ = lean_unbox(v___y_1017_);
v_res_1022_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_1010_, v_type_1011_, v___y_1012_, v_value_1013_, v_nondep_10577__boxed_1020_, v_toApplicative_1015_, v___x_1016_, v___y_10579__boxed_1021_, v_us_1018_, v_rb_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1023_, lean_object* v_____x_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_apply_1(v___f_1023_, v_____x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1030_, lean_object* v_declName_1031_, lean_object* v_type_1032_, lean_object* v_value_1033_, lean_object* v_us_1034_, lean_object* v___x_1035_, lean_object* v_toApplicative_1036_, uint8_t v_nondep_1037_, lean_object* v_rb_1038_){
_start:
{
lean_object* v_expr_1039_; lean_object* v_exprType_1040_; lean_object* v_exprInit_1041_; lean_object* v_exprResult_1042_; lean_object* v_proof_1043_; uint8_t v_modified_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1074_; 
v_expr_1039_ = lean_ctor_get(v_rb_1038_, 0);
v_exprType_1040_ = lean_ctor_get(v_rb_1038_, 1);
v_exprInit_1041_ = lean_ctor_get(v_rb_1038_, 2);
v_exprResult_1042_ = lean_ctor_get(v_rb_1038_, 3);
v_proof_1043_ = lean_ctor_get(v_rb_1038_, 4);
v_modified_1044_ = lean_ctor_get_uint8(v_rb_1038_, sizeof(void*)*5);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_rb_1038_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1046_ = v_rb_1038_;
v_isShared_1047_ = v_isSharedCheck_1074_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_proof_1043_);
lean_inc(v_exprResult_1042_);
lean_inc(v_exprInit_1041_);
lean_inc(v_exprType_1040_);
lean_inc(v_expr_1039_);
lean_dec(v_rb_1038_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1074_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_expr_1048_; lean_object* v_exprType_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v_exprInit_1052_; lean_object* v_exprResult_1053_; 
v_expr_1048_ = lean_expr_lower_loose_bvars(v_expr_1039_, v___x_1030_, v___x_1030_);
lean_dec_ref(v_expr_1039_);
v_exprType_1049_ = lean_expr_lower_loose_bvars(v_exprType_1040_, v___x_1030_, v___x_1030_);
lean_dec_ref(v_exprType_1040_);
v___x_1050_ = 0;
lean_inc_ref(v_type_1032_);
lean_inc(v_declName_1031_);
v___x_1051_ = l_Lean_mkLambda(v_declName_1031_, v___x_1050_, v_type_1032_, v_exprInit_1041_);
lean_inc_ref(v_value_1033_);
lean_inc_ref(v___x_1051_);
v_exprInit_1052_ = l_Lean_Expr_app___override(v___x_1051_, v_value_1033_);
v_exprResult_1053_ = lean_expr_lower_loose_bvars(v_exprResult_1042_, v___x_1030_, v___x_1030_);
lean_dec_ref(v_exprResult_1042_);
if (v_modified_1044_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_proof_1059_; lean_object* v_toPure_1060_; lean_object* v___x_1062_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v_proof_1043_);
lean_dec(v_declName_1031_);
v___x_1054_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1055_ = l_Lean_mkConst(v___x_1054_, v_us_1034_);
v___x_1056_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1057_ = l_Lean_mkConst(v___x_1056_, v___x_1035_);
lean_inc_ref(v_expr_1048_);
lean_inc_ref(v_exprType_1049_);
v___x_1058_ = l_Lean_mkAppB(v___x_1057_, v_exprType_1049_, v_expr_1048_);
lean_inc_ref_n(v_expr_1048_, 2);
lean_inc_ref(v_exprType_1049_);
v_proof_1059_ = l_Lean_mkApp6(v___x_1055_, v_type_1032_, v_exprType_1049_, v_value_1033_, v_expr_1048_, v_expr_1048_, v___x_1058_);
v_toPure_1060_ = lean_ctor_get(v_toApplicative_1036_, 1);
lean_inc(v_toPure_1060_);
lean_dec_ref(v_toApplicative_1036_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v_proof_1059_);
lean_ctor_set(v___x_1046_, 3, v_exprResult_1053_);
lean_ctor_set(v___x_1046_, 2, v_exprInit_1052_);
lean_ctor_set(v___x_1046_, 1, v_exprType_1049_);
lean_ctor_set(v___x_1046_, 0, v_expr_1048_);
v___x_1062_ = v___x_1046_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_expr_1048_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_exprType_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_exprInit_1052_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_exprResult_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_proof_1059_);
v___x_1062_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; 
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*5, v_nondep_1037_);
v___x_1063_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1062_);
return v___x_1063_;
}
}
else
{
lean_object* v_toPure_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_proof_1069_; lean_object* v___x_1071_; 
lean_dec(v___x_1035_);
v_toPure_1065_ = lean_ctor_get(v_toApplicative_1036_, 1);
lean_inc(v_toPure_1065_);
lean_dec_ref(v_toApplicative_1036_);
lean_inc_ref(v_type_1032_);
v___x_1066_ = l_Lean_mkLambda(v_declName_1031_, v___x_1050_, v_type_1032_, v_proof_1043_);
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1068_ = l_Lean_mkConst(v___x_1067_, v_us_1034_);
lean_inc_ref(v_expr_1048_);
lean_inc_ref(v_exprType_1049_);
v_proof_1069_ = l_Lean_mkApp6(v___x_1068_, v_type_1032_, v_exprType_1049_, v_value_1033_, v___x_1051_, v_expr_1048_, v___x_1066_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v_proof_1069_);
lean_ctor_set(v___x_1046_, 3, v_exprResult_1053_);
lean_ctor_set(v___x_1046_, 2, v_exprInit_1052_);
lean_ctor_set(v___x_1046_, 1, v_exprType_1049_);
lean_ctor_set(v___x_1046_, 0, v_expr_1048_);
v___x_1071_ = v___x_1046_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_expr_1048_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_exprType_1049_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_exprInit_1052_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_exprResult_1053_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_proof_1069_);
v___x_1071_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*5, v_nondep_1037_);
v___x_1072_ = lean_apply_2(v_toPure_1065_, lean_box(0), v___x_1071_);
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1075_, lean_object* v_declName_1076_, lean_object* v_type_1077_, lean_object* v_value_1078_, lean_object* v_us_1079_, lean_object* v___x_1080_, lean_object* v_toApplicative_1081_, lean_object* v_nondep_1082_, lean_object* v_rb_1083_){
_start:
{
uint8_t v_nondep_10664__boxed_1084_; lean_object* v_res_1085_; 
v_nondep_10664__boxed_1084_ = lean_unbox(v_nondep_1082_);
v_res_1085_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1075_, v_declName_1076_, v_type_1077_, v_value_1078_, v_us_1079_, v___x_1080_, v_toApplicative_1081_, v_nondep_10664__boxed_1084_, v_rb_1083_);
lean_dec(v___x_1075_);
return v_res_1085_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v_cls_1095_, lean_object* v___x_1096_, lean_object* v___f_1097_, lean_object* v_declName_1098_, lean_object* v_val_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_10236__overap_1105_; lean_object* v___x_1106_; 
lean_inc(v_cls_1095_);
lean_inc_ref(v___x_1093_);
lean_inc_ref(v___x_1092_);
v___x_10236__overap_1105_ = l_Lean_isTracingEnabledFor___redArg(v___x_1092_, v___x_1093_, v___x_1094_, v_cls_1095_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
v___x_1106_ = lean_apply_5(v___x_10236__overap_1105_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1131_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1131_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_unbox(v_a_1107_);
lean_dec(v_a_1107_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec_ref(v_val_1099_);
lean_dec(v_declName_1098_);
lean_dec(v___f_1097_);
lean_dec(v___x_1096_);
lean_dec(v_cls_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v___x_1092_);
v___x_1112_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
else
{
lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_toMonadRef_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_10256__overap_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_1109_);
v___f_1116_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_1117_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1118_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1116_, v___x_1096_, v___x_1117_);
v___x_1119_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1116_, v___f_1097_, v___x_1118_);
v_toMonadRef_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref(v_toMonadRef_1120_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1122_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1123_ = l_Lean_MessageData_ofName(v_declName_1098_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_MessageData_ofExpr(v_val_1099_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_10256__overap_1129_ = l_Lean_addTrace___redArg(v___x_1092_, v___x_1093_, v_toMonadRef_1120_, v___x_1121_, v_cls_1095_, v___x_1128_);
v___x_1130_ = lean_apply_5(v___x_10256__overap_1129_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
return v___x_1130_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec_ref(v_val_1099_);
lean_dec(v_declName_1098_);
lean_dec(v___f_1097_);
lean_dec(v___x_1096_);
lean_dec(v_cls_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v___x_1092_);
v_a_1132_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1106_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1106_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v_cls_1143_, lean_object* v___x_1144_, lean_object* v___f_1145_, lean_object* v_declName_1146_, lean_object* v_val_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v___x_1140_, v___x_1141_, v___x_1142_, v_cls_1143_, v___x_1144_, v___f_1145_, v_declName_1146_, v_val_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v_res_1153_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v___x_1160_, lean_object* v___x_1161_, lean_object* v___x_1162_, lean_object* v_cls_1163_, lean_object* v___x_1164_, lean_object* v___f_1165_, lean_object* v_declName_1166_, lean_object* v_val_1167_, lean_object* v_val_x27_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_9905__overap_1174_; lean_object* v___x_1175_; 
lean_inc(v_cls_1163_);
lean_inc_ref(v___x_1161_);
lean_inc_ref(v___x_1160_);
v___x_9905__overap_1174_ = l_Lean_isTracingEnabledFor___redArg(v___x_1160_, v___x_1161_, v___x_1162_, v_cls_1163_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc(v___y_1170_);
lean_inc_ref(v___y_1169_);
v___x_1175_ = lean_apply_5(v___x_9905__overap_1174_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, lean_box(0));
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1204_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_unbox(v_a_1176_);
lean_dec(v_a_1176_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_val_x27_1168_);
lean_dec_ref(v_val_1167_);
lean_dec(v_declName_1166_);
lean_dec(v___f_1165_);
lean_dec(v___x_1164_);
lean_dec(v_cls_1163_);
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1160_);
v___x_1181_ = lean_box(0);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_toMonadRef_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_9930__overap_1202_; lean_object* v___x_1203_; 
lean_del_object(v___x_1178_);
v___f_1185_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_1186_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1187_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1185_, v___x_1164_, v___x_1186_);
v___x_1188_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1185_, v___f_1165_, v___x_1187_);
v_toMonadRef_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_toMonadRef_1189_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1191_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1192_ = l_Lean_MessageData_ofName(v_declName_1166_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_MessageData_ofExpr(v_val_1167_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_MessageData_ofExpr(v_val_x27_1168_);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_9930__overap_1202_ = l_Lean_addTrace___redArg(v___x_1160_, v___x_1161_, v_toMonadRef_1189_, v___x_1190_, v_cls_1163_, v___x_1201_);
v___x_1203_ = lean_apply_5(v___x_9930__overap_1202_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, lean_box(0));
return v___x_1203_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_val_x27_1168_);
lean_dec_ref(v_val_1167_);
lean_dec(v_declName_1166_);
lean_dec(v___f_1165_);
lean_dec(v___x_1164_);
lean_dec(v_cls_1163_);
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1160_);
v_a_1205_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1175_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1175_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v_cls_1216_, lean_object* v___x_1217_, lean_object* v___f_1218_, lean_object* v_declName_1219_, lean_object* v_val_1220_, lean_object* v_val_x27_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v___x_1213_, v___x_1214_, v___x_1215_, v_cls_1216_, v___x_1217_, v___f_1218_, v_declName_1219_, v_val_1220_, v_val_x27_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_toApplicative_1228_, lean_object* v_e_1229_, lean_object* v_xs_1230_, lean_object* v_h_1231_, uint8_t v_nondep_1232_, lean_object* v_toBind_1233_, lean_object* v___f_1234_, lean_object* v_____r_1235_){
_start:
{
lean_object* v_toPure_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_toPure_1236_ = lean_ctor_get(v_toApplicative_1228_, 1);
lean_inc(v_toPure_1236_);
lean_dec_ref(v_toApplicative_1228_);
v___x_1237_ = lean_expr_abstract(v_e_1229_, v_xs_1230_);
v___x_1238_ = lean_expr_abstract(v_h_1231_, v_xs_1230_);
v___x_1239_ = lean_box(v_nondep_1232_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_apply_2(v_toPure_1236_, lean_box(0), v___x_1241_);
v___x_1243_ = lean_apply_4(v_toBind_1233_, lean_box(0), lean_box(0), v___x_1242_, v___f_1234_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_toApplicative_1244_, lean_object* v_e_1245_, lean_object* v_xs_1246_, lean_object* v_h_1247_, lean_object* v_nondep_1248_, lean_object* v_toBind_1249_, lean_object* v___f_1250_, lean_object* v_____r_1251_){
_start:
{
uint8_t v_nondep_10976__boxed_1252_; lean_object* v_res_1253_; 
v_nondep_10976__boxed_1252_ = lean_unbox(v_nondep_1248_);
v_res_1253_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1244_, v_e_1245_, v_xs_1246_, v_h_1247_, v_nondep_10976__boxed_1252_, v_toBind_1249_, v___f_1250_, v_____r_1251_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_xs_1246_);
lean_dec_ref(v_e_1245_);
return v_res_1253_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v_cls_1260_, lean_object* v___x_1261_, lean_object* v___f_1262_, lean_object* v_declName_1263_, lean_object* v_val_1264_, lean_object* v_e_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_10089__overap_1271_; lean_object* v___x_1272_; 
lean_inc(v_cls_1260_);
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
v___x_10089__overap_1271_ = l_Lean_isTracingEnabledFor___redArg(v___x_1257_, v___x_1258_, v___x_1259_, v_cls_1260_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
v___x_1272_ = lean_apply_5(v___x_10089__overap_1271_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, lean_box(0));
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1301_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1301_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1301_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec_ref(v_e_1265_);
lean_dec_ref(v_val_1264_);
lean_dec(v_declName_1263_);
lean_dec(v___f_1262_);
lean_dec(v___x_1261_);
lean_dec(v_cls_1260_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
v___x_1278_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1280_ = v___x_1275_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
else
{
lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_toMonadRef_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_10114__overap_1299_; lean_object* v___x_1300_; 
lean_del_object(v___x_1275_);
v___f_1282_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_1283_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1284_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1282_, v___x_1261_, v___x_1283_);
v___x_1285_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1282_, v___f_1262_, v___x_1284_);
v_toMonadRef_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc_ref(v_toMonadRef_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1289_ = l_Lean_MessageData_ofName(v_declName_1263_);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = l_Lean_MessageData_ofExpr(v_val_1264_);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_MessageData_ofExpr(v_e_1265_);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_10114__overap_1299_ = l_Lean_addTrace___redArg(v___x_1257_, v___x_1258_, v_toMonadRef_1286_, v___x_1287_, v_cls_1260_, v___x_1298_);
v___x_1300_ = lean_apply_5(v___x_10114__overap_1299_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, lean_box(0));
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec_ref(v_e_1265_);
lean_dec_ref(v_val_1264_);
lean_dec(v_declName_1263_);
lean_dec(v___f_1262_);
lean_dec(v___x_1261_);
lean_dec(v_cls_1260_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1257_);
v_a_1302_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1272_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1272_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v_cls_1313_, lean_object* v___x_1314_, lean_object* v___f_1315_, lean_object* v_declName_1316_, lean_object* v_val_1317_, lean_object* v_e_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v___x_1310_, v___x_1311_, v___x_1312_, v_cls_1313_, v___x_1314_, v___f_1315_, v_declName_1316_, v_val_1317_, v_e_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
return v_res_1324_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
v___x_1327_ = l_ReaderT_instMonad___redArg(v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1344_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1345_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1344_, v___x_1343_);
return v___x_1345_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
v___f_1347_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1348_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1347_, v___x_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_toApplicative_1354_, lean_object* v_level_1355_, lean_object* v___x_1356_, lean_object* v_type_1357_, lean_object* v_value_1358_, uint8_t v___x_1359_, lean_object* v_toBind_1360_, lean_object* v___f_1361_, lean_object* v_xs_1362_, uint8_t v_nondep_1363_, lean_object* v___f_1364_, lean_object* v_declName_1365_, lean_object* v_val_1366_, lean_object* v_inst_1367_, lean_object* v_____do__lift_1368_){
_start:
{
if (lean_obj_tag(v_____do__lift_1368_) == 0)
{
lean_object* v_toPure_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_inst_1367_);
lean_dec_ref(v_val_1366_);
lean_dec(v_declName_1365_);
lean_dec(v___f_1364_);
lean_dec_ref(v_xs_1362_);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1354_, 1);
lean_inc(v_toPure_1369_);
lean_dec_ref(v_toApplicative_1354_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_level_1355_);
lean_ctor_set(v___x_1371_, 1, v___x_1356_);
v___x_1372_ = l_Lean_mkConst(v___x_1370_, v___x_1371_);
lean_inc_ref(v_value_1358_);
v___x_1373_ = l_Lean_mkAppB(v___x_1372_, v_type_1357_, v_value_1358_);
v___x_1374_ = lean_box(v___x_1359_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_value_1358_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_apply_2(v_toPure_1369_, lean_box(0), v___x_1376_);
v___x_1378_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1377_, v___f_1361_);
return v___x_1378_;
}
else
{
lean_object* v_e_1379_; lean_object* v_h_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v___f_1361_);
lean_dec_ref(v_value_1358_);
lean_dec_ref(v_type_1357_);
lean_dec(v___x_1356_);
lean_dec(v_level_1355_);
v_e_1379_ = lean_ctor_get(v_____do__lift_1368_, 0);
v_h_1380_ = lean_ctor_get(v_____do__lift_1368_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_____do__lift_1368_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1382_ = v_____do__lift_1368_;
v_isShared_1383_ = v_isSharedCheck_1456_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_h_1380_);
lean_inc(v_e_1379_);
lean_dec(v_____do__lift_1368_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1456_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v_toApplicative_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1454_; 
v___x_1384_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1384_, 1);
lean_dec(v_unused_1455_);
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1454_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_toApplicative_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1454_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_toFunctor_1389_; lean_object* v_toSeq_1390_; lean_object* v_toSeqLeft_1391_; lean_object* v_toSeqRight_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1452_; 
v_toFunctor_1389_ = lean_ctor_get(v_toApplicative_1385_, 0);
v_toSeq_1390_ = lean_ctor_get(v_toApplicative_1385_, 2);
v_toSeqLeft_1391_ = lean_ctor_get(v_toApplicative_1385_, 3);
v_toSeqRight_1392_ = lean_ctor_get(v_toApplicative_1385_, 4);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_toApplicative_1385_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_toApplicative_1385_, 1);
lean_dec(v_unused_1453_);
v___x_1394_ = v_toApplicative_1385_;
v_isShared_1395_ = v_isSharedCheck_1452_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_toSeqRight_1392_);
lean_inc(v_toSeqLeft_1391_);
lean_inc(v_toSeq_1390_);
lean_inc(v_toFunctor_1389_);
lean_dec(v_toApplicative_1385_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1452_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___f_1396_; lean_object* v___f_1397_; lean_object* v___f_1398_; lean_object* v___f_1399_; lean_object* v___x_1401_; 
v___f_1396_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1397_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_1389_);
v___f_1398_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1398_, 0, v_toFunctor_1389_);
v___f_1399_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1399_, 0, v_toFunctor_1389_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 0);
lean_ctor_set(v___x_1382_, 1, v___f_1399_);
lean_ctor_set(v___x_1382_, 0, v___f_1398_);
v___x_1401_ = v___x_1382_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___f_1398_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___f_1399_);
v___x_1401_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___f_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___x_1406_; 
v___f_1402_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1402_, 0, v_toSeqRight_1392_);
v___f_1403_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1403_, 0, v_toSeqLeft_1391_);
v___f_1404_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1404_, 0, v_toSeq_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 4, v___f_1402_);
lean_ctor_set(v___x_1394_, 3, v___f_1403_);
lean_ctor_set(v___x_1394_, 2, v___f_1404_);
lean_ctor_set(v___x_1394_, 1, v___f_1396_);
lean_ctor_set(v___x_1394_, 0, v___x_1401_);
v___x_1406_ = v___x_1394_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___f_1396_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v___f_1404_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v___f_1403_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v___f_1402_);
v___x_1406_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___f_1397_);
lean_ctor_set(v___x_1387_, 0, v___x_1406_);
v___x_1408_ = v___x_1387_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___f_1397_);
v___x_1408_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v_toApplicative_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1447_; 
v___x_1409_ = l_ReaderT_instMonad___redArg(v___x_1408_);
v_toApplicative_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v___x_1409_, 1);
lean_dec(v_unused_1448_);
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1447_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_toApplicative_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1447_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_toFunctor_1414_; lean_object* v_toSeq_1415_; lean_object* v_toSeqLeft_1416_; lean_object* v_toSeqRight_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1445_; 
v_toFunctor_1414_ = lean_ctor_get(v_toApplicative_1410_, 0);
v_toSeq_1415_ = lean_ctor_get(v_toApplicative_1410_, 2);
v_toSeqLeft_1416_ = lean_ctor_get(v_toApplicative_1410_, 3);
v_toSeqRight_1417_ = lean_ctor_get(v_toApplicative_1410_, 4);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_toApplicative_1410_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v_toApplicative_1410_, 1);
lean_dec(v_unused_1446_);
v___x_1419_ = v_toApplicative_1410_;
v_isShared_1420_ = v_isSharedCheck_1445_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_toSeqRight_1417_);
lean_inc(v_toSeqLeft_1416_);
lean_inc(v_toSeq_1415_);
lean_inc(v_toFunctor_1414_);
lean_dec(v_toApplicative_1410_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1445_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v_cls_1423_; lean_object* v___f_1424_; lean_object* v___f_1425_; lean_object* v___f_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; lean_object* v___f_1430_; lean_object* v___f_1431_; lean_object* v___x_1433_; 
v___x_1421_ = lean_box(v_nondep_1363_);
lean_inc(v_toBind_1360_);
lean_inc_ref(v_e_1379_);
v___f_1422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1422_, 0, v_toApplicative_1354_);
lean_closure_set(v___f_1422_, 1, v_e_1379_);
lean_closure_set(v___f_1422_, 2, v_xs_1362_);
lean_closure_set(v___f_1422_, 3, v_h_1380_);
lean_closure_set(v___f_1422_, 4, v___x_1421_);
lean_closure_set(v___f_1422_, 5, v_toBind_1360_);
lean_closure_set(v___f_1422_, 6, v___f_1364_);
v_cls_1423_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1424_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1425_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1414_);
v___f_1426_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1426_, 0, v_toFunctor_1414_);
v___f_1427_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1427_, 0, v_toFunctor_1414_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___f_1426_);
lean_ctor_set(v___x_1428_, 1, v___f_1427_);
v___f_1429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1429_, 0, v_toSeqRight_1417_);
v___f_1430_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1430_, 0, v_toSeqLeft_1416_);
v___f_1431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1431_, 0, v_toSeq_1415_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 4, v___f_1429_);
lean_ctor_set(v___x_1419_, 3, v___f_1430_);
lean_ctor_set(v___x_1419_, 2, v___f_1431_);
lean_ctor_set(v___x_1419_, 1, v___f_1424_);
lean_ctor_set(v___x_1419_, 0, v___x_1428_);
v___x_1433_ = v___x_1419_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___f_1424_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v___f_1431_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v___f_1430_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v___f_1429_);
v___x_1433_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___f_1425_);
lean_ctor_set(v___x_1412_, 0, v___x_1433_);
v___x_1435_ = v___x_1412_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___f_1425_);
v___x_1435_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___f_1436_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1437_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1438_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_1439_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_1440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 14, 9);
lean_closure_set(v___f_1440_, 0, v___x_1435_);
lean_closure_set(v___f_1440_, 1, v___x_1438_);
lean_closure_set(v___f_1440_, 2, v___x_1439_);
lean_closure_set(v___f_1440_, 3, v_cls_1423_);
lean_closure_set(v___f_1440_, 4, v___x_1437_);
lean_closure_set(v___f_1440_, 5, v___f_1436_);
lean_closure_set(v___f_1440_, 6, v_declName_1365_);
lean_closure_set(v___f_1440_, 7, v_val_1366_);
lean_closure_set(v___f_1440_, 8, v_e_1379_);
v___x_1441_ = lean_apply_2(v_inst_1367_, lean_box(0), v___f_1440_);
v___x_1442_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1441_, v___f_1422_);
return v___x_1442_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object* v_toApplicative_1457_, lean_object* v_level_1458_, lean_object* v___x_1459_, lean_object* v_type_1460_, lean_object* v_value_1461_, lean_object* v___x_1462_, lean_object* v_toBind_1463_, lean_object* v___f_1464_, lean_object* v_xs_1465_, lean_object* v_nondep_1466_, lean_object* v___f_1467_, lean_object* v_declName_1468_, lean_object* v_val_1469_, lean_object* v_inst_1470_, lean_object* v_____do__lift_1471_){
_start:
{
uint8_t v___x_11196__boxed_1472_; uint8_t v_nondep_11198__boxed_1473_; lean_object* v_res_1474_; 
v___x_11196__boxed_1472_ = lean_unbox(v___x_1462_);
v_nondep_11198__boxed_1473_ = lean_unbox(v_nondep_1466_);
v_res_1474_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1457_, v_level_1458_, v___x_1459_, v_type_1460_, v_value_1461_, v___x_11196__boxed_1472_, v_toBind_1463_, v___f_1464_, v_xs_1465_, v_nondep_11198__boxed_1473_, v___f_1467_, v_declName_1468_, v_val_1469_, v_inst_1470_, v_____do__lift_1471_);
return v_res_1474_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1485_ = lean_unsigned_to_nat(8u);
v___x_1486_ = lean_unsigned_to_nat(287u);
v___x_1487_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1488_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1489_ = l_mkPanicMessageWithDecl(v___x_1488_, v___x_1487_, v___x_1486_, v___x_1485_, v___x_1484_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1490_, lean_object* v_type_1491_, lean_object* v_fst_1492_, lean_object* v___x_1493_, lean_object* v_value_1494_, uint8_t v_nondep_1495_, uint8_t v_fst_1496_, lean_object* v_toApplicative_1497_, lean_object* v___x_1498_, lean_object* v_us_1499_, lean_object* v_snd_1500_, lean_object* v_inst_1501_, lean_object* v_rb_1502_){
_start:
{
lean_object* v_expr_1503_; lean_object* v_exprType_1504_; lean_object* v_exprInit_1505_; lean_object* v_exprResult_1506_; lean_object* v_proof_1507_; uint8_t v_modified_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1559_; 
v_expr_1503_ = lean_ctor_get(v_rb_1502_, 0);
v_exprType_1504_ = lean_ctor_get(v_rb_1502_, 1);
v_exprInit_1505_ = lean_ctor_get(v_rb_1502_, 2);
v_exprResult_1506_ = lean_ctor_get(v_rb_1502_, 3);
v_proof_1507_ = lean_ctor_get(v_rb_1502_, 4);
v_modified_1508_ = lean_ctor_get_uint8(v_rb_1502_, sizeof(void*)*5);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_rb_1502_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1510_ = v_rb_1502_;
v_isShared_1511_ = v_isSharedCheck_1559_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_proof_1507_);
lean_inc(v_exprResult_1506_);
lean_inc(v_exprInit_1505_);
lean_inc(v_exprType_1504_);
lean_inc(v_expr_1503_);
lean_dec(v_rb_1502_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1559_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_expr_has_loose_bvar(v_exprType_1504_, v___x_1512_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v_expr_1516_; lean_object* v_exprType_1517_; lean_object* v___x_1518_; lean_object* v_exprInit_1519_; lean_object* v_exprResult_1520_; 
lean_dec_ref(v_inst_1501_);
v___x_1514_ = 0;
lean_inc_ref(v_type_1491_);
lean_inc(v_declName_1490_);
v___x_1515_ = l_Lean_mkLambda(v_declName_1490_, v___x_1514_, v_type_1491_, v_expr_1503_);
lean_inc_ref(v_fst_1492_);
lean_inc_ref(v___x_1515_);
v_expr_1516_ = l_Lean_Expr_app___override(v___x_1515_, v_fst_1492_);
v_exprType_1517_ = lean_expr_lower_loose_bvars(v_exprType_1504_, v___x_1493_, v___x_1493_);
lean_dec_ref(v_exprType_1504_);
lean_inc_ref(v_type_1491_);
lean_inc(v_declName_1490_);
v___x_1518_ = l_Lean_mkLambda(v_declName_1490_, v___x_1514_, v_type_1491_, v_exprInit_1505_);
lean_inc_ref(v_value_1494_);
lean_inc_ref(v___x_1518_);
v_exprInit_1519_ = l_Lean_Expr_app___override(v___x_1518_, v_value_1494_);
lean_inc_ref(v_fst_1492_);
lean_inc_ref(v_type_1491_);
lean_inc(v_declName_1490_);
v_exprResult_1520_ = l_Lean_Expr_letE___override(v_declName_1490_, v_type_1491_, v_fst_1492_, v_exprResult_1506_, v_nondep_1495_);
if (v_fst_1496_ == 0)
{
lean_dec_ref(v_snd_1500_);
lean_dec_ref(v_fst_1492_);
if (v_modified_1508_ == 0)
{
lean_object* v_toPure_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_proof_1524_; lean_object* v___x_1526_; 
lean_dec_ref(v___x_1518_);
lean_dec_ref(v___x_1515_);
lean_dec_ref(v_proof_1507_);
lean_dec(v_us_1499_);
lean_dec_ref(v_value_1494_);
lean_dec_ref(v_type_1491_);
lean_dec(v_declName_1490_);
v_toPure_1521_ = lean_ctor_get(v_toApplicative_1497_, 1);
lean_inc(v_toPure_1521_);
lean_dec_ref(v_toApplicative_1497_);
v___x_1522_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1523_ = l_Lean_mkConst(v___x_1522_, v___x_1498_);
lean_inc_ref(v_expr_1516_);
lean_inc_ref(v_exprType_1517_);
v_proof_1524_ = l_Lean_mkAppB(v___x_1523_, v_exprType_1517_, v_expr_1516_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_proof_1524_);
lean_ctor_set(v___x_1510_, 3, v_exprResult_1520_);
lean_ctor_set(v___x_1510_, 2, v_exprInit_1519_);
lean_ctor_set(v___x_1510_, 1, v_exprType_1517_);
lean_ctor_set(v___x_1510_, 0, v_expr_1516_);
v___x_1526_ = v___x_1510_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_expr_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_exprType_1517_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_exprInit_1519_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_exprResult_1520_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_proof_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*5, v_modified_1508_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_apply_2(v_toPure_1521_, lean_box(0), v___x_1526_);
return v___x_1527_;
}
}
else
{
lean_object* v_toPure_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v_proof_1533_; lean_object* v___x_1535_; 
lean_dec(v___x_1498_);
v_toPure_1529_ = lean_ctor_get(v_toApplicative_1497_, 1);
lean_inc(v_toPure_1529_);
lean_dec_ref(v_toApplicative_1497_);
lean_inc_ref(v_type_1491_);
v___x_1530_ = l_Lean_mkLambda(v_declName_1490_, v___x_1514_, v_type_1491_, v_proof_1507_);
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1532_ = l_Lean_mkConst(v___x_1531_, v_us_1499_);
lean_inc_ref(v_exprType_1517_);
v_proof_1533_ = l_Lean_mkApp6(v___x_1532_, v_type_1491_, v_exprType_1517_, v_value_1494_, v___x_1518_, v___x_1515_, v___x_1530_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_proof_1533_);
lean_ctor_set(v___x_1510_, 3, v_exprResult_1520_);
lean_ctor_set(v___x_1510_, 2, v_exprInit_1519_);
lean_ctor_set(v___x_1510_, 1, v_exprType_1517_);
lean_ctor_set(v___x_1510_, 0, v_expr_1516_);
v___x_1535_ = v___x_1510_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_expr_1516_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_exprType_1517_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_exprInit_1519_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_exprResult_1520_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_proof_1533_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*5, v_nondep_1495_);
v___x_1536_ = lean_apply_2(v_toPure_1529_, lean_box(0), v___x_1535_);
return v___x_1536_;
}
}
}
else
{
lean_dec(v___x_1498_);
if (v_modified_1508_ == 0)
{
lean_object* v_toPure_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_proof_1541_; lean_object* v___x_1543_; 
lean_dec_ref(v___x_1515_);
lean_dec_ref(v_proof_1507_);
lean_dec(v_declName_1490_);
v_toPure_1538_ = lean_ctor_get(v_toApplicative_1497_, 1);
lean_inc(v_toPure_1538_);
lean_dec_ref(v_toApplicative_1497_);
v___x_1539_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1540_ = l_Lean_mkConst(v___x_1539_, v_us_1499_);
lean_inc_ref(v_exprType_1517_);
v_proof_1541_ = l_Lean_mkApp6(v___x_1540_, v_type_1491_, v_exprType_1517_, v_value_1494_, v_fst_1492_, v___x_1518_, v_snd_1500_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_proof_1541_);
lean_ctor_set(v___x_1510_, 3, v_exprResult_1520_);
lean_ctor_set(v___x_1510_, 2, v_exprInit_1519_);
lean_ctor_set(v___x_1510_, 1, v_exprType_1517_);
lean_ctor_set(v___x_1510_, 0, v_expr_1516_);
v___x_1543_ = v___x_1510_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_expr_1516_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_exprType_1517_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_exprInit_1519_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_exprResult_1520_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_proof_1541_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*5, v_nondep_1495_);
v___x_1544_ = lean_apply_2(v_toPure_1538_, lean_box(0), v___x_1543_);
return v___x_1544_;
}
}
else
{
lean_object* v_toPure_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_proof_1550_; lean_object* v___x_1552_; 
v_toPure_1546_ = lean_ctor_get(v_toApplicative_1497_, 1);
lean_inc(v_toPure_1546_);
lean_dec_ref(v_toApplicative_1497_);
lean_inc_ref(v_type_1491_);
v___x_1547_ = l_Lean_mkLambda(v_declName_1490_, v___x_1514_, v_type_1491_, v_proof_1507_);
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1549_ = l_Lean_mkConst(v___x_1548_, v_us_1499_);
lean_inc_ref(v_exprType_1517_);
v_proof_1550_ = l_Lean_mkApp8(v___x_1549_, v_type_1491_, v_exprType_1517_, v_value_1494_, v_fst_1492_, v___x_1518_, v___x_1515_, v_snd_1500_, v___x_1547_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_proof_1550_);
lean_ctor_set(v___x_1510_, 3, v_exprResult_1520_);
lean_ctor_set(v___x_1510_, 2, v_exprInit_1519_);
lean_ctor_set(v___x_1510_, 1, v_exprType_1517_);
lean_ctor_set(v___x_1510_, 0, v_expr_1516_);
v___x_1552_ = v___x_1510_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_expr_1516_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_exprType_1517_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_exprInit_1519_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_exprResult_1520_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_proof_1550_);
v___x_1552_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; 
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*5, v_nondep_1495_);
v___x_1553_ = lean_apply_2(v_toPure_1546_, lean_box(0), v___x_1552_);
return v___x_1553_;
}
}
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_del_object(v___x_1510_);
lean_dec_ref(v_proof_1507_);
lean_dec_ref(v_exprResult_1506_);
lean_dec_ref(v_exprInit_1505_);
lean_dec_ref(v_exprType_1504_);
lean_dec_ref(v_expr_1503_);
lean_dec_ref(v_snd_1500_);
lean_dec(v_us_1499_);
lean_dec(v___x_1498_);
lean_dec_ref(v_toApplicative_1497_);
lean_dec_ref(v_value_1494_);
lean_dec_ref(v_fst_1492_);
lean_dec_ref(v_type_1491_);
lean_dec(v_declName_1490_);
v___x_1555_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1556_ = l_instInhabitedOfMonad___redArg(v_inst_1501_, v___x_1555_);
v___x_1557_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1558_ = l_panic___redArg(v___x_1556_, v___x_1557_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1560_, lean_object* v_type_1561_, lean_object* v_fst_1562_, lean_object* v___x_1563_, lean_object* v_value_1564_, lean_object* v_nondep_1565_, lean_object* v_fst_1566_, lean_object* v_toApplicative_1567_, lean_object* v___x_1568_, lean_object* v_us_1569_, lean_object* v_snd_1570_, lean_object* v_inst_1571_, lean_object* v_rb_1572_){
_start:
{
uint8_t v_nondep_11449__boxed_1573_; uint8_t v_fst_11450__boxed_1574_; lean_object* v_res_1575_; 
v_nondep_11449__boxed_1573_ = lean_unbox(v_nondep_1565_);
v_fst_11450__boxed_1574_ = lean_unbox(v_fst_1566_);
v_res_1575_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1560_, v_type_1561_, v_fst_1562_, v___x_1563_, v_value_1564_, v_nondep_11449__boxed_1573_, v_fst_11450__boxed_1574_, v_toApplicative_1567_, v___x_1568_, v_us_1569_, v_snd_1570_, v_inst_1571_, v_rb_1572_);
lean_dec(v___x_1563_);
return v_res_1575_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0));
v___x_1581_ = lean_unsigned_to_nat(34u);
v___x_1582_ = lean_unsigned_to_nat(217u);
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1584_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1585_ = l_mkPanicMessageWithDecl(v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1586_, lean_object* v_type_1587_, lean_object* v_value_1588_, uint8_t v_nondep_1589_, lean_object* v_toApplicative_1590_, lean_object* v___x_1591_, lean_object* v_us_1592_, lean_object* v_decl_1593_, lean_object* v_x_1594_, lean_object* v_i_1595_, lean_object* v_xs_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_info_1601_, lean_object* v_fixed_1602_, lean_object* v_used_1603_, lean_object* v_body_1604_, lean_object* v_toBind_1605_, lean_object* v_withNewLemmas_1606_, lean_object* v_val_x27_1607_, lean_object* v_val_1608_, uint8_t v___x_1609_, lean_object* v_____r_1610_){
_start:
{
uint8_t v___y_1612_; lean_object* v___y_1613_; uint8_t v___y_1629_; uint8_t v___x_1631_; 
v___x_1631_ = lean_expr_eqv(v_val_1608_, v_val_x27_1607_);
if (v___x_1631_ == 0)
{
v___y_1629_ = v_nondep_1589_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v___x_1609_;
goto v___jp_1628_;
}
v___jp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1614_ = lean_box(v_nondep_1589_);
v___x_1615_ = lean_box(v___y_1612_);
v___f_1616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1616_, 0, v_declName_1586_);
lean_closure_set(v___f_1616_, 1, v_type_1587_);
lean_closure_set(v___f_1616_, 2, v___y_1613_);
lean_closure_set(v___f_1616_, 3, v_value_1588_);
lean_closure_set(v___f_1616_, 4, v___x_1614_);
lean_closure_set(v___f_1616_, 5, v_toApplicative_1590_);
lean_closure_set(v___f_1616_, 6, v___x_1591_);
lean_closure_set(v___f_1616_, 7, v___x_1615_);
lean_closure_set(v___f_1616_, 8, v_us_1592_);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_decl_1593_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_mk_empty_array_with_capacity(v___x_1619_);
lean_inc_ref(v_x_1594_);
v___x_1621_ = lean_array_push(v___x_1620_, v_x_1594_);
v___x_1622_ = lean_nat_add(v_i_1595_, v___x_1619_);
v___x_1623_ = lean_array_push(v_xs_1596_, v_x_1594_);
lean_inc_ref(v_inst_1599_);
lean_inc_ref(v_inst_1597_);
v___x_1624_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v_info_1601_, v_fixed_1602_, v_used_1603_, v_body_1604_, v___x_1622_, v___x_1623_);
v___x_1625_ = lean_apply_4(v_toBind_1605_, lean_box(0), lean_box(0), v___x_1624_, v___f_1616_);
v___x_1626_ = lean_apply_3(v_withNewLemmas_1606_, lean_box(0), v___x_1621_, v___x_1625_);
v___x_1627_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1599_, v_inst_1597_, v___x_1618_, v___x_1626_);
return v___x_1627_;
}
v___jp_1628_:
{
if (v___y_1629_ == 0)
{
lean_inc_ref(v_value_1588_);
v___y_1612_ = v___y_1629_;
v___y_1613_ = v_value_1588_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_expr_abstract(v_val_x27_1607_, v_xs_1596_);
v___y_1612_ = v___y_1629_;
v___y_1613_ = v___x_1630_;
goto v___jp_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1632_ = _args[0];
lean_object* v_type_1633_ = _args[1];
lean_object* v_value_1634_ = _args[2];
lean_object* v_nondep_1635_ = _args[3];
lean_object* v_toApplicative_1636_ = _args[4];
lean_object* v___x_1637_ = _args[5];
lean_object* v_us_1638_ = _args[6];
lean_object* v_decl_1639_ = _args[7];
lean_object* v_x_1640_ = _args[8];
lean_object* v_i_1641_ = _args[9];
lean_object* v_xs_1642_ = _args[10];
lean_object* v_inst_1643_ = _args[11];
lean_object* v_inst_1644_ = _args[12];
lean_object* v_inst_1645_ = _args[13];
lean_object* v_inst_1646_ = _args[14];
lean_object* v_info_1647_ = _args[15];
lean_object* v_fixed_1648_ = _args[16];
lean_object* v_used_1649_ = _args[17];
lean_object* v_body_1650_ = _args[18];
lean_object* v_toBind_1651_ = _args[19];
lean_object* v_withNewLemmas_1652_ = _args[20];
lean_object* v_val_x27_1653_ = _args[21];
lean_object* v_val_1654_ = _args[22];
lean_object* v___x_1655_ = _args[23];
lean_object* v_____r_1656_ = _args[24];
_start:
{
uint8_t v_nondep_11720__boxed_1657_; uint8_t v___x_11727__boxed_1658_; lean_object* v_res_1659_; 
v_nondep_11720__boxed_1657_ = lean_unbox(v_nondep_1635_);
v___x_11727__boxed_1658_ = lean_unbox(v___x_1655_);
v_res_1659_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1632_, v_type_1633_, v_value_1634_, v_nondep_11720__boxed_1657_, v_toApplicative_1636_, v___x_1637_, v_us_1638_, v_decl_1639_, v_x_1640_, v_i_1641_, v_xs_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_, v_info_1647_, v_fixed_1648_, v_used_1649_, v_body_1650_, v_toBind_1651_, v_withNewLemmas_1652_, v_val_x27_1653_, v_val_1654_, v___x_11727__boxed_1658_, v_____r_1656_);
lean_dec_ref(v_val_1654_);
lean_dec_ref(v_val_x27_1653_);
lean_dec(v_i_1641_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1660_, lean_object* v_type_1661_, lean_object* v_value_1662_, uint8_t v_nondep_1663_, lean_object* v_toApplicative_1664_, lean_object* v___x_1665_, lean_object* v_us_1666_, lean_object* v_decl_1667_, lean_object* v_x_1668_, lean_object* v_i_1669_, lean_object* v_xs_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_info_1675_, lean_object* v_fixed_1676_, lean_object* v_used_1677_, lean_object* v_body_1678_, lean_object* v_toBind_1679_, lean_object* v_withNewLemmas_1680_, lean_object* v_val_1681_, uint8_t v___x_1682_, lean_object* v_val_x27_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v_toApplicative_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1753_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v___x_1684_, 1);
lean_dec(v_unused_1754_);
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1753_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_toApplicative_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1753_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_toFunctor_1689_; lean_object* v_toSeq_1690_; lean_object* v_toSeqLeft_1691_; lean_object* v_toSeqRight_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1751_; 
v_toFunctor_1689_ = lean_ctor_get(v_toApplicative_1685_, 0);
v_toSeq_1690_ = lean_ctor_get(v_toApplicative_1685_, 2);
v_toSeqLeft_1691_ = lean_ctor_get(v_toApplicative_1685_, 3);
v_toSeqRight_1692_ = lean_ctor_get(v_toApplicative_1685_, 4);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_toApplicative_1685_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v_toApplicative_1685_, 1);
lean_dec(v_unused_1752_);
v___x_1694_ = v_toApplicative_1685_;
v_isShared_1695_ = v_isSharedCheck_1751_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_toSeqRight_1692_);
lean_inc(v_toSeqLeft_1691_);
lean_inc(v_toSeq_1690_);
lean_inc(v_toFunctor_1689_);
lean_dec(v_toApplicative_1685_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1751_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___x_1705_; 
v___f_1696_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1697_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_1689_);
v___f_1698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1698_, 0, v_toFunctor_1689_);
v___f_1699_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1699_, 0, v_toFunctor_1689_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___f_1698_);
lean_ctor_set(v___x_1700_, 1, v___f_1699_);
v___f_1701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1701_, 0, v_toSeqRight_1692_);
v___f_1702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1702_, 0, v_toSeqLeft_1691_);
v___f_1703_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1703_, 0, v_toSeq_1690_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 4, v___f_1701_);
lean_ctor_set(v___x_1694_, 3, v___f_1702_);
lean_ctor_set(v___x_1694_, 2, v___f_1703_);
lean_ctor_set(v___x_1694_, 1, v___f_1696_);
lean_ctor_set(v___x_1694_, 0, v___x_1700_);
v___x_1705_ = v___x_1694_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___f_1696_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v___f_1703_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v___f_1702_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v___f_1701_);
v___x_1705_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 1, v___f_1697_);
lean_ctor_set(v___x_1687_, 0, v___x_1705_);
v___x_1707_ = v___x_1687_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___f_1697_);
v___x_1707_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v_toApplicative_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1747_; 
v___x_1708_ = l_ReaderT_instMonad___redArg(v___x_1707_);
v_toApplicative_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v___x_1708_, 1);
lean_dec(v_unused_1748_);
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1747_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_toApplicative_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1747_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_toFunctor_1713_; lean_object* v_toSeq_1714_; lean_object* v_toSeqLeft_1715_; lean_object* v_toSeqRight_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1745_; 
v_toFunctor_1713_ = lean_ctor_get(v_toApplicative_1709_, 0);
v_toSeq_1714_ = lean_ctor_get(v_toApplicative_1709_, 2);
v_toSeqLeft_1715_ = lean_ctor_get(v_toApplicative_1709_, 3);
v_toSeqRight_1716_ = lean_ctor_get(v_toApplicative_1709_, 4);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_toApplicative_1709_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v_toApplicative_1709_, 1);
lean_dec(v_unused_1746_);
v___x_1718_ = v_toApplicative_1709_;
v_isShared_1719_ = v_isSharedCheck_1745_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_toSeqRight_1716_);
lean_inc(v_toSeqLeft_1715_);
lean_inc(v_toSeq_1714_);
lean_inc(v_toFunctor_1713_);
lean_dec(v_toApplicative_1709_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1745_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v_cls_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___x_1733_; 
v___x_1720_ = lean_box(v_nondep_1663_);
v___x_1721_ = lean_box(v___x_1682_);
lean_inc_ref(v_val_1681_);
lean_inc_ref(v_val_x27_1683_);
lean_inc(v_toBind_1679_);
lean_inc(v_inst_1672_);
lean_inc(v_declName_1660_);
v___f_1722_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 25, 24);
lean_closure_set(v___f_1722_, 0, v_declName_1660_);
lean_closure_set(v___f_1722_, 1, v_type_1661_);
lean_closure_set(v___f_1722_, 2, v_value_1662_);
lean_closure_set(v___f_1722_, 3, v___x_1720_);
lean_closure_set(v___f_1722_, 4, v_toApplicative_1664_);
lean_closure_set(v___f_1722_, 5, v___x_1665_);
lean_closure_set(v___f_1722_, 6, v_us_1666_);
lean_closure_set(v___f_1722_, 7, v_decl_1667_);
lean_closure_set(v___f_1722_, 8, v_x_1668_);
lean_closure_set(v___f_1722_, 9, v_i_1669_);
lean_closure_set(v___f_1722_, 10, v_xs_1670_);
lean_closure_set(v___f_1722_, 11, v_inst_1671_);
lean_closure_set(v___f_1722_, 12, v_inst_1672_);
lean_closure_set(v___f_1722_, 13, v_inst_1673_);
lean_closure_set(v___f_1722_, 14, v_inst_1674_);
lean_closure_set(v___f_1722_, 15, v_info_1675_);
lean_closure_set(v___f_1722_, 16, v_fixed_1676_);
lean_closure_set(v___f_1722_, 17, v_used_1677_);
lean_closure_set(v___f_1722_, 18, v_body_1678_);
lean_closure_set(v___f_1722_, 19, v_toBind_1679_);
lean_closure_set(v___f_1722_, 20, v_withNewLemmas_1680_);
lean_closure_set(v___f_1722_, 21, v_val_x27_1683_);
lean_closure_set(v___f_1722_, 22, v_val_1681_);
lean_closure_set(v___f_1722_, 23, v___x_1721_);
v_cls_1723_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1724_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1725_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1713_);
v___f_1726_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1726_, 0, v_toFunctor_1713_);
v___f_1727_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1727_, 0, v_toFunctor_1713_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___f_1726_);
lean_ctor_set(v___x_1728_, 1, v___f_1727_);
v___f_1729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1729_, 0, v_toSeqRight_1716_);
v___f_1730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1730_, 0, v_toSeqLeft_1715_);
v___f_1731_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1731_, 0, v_toSeq_1714_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 4, v___f_1729_);
lean_ctor_set(v___x_1718_, 3, v___f_1730_);
lean_ctor_set(v___x_1718_, 2, v___f_1731_);
lean_ctor_set(v___x_1718_, 1, v___f_1724_);
lean_ctor_set(v___x_1718_, 0, v___x_1728_);
v___x_1733_ = v___x_1718_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___f_1724_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v___f_1731_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v___f_1730_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v___f_1729_);
v___x_1733_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___f_1725_);
lean_ctor_set(v___x_1711_, 0, v___x_1733_);
v___x_1735_ = v___x_1711_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___f_1725_);
v___x_1735_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___f_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___f_1736_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1738_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_1740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 14, 9);
lean_closure_set(v___f_1740_, 0, v___x_1735_);
lean_closure_set(v___f_1740_, 1, v___x_1738_);
lean_closure_set(v___f_1740_, 2, v___x_1739_);
lean_closure_set(v___f_1740_, 3, v_cls_1723_);
lean_closure_set(v___f_1740_, 4, v___x_1737_);
lean_closure_set(v___f_1740_, 5, v___f_1736_);
lean_closure_set(v___f_1740_, 6, v_declName_1660_);
lean_closure_set(v___f_1740_, 7, v_val_1681_);
lean_closure_set(v___f_1740_, 8, v_val_x27_1683_);
v___x_1741_ = lean_apply_2(v_inst_1672_, lean_box(0), v___f_1740_);
v___x_1742_ = lean_apply_4(v_toBind_1679_, lean_box(0), lean_box(0), v___x_1741_, v___f_1722_);
return v___x_1742_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1755_ = _args[0];
lean_object* v_type_1756_ = _args[1];
lean_object* v_value_1757_ = _args[2];
lean_object* v_nondep_1758_ = _args[3];
lean_object* v_toApplicative_1759_ = _args[4];
lean_object* v___x_1760_ = _args[5];
lean_object* v_us_1761_ = _args[6];
lean_object* v_decl_1762_ = _args[7];
lean_object* v_x_1763_ = _args[8];
lean_object* v_i_1764_ = _args[9];
lean_object* v_xs_1765_ = _args[10];
lean_object* v_inst_1766_ = _args[11];
lean_object* v_inst_1767_ = _args[12];
lean_object* v_inst_1768_ = _args[13];
lean_object* v_inst_1769_ = _args[14];
lean_object* v_info_1770_ = _args[15];
lean_object* v_fixed_1771_ = _args[16];
lean_object* v_used_1772_ = _args[17];
lean_object* v_body_1773_ = _args[18];
lean_object* v_toBind_1774_ = _args[19];
lean_object* v_withNewLemmas_1775_ = _args[20];
lean_object* v_val_1776_ = _args[21];
lean_object* v___x_1777_ = _args[22];
lean_object* v_val_x27_1778_ = _args[23];
_start:
{
uint8_t v_nondep_11751__boxed_1779_; uint8_t v___x_11758__boxed_1780_; lean_object* v_res_1781_; 
v_nondep_11751__boxed_1779_ = lean_unbox(v_nondep_1758_);
v___x_11758__boxed_1780_ = lean_unbox(v___x_1777_);
v_res_1781_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1755_, v_type_1756_, v_value_1757_, v_nondep_11751__boxed_1779_, v_toApplicative_1759_, v___x_1760_, v_us_1761_, v_decl_1762_, v_x_1763_, v_i_1764_, v_xs_1765_, v_inst_1766_, v_inst_1767_, v_inst_1768_, v_inst_1769_, v_info_1770_, v_fixed_1771_, v_used_1772_, v_body_1773_, v_toBind_1774_, v_withNewLemmas_1775_, v_val_1776_, v___x_11758__boxed_1780_, v_val_x27_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1782_, lean_object* v_declName_1783_, lean_object* v_type_1784_, lean_object* v_value_1785_, uint8_t v_nondep_1786_, lean_object* v_toApplicative_1787_, lean_object* v___x_1788_, lean_object* v_us_1789_, lean_object* v_inst_1790_, lean_object* v_x_1791_, lean_object* v_i_1792_, lean_object* v_xs_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_info_1797_, lean_object* v_fixed_1798_, lean_object* v_used_1799_, lean_object* v_body_1800_, lean_object* v_toBind_1801_, lean_object* v_withNewLemmas_1802_, lean_object* v_____x_1803_){
_start:
{
lean_object* v_snd_1804_; lean_object* v_fst_1805_; lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1826_; 
v_snd_1804_ = lean_ctor_get(v_____x_1803_, 1);
lean_inc(v_snd_1804_);
v_fst_1805_ = lean_ctor_get(v_____x_1803_, 0);
lean_inc(v_fst_1805_);
lean_dec_ref(v_____x_1803_);
v_fst_1806_ = lean_ctor_get(v_snd_1804_, 0);
v_snd_1807_ = lean_ctor_get(v_snd_1804_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_snd_1804_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1809_ = v_snd_1804_;
v_isShared_1810_ = v_isSharedCheck_1826_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snd_1807_);
lean_inc(v_fst_1806_);
lean_dec(v_snd_1804_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1826_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
lean_ctor_set(v___x_1809_, 1, v___x_1811_);
lean_ctor_set(v___x_1809_, 0, v_decl_1782_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_decl_1782_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_box(v_nondep_1786_);
lean_inc_ref(v_inst_1790_);
v___f_1816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1816_, 0, v_declName_1783_);
lean_closure_set(v___f_1816_, 1, v_type_1784_);
lean_closure_set(v___f_1816_, 2, v_fst_1805_);
lean_closure_set(v___f_1816_, 3, v___x_1814_);
lean_closure_set(v___f_1816_, 4, v_value_1785_);
lean_closure_set(v___f_1816_, 5, v___x_1815_);
lean_closure_set(v___f_1816_, 6, v_fst_1806_);
lean_closure_set(v___f_1816_, 7, v_toApplicative_1787_);
lean_closure_set(v___f_1816_, 8, v___x_1788_);
lean_closure_set(v___f_1816_, 9, v_us_1789_);
lean_closure_set(v___f_1816_, 10, v_snd_1807_);
lean_closure_set(v___f_1816_, 11, v_inst_1790_);
v___x_1817_ = lean_mk_empty_array_with_capacity(v___x_1814_);
lean_inc_ref(v_x_1791_);
v___x_1818_ = lean_array_push(v___x_1817_, v_x_1791_);
v___x_1819_ = lean_nat_add(v_i_1792_, v___x_1814_);
v___x_1820_ = lean_array_push(v_xs_1793_, v_x_1791_);
lean_inc_ref(v_inst_1795_);
lean_inc_ref(v_inst_1790_);
v___x_1821_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1790_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_info_1797_, v_fixed_1798_, v_used_1799_, v_body_1800_, v___x_1819_, v___x_1820_);
v___x_1822_ = lean_apply_4(v_toBind_1801_, lean_box(0), lean_box(0), v___x_1821_, v___f_1816_);
v___x_1823_ = lean_apply_3(v_withNewLemmas_1802_, lean_box(0), v___x_1818_, v___x_1822_);
v___x_1824_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1795_, v_inst_1790_, v___x_1813_, v___x_1823_);
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1827_ = _args[0];
lean_object* v_declName_1828_ = _args[1];
lean_object* v_type_1829_ = _args[2];
lean_object* v_value_1830_ = _args[3];
lean_object* v_nondep_1831_ = _args[4];
lean_object* v_toApplicative_1832_ = _args[5];
lean_object* v___x_1833_ = _args[6];
lean_object* v_us_1834_ = _args[7];
lean_object* v_inst_1835_ = _args[8];
lean_object* v_x_1836_ = _args[9];
lean_object* v_i_1837_ = _args[10];
lean_object* v_xs_1838_ = _args[11];
lean_object* v_inst_1839_ = _args[12];
lean_object* v_inst_1840_ = _args[13];
lean_object* v_inst_1841_ = _args[14];
lean_object* v_info_1842_ = _args[15];
lean_object* v_fixed_1843_ = _args[16];
lean_object* v_used_1844_ = _args[17];
lean_object* v_body_1845_ = _args[18];
lean_object* v_toBind_1846_ = _args[19];
lean_object* v_withNewLemmas_1847_ = _args[20];
lean_object* v_____x_1848_ = _args[21];
_start:
{
uint8_t v_nondep_11693__boxed_1849_; lean_object* v_res_1850_; 
v_nondep_11693__boxed_1849_ = lean_unbox(v_nondep_1831_);
v_res_1850_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1827_, v_declName_1828_, v_type_1829_, v_value_1830_, v_nondep_11693__boxed_1849_, v_toApplicative_1832_, v___x_1833_, v_us_1834_, v_inst_1835_, v_x_1836_, v_i_1837_, v_xs_1838_, v_inst_1839_, v_inst_1840_, v_inst_1841_, v_info_1842_, v_fixed_1843_, v_used_1844_, v_body_1845_, v_toBind_1846_, v_withNewLemmas_1847_, v_____x_1848_);
lean_dec(v_i_1837_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1851_ = _args[0];
lean_object* v_declName_1852_ = _args[1];
lean_object* v_type_1853_ = _args[2];
lean_object* v_value_1854_ = _args[3];
lean_object* v_us_1855_ = _args[4];
lean_object* v___x_1856_ = _args[5];
lean_object* v_toApplicative_1857_ = _args[6];
lean_object* v_nondep_1858_ = _args[7];
lean_object* v_i_1859_ = _args[8];
lean_object* v_xs_1860_ = _args[9];
lean_object* v_inst_1861_ = _args[10];
lean_object* v_inst_1862_ = _args[11];
lean_object* v_inst_1863_ = _args[12];
lean_object* v_inst_1864_ = _args[13];
lean_object* v_info_1865_ = _args[14];
lean_object* v_fixed_1866_ = _args[15];
lean_object* v_used_1867_ = _args[16];
lean_object* v_body_1868_ = _args[17];
lean_object* v_toBind_1869_ = _args[18];
lean_object* v_____r_1870_ = _args[19];
_start:
{
uint8_t v_nondep_11676__boxed_1871_; lean_object* v_res_1872_; 
v_nondep_11676__boxed_1871_ = lean_unbox(v_nondep_1858_);
v_res_1872_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1851_, v_declName_1852_, v_type_1853_, v_value_1854_, v_us_1855_, v___x_1856_, v_toApplicative_1857_, v_nondep_11676__boxed_1871_, v_i_1859_, v_xs_1860_, v_inst_1861_, v_inst_1862_, v_inst_1863_, v_inst_1864_, v_info_1865_, v_fixed_1866_, v_used_1867_, v_body_1868_, v_toBind_1869_, v_____r_1870_);
lean_dec(v_i_1859_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_info_1877_, lean_object* v_fixed_1878_, lean_object* v_used_1879_, lean_object* v_e_1880_, lean_object* v_i_1881_, lean_object* v_xs_1882_){
_start:
{
lean_object* v_haveInfo_1888_; lean_object* v_body_1889_; lean_object* v_bodyType_1890_; lean_object* v_level_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v_haveInfo_1888_ = lean_ctor_get(v_info_1877_, 0);
v_body_1889_ = lean_ctor_get(v_info_1877_, 3);
v_bodyType_1890_ = lean_ctor_get(v_info_1877_, 4);
v_level_1891_ = lean_ctor_get(v_info_1877_, 5);
v___x_1892_ = lean_array_get_size(v_haveInfo_1888_);
v___x_1893_ = lean_nat_dec_lt(v_i_1881_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v_toApplicative_1894_; lean_object* v_toBind_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1971_; 
lean_inc(v_level_1891_);
lean_inc_ref(v_bodyType_1890_);
lean_inc_ref(v_body_1889_);
lean_dec(v_i_1881_);
lean_dec_ref(v_used_1879_);
lean_dec_ref(v_fixed_1878_);
lean_dec_ref(v_info_1877_);
lean_dec_ref(v_inst_1875_);
v_toApplicative_1894_ = lean_ctor_get(v_inst_1873_, 0);
v_toBind_1895_ = lean_ctor_get(v_inst_1873_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_inst_1873_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1897_ = v_inst_1873_;
v_isShared_1898_ = v_isSharedCheck_1971_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_toBind_1895_);
lean_inc(v_toApplicative_1894_);
lean_dec(v_inst_1873_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1971_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v_toApplicative_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1969_; 
v___x_1899_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1899_, 1);
lean_dec(v_unused_1970_);
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1969_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_toApplicative_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1969_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_toFunctor_1904_; lean_object* v_toSeq_1905_; lean_object* v_toSeqLeft_1906_; lean_object* v_toSeqRight_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1967_; 
v_toFunctor_1904_ = lean_ctor_get(v_toApplicative_1900_, 0);
v_toSeq_1905_ = lean_ctor_get(v_toApplicative_1900_, 2);
v_toSeqLeft_1906_ = lean_ctor_get(v_toApplicative_1900_, 3);
v_toSeqRight_1907_ = lean_ctor_get(v_toApplicative_1900_, 4);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_toApplicative_1900_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_toApplicative_1900_, 1);
lean_dec(v_unused_1968_);
v___x_1909_ = v_toApplicative_1900_;
v_isShared_1910_ = v_isSharedCheck_1967_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_toSeqRight_1907_);
lean_inc(v_toSeqLeft_1906_);
lean_inc(v_toSeq_1905_);
lean_inc(v_toFunctor_1904_);
lean_dec(v_toApplicative_1900_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1967_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___f_1911_; lean_object* v___f_1912_; lean_object* v___f_1913_; lean_object* v___f_1914_; lean_object* v___x_1916_; 
v___f_1911_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1912_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_1904_);
v___f_1913_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1913_, 0, v_toFunctor_1904_);
v___f_1914_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1914_, 0, v_toFunctor_1904_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___f_1914_);
lean_ctor_set(v___x_1897_, 0, v___f_1913_);
v___x_1916_ = v___x_1897_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___f_1913_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___f_1914_);
v___x_1916_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1921_; 
v___f_1917_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1917_, 0, v_toSeqRight_1907_);
v___f_1918_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1918_, 0, v_toSeqLeft_1906_);
v___f_1919_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1919_, 0, v_toSeq_1905_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 4, v___f_1917_);
lean_ctor_set(v___x_1909_, 3, v___f_1918_);
lean_ctor_set(v___x_1909_, 2, v___f_1919_);
lean_ctor_set(v___x_1909_, 1, v___f_1911_);
lean_ctor_set(v___x_1909_, 0, v___x_1916_);
v___x_1921_ = v___x_1909_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___f_1911_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v___f_1919_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v___f_1918_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v___f_1917_);
v___x_1921_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v___f_1912_);
lean_ctor_set(v___x_1902_, 0, v___x_1921_);
v___x_1923_ = v___x_1902_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___f_1912_);
v___x_1923_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v_toApplicative_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1962_; 
v___x_1924_ = l_ReaderT_instMonad___redArg(v___x_1923_);
v_toApplicative_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v___x_1924_, 1);
lean_dec(v_unused_1963_);
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1962_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_toApplicative_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1962_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_toFunctor_1929_; lean_object* v_toSeq_1930_; lean_object* v_toSeqLeft_1931_; lean_object* v_toSeqRight_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1960_; 
v_toFunctor_1929_ = lean_ctor_get(v_toApplicative_1925_, 0);
v_toSeq_1930_ = lean_ctor_get(v_toApplicative_1925_, 2);
v_toSeqLeft_1931_ = lean_ctor_get(v_toApplicative_1925_, 3);
v_toSeqRight_1932_ = lean_ctor_get(v_toApplicative_1925_, 4);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_toApplicative_1925_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v_toApplicative_1925_, 1);
lean_dec(v_unused_1961_);
v___x_1934_ = v_toApplicative_1925_;
v_isShared_1935_ = v_isSharedCheck_1960_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_toSeqRight_1932_);
lean_inc(v_toSeqLeft_1931_);
lean_inc(v_toSeq_1930_);
lean_inc(v_toFunctor_1929_);
lean_dec(v_toApplicative_1925_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1960_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v_cls_1938_; lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___f_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___x_1948_; 
v___x_1936_ = lean_box(v___x_1893_);
lean_inc(v_toBind_1895_);
lean_inc_ref(v_body_1889_);
v___f_1937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1937_, 0, v_inst_1876_);
lean_closure_set(v___f_1937_, 1, v_bodyType_1890_);
lean_closure_set(v___f_1937_, 2, v_xs_1882_);
lean_closure_set(v___f_1937_, 3, v_toApplicative_1894_);
lean_closure_set(v___f_1937_, 4, v_level_1891_);
lean_closure_set(v___f_1937_, 5, v_e_1880_);
lean_closure_set(v___f_1937_, 6, v___x_1936_);
lean_closure_set(v___f_1937_, 7, v_body_1889_);
lean_closure_set(v___f_1937_, 8, v_toBind_1895_);
v_cls_1938_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1939_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1940_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1929_);
v___f_1941_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1941_, 0, v_toFunctor_1929_);
v___f_1942_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1942_, 0, v_toFunctor_1929_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___f_1941_);
lean_ctor_set(v___x_1943_, 1, v___f_1942_);
v___f_1944_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1944_, 0, v_toSeqRight_1932_);
v___f_1945_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1945_, 0, v_toSeqLeft_1931_);
v___f_1946_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1946_, 0, v_toSeq_1930_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 4, v___f_1944_);
lean_ctor_set(v___x_1934_, 3, v___f_1945_);
lean_ctor_set(v___x_1934_, 2, v___f_1946_);
lean_ctor_set(v___x_1934_, 1, v___f_1939_);
lean_ctor_set(v___x_1934_, 0, v___x_1943_);
v___x_1948_ = v___x_1934_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___f_1939_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v___f_1946_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v___f_1945_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v___f_1944_);
v___x_1948_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___f_1940_);
lean_ctor_set(v___x_1927_, 0, v___x_1948_);
v___x_1950_ = v___x_1927_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___f_1940_);
v___x_1950_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___f_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___f_1951_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1953_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_1955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 12, 7);
lean_closure_set(v___f_1955_, 0, v___x_1950_);
lean_closure_set(v___f_1955_, 1, v___x_1953_);
lean_closure_set(v___f_1955_, 2, v___x_1954_);
lean_closure_set(v___f_1955_, 3, v_cls_1938_);
lean_closure_set(v___f_1955_, 4, v___x_1952_);
lean_closure_set(v___f_1955_, 5, v___f_1951_);
lean_closure_set(v___f_1955_, 6, v_body_1889_);
v___x_1956_ = lean_apply_2(v_inst_1874_, lean_box(0), v___f_1955_);
v___x_1957_ = lean_apply_4(v_toBind_1895_, lean_box(0), lean_box(0), v___x_1956_, v___f_1937_);
return v___x_1957_;
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
else
{
if (lean_obj_tag(v_e_1880_) == 8)
{
uint8_t v_nondep_1972_; 
v_nondep_1972_ = lean_ctor_get_uint8(v_e_1880_, sizeof(void*)*4 + 8);
if (v_nondep_1972_ == 1)
{
lean_object* v_declName_1973_; lean_object* v_type_1974_; lean_object* v_value_1975_; lean_object* v_body_1976_; lean_object* v_hinfo_1977_; lean_object* v_decl_1978_; lean_object* v_level_1979_; lean_object* v_x_1980_; lean_object* v_val_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_us_1984_; uint8_t v___y_1986_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_declName_1973_ = lean_ctor_get(v_e_1880_, 0);
lean_inc(v_declName_1973_);
v_type_1974_ = lean_ctor_get(v_e_1880_, 1);
lean_inc_ref(v_type_1974_);
v_value_1975_ = lean_ctor_get(v_e_1880_, 2);
lean_inc_ref(v_value_1975_);
v_body_1976_ = lean_ctor_get(v_e_1880_, 3);
lean_inc_ref(v_body_1976_);
lean_dec_ref(v_e_1880_);
v_hinfo_1977_ = lean_array_fget_borrowed(v_haveInfo_1888_, v_i_1881_);
v_decl_1978_ = lean_ctor_get(v_hinfo_1977_, 2);
v_level_1979_ = lean_ctor_get(v_hinfo_1977_, 3);
lean_inc_ref(v_decl_1978_);
v_x_1980_ = l_Lean_LocalDecl_toExpr(v_decl_1978_);
v_val_1981_ = l_Lean_LocalDecl_value(v_decl_1978_, v_nondep_1972_);
v___x_1982_ = lean_box(0);
lean_inc(v_level_1891_);
v___x_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_level_1891_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
lean_inc_ref(v___x_1983_);
lean_inc(v_level_1979_);
v_us_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1984_, 0, v_level_1979_);
lean_ctor_set(v_us_1984_, 1, v___x_1983_);
v___x_2013_ = lean_array_get_size(v_used_1879_);
v___x_2014_ = lean_nat_dec_lt(v_i_1881_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_inc_ref(v_decl_1978_);
goto v___jp_1996_;
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = lean_array_fget_borrowed(v_used_1879_, v_i_1881_);
v___x_2016_ = lean_unbox(v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v_toApplicative_2017_; lean_object* v_toBind_2018_; lean_object* v___x_2019_; lean_object* v_toApplicative_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_x_1980_);
v_toApplicative_2017_ = lean_ctor_get(v_inst_1873_, 0);
lean_inc_ref(v_toApplicative_2017_);
v_toBind_2018_ = lean_ctor_get(v_inst_1873_, 1);
lean_inc(v_toBind_2018_);
v___x_2019_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2019_, 1);
lean_dec(v_unused_2088_);
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2087_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_toApplicative_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2087_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_toFunctor_2024_; lean_object* v_toSeq_2025_; lean_object* v_toSeqLeft_2026_; lean_object* v_toSeqRight_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2085_; 
v_toFunctor_2024_ = lean_ctor_get(v_toApplicative_2020_, 0);
v_toSeq_2025_ = lean_ctor_get(v_toApplicative_2020_, 2);
v_toSeqLeft_2026_ = lean_ctor_get(v_toApplicative_2020_, 3);
v_toSeqRight_2027_ = lean_ctor_get(v_toApplicative_2020_, 4);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_toApplicative_2020_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_dec(v_unused_2086_);
v___x_2029_ = v_toApplicative_2020_;
v_isShared_2030_ = v_isSharedCheck_2085_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_toSeqRight_2027_);
lean_inc(v_toSeqLeft_2026_);
lean_inc(v_toSeq_2025_);
lean_inc(v_toFunctor_2024_);
lean_dec(v_toApplicative_2020_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2085_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___f_2031_; lean_object* v___f_2032_; lean_object* v___f_2033_; lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___f_2038_; lean_object* v___x_2040_; 
v___f_2031_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_2032_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_2024_);
v___f_2033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2033_, 0, v_toFunctor_2024_);
v___f_2034_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2034_, 0, v_toFunctor_2024_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___f_2033_);
lean_ctor_set(v___x_2035_, 1, v___f_2034_);
v___f_2036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2036_, 0, v_toSeqRight_2027_);
v___f_2037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2037_, 0, v_toSeqLeft_2026_);
v___f_2038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2038_, 0, v_toSeq_2025_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___f_2036_);
lean_ctor_set(v___x_2029_, 3, v___f_2037_);
lean_ctor_set(v___x_2029_, 2, v___f_2038_);
lean_ctor_set(v___x_2029_, 1, v___f_2031_);
lean_ctor_set(v___x_2029_, 0, v___x_2035_);
v___x_2040_ = v___x_2029_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___f_2031_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v___f_2038_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v___f_2037_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v___f_2036_);
v___x_2040_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v___f_2032_);
lean_ctor_set(v___x_2022_, 0, v___x_2040_);
v___x_2042_ = v___x_2022_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___f_2032_);
v___x_2042_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v_toApplicative_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2081_; 
v___x_2043_ = l_ReaderT_instMonad___redArg(v___x_2042_);
v_toApplicative_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2043_, 1);
lean_dec(v_unused_2082_);
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2081_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_toApplicative_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2081_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_toFunctor_2048_; lean_object* v_toSeq_2049_; lean_object* v_toSeqLeft_2050_; lean_object* v_toSeqRight_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2079_; 
v_toFunctor_2048_ = lean_ctor_get(v_toApplicative_2044_, 0);
v_toSeq_2049_ = lean_ctor_get(v_toApplicative_2044_, 2);
v_toSeqLeft_2050_ = lean_ctor_get(v_toApplicative_2044_, 3);
v_toSeqRight_2051_ = lean_ctor_get(v_toApplicative_2044_, 4);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_toApplicative_2044_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v_toApplicative_2044_, 1);
lean_dec(v_unused_2080_);
v___x_2053_ = v_toApplicative_2044_;
v_isShared_2054_ = v_isSharedCheck_2079_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_toSeqRight_2051_);
lean_inc(v_toSeqLeft_2050_);
lean_inc(v_toSeq_2049_);
lean_inc(v_toFunctor_2048_);
lean_dec(v_toApplicative_2044_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2079_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v_cls_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___x_2067_; 
v___x_2055_ = lean_box(v_nondep_1972_);
lean_inc(v_toBind_2018_);
lean_inc(v_inst_1874_);
lean_inc(v_declName_1973_);
v___f_2056_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2056_, 0, v___x_1982_);
lean_closure_set(v___f_2056_, 1, v_declName_1973_);
lean_closure_set(v___f_2056_, 2, v_type_1974_);
lean_closure_set(v___f_2056_, 3, v_value_1975_);
lean_closure_set(v___f_2056_, 4, v_us_1984_);
lean_closure_set(v___f_2056_, 5, v___x_1983_);
lean_closure_set(v___f_2056_, 6, v_toApplicative_2017_);
lean_closure_set(v___f_2056_, 7, v___x_2055_);
lean_closure_set(v___f_2056_, 8, v_i_1881_);
lean_closure_set(v___f_2056_, 9, v_xs_1882_);
lean_closure_set(v___f_2056_, 10, v_inst_1873_);
lean_closure_set(v___f_2056_, 11, v_inst_1874_);
lean_closure_set(v___f_2056_, 12, v_inst_1875_);
lean_closure_set(v___f_2056_, 13, v_inst_1876_);
lean_closure_set(v___f_2056_, 14, v_info_1877_);
lean_closure_set(v___f_2056_, 15, v_fixed_1878_);
lean_closure_set(v___f_2056_, 16, v_used_1879_);
lean_closure_set(v___f_2056_, 17, v_body_1976_);
lean_closure_set(v___f_2056_, 18, v_toBind_2018_);
v_cls_2057_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_2058_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_2059_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_2048_);
v___f_2060_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2060_, 0, v_toFunctor_2048_);
v___f_2061_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2061_, 0, v_toFunctor_2048_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___f_2060_);
lean_ctor_set(v___x_2062_, 1, v___f_2061_);
v___f_2063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2063_, 0, v_toSeqRight_2051_);
v___f_2064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2064_, 0, v_toSeqLeft_2050_);
v___f_2065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2065_, 0, v_toSeq_2049_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 4, v___f_2063_);
lean_ctor_set(v___x_2053_, 3, v___f_2064_);
lean_ctor_set(v___x_2053_, 2, v___f_2065_);
lean_ctor_set(v___x_2053_, 1, v___f_2058_);
lean_ctor_set(v___x_2053_, 0, v___x_2062_);
v___x_2067_ = v___x_2053_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___f_2058_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v___f_2065_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v___f_2064_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___f_2063_);
v___x_2067_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___f_2059_);
lean_ctor_set(v___x_2046_, 0, v___x_2067_);
v___x_2069_ = v___x_2046_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___f_2059_);
v___x_2069_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___f_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___f_2070_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_2072_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_2074_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 13, 8);
lean_closure_set(v___f_2074_, 0, v___x_2069_);
lean_closure_set(v___f_2074_, 1, v___x_2072_);
lean_closure_set(v___f_2074_, 2, v___x_2073_);
lean_closure_set(v___f_2074_, 3, v_cls_2057_);
lean_closure_set(v___f_2074_, 4, v___x_2071_);
lean_closure_set(v___f_2074_, 5, v___f_2070_);
lean_closure_set(v___f_2074_, 6, v_declName_1973_);
lean_closure_set(v___f_2074_, 7, v_val_1981_);
v___x_2075_ = lean_apply_2(v_inst_1874_, lean_box(0), v___f_2074_);
v___x_2076_ = lean_apply_4(v_toBind_2018_, lean_box(0), lean_box(0), v___x_2075_, v___f_2056_);
return v___x_2076_;
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
lean_inc_ref(v_decl_1978_);
goto v___jp_1996_;
}
}
v___jp_1985_:
{
lean_object* v_toApplicative_1987_; lean_object* v_toBind_1988_; lean_object* v_withNewLemmas_1989_; lean_object* v_dsimp_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_toApplicative_1987_ = lean_ctor_get(v_inst_1873_, 0);
lean_inc_ref(v_toApplicative_1987_);
v_toBind_1988_ = lean_ctor_get(v_inst_1873_, 1);
lean_inc(v_toBind_1988_);
v_withNewLemmas_1989_ = lean_ctor_get(v_inst_1876_, 0);
lean_inc(v_withNewLemmas_1989_);
v_dsimp_1990_ = lean_ctor_get(v_inst_1876_, 1);
lean_inc(v_dsimp_1990_);
v___x_1991_ = lean_box(v_nondep_1972_);
v___x_1992_ = lean_box(v___y_1986_);
lean_inc_ref(v_val_1981_);
lean_inc(v_toBind_1988_);
v___f_1993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 24, 23);
lean_closure_set(v___f_1993_, 0, v_declName_1973_);
lean_closure_set(v___f_1993_, 1, v_type_1974_);
lean_closure_set(v___f_1993_, 2, v_value_1975_);
lean_closure_set(v___f_1993_, 3, v___x_1991_);
lean_closure_set(v___f_1993_, 4, v_toApplicative_1987_);
lean_closure_set(v___f_1993_, 5, v___x_1983_);
lean_closure_set(v___f_1993_, 6, v_us_1984_);
lean_closure_set(v___f_1993_, 7, v_decl_1978_);
lean_closure_set(v___f_1993_, 8, v_x_1980_);
lean_closure_set(v___f_1993_, 9, v_i_1881_);
lean_closure_set(v___f_1993_, 10, v_xs_1882_);
lean_closure_set(v___f_1993_, 11, v_inst_1873_);
lean_closure_set(v___f_1993_, 12, v_inst_1874_);
lean_closure_set(v___f_1993_, 13, v_inst_1875_);
lean_closure_set(v___f_1993_, 14, v_inst_1876_);
lean_closure_set(v___f_1993_, 15, v_info_1877_);
lean_closure_set(v___f_1993_, 16, v_fixed_1878_);
lean_closure_set(v___f_1993_, 17, v_used_1879_);
lean_closure_set(v___f_1993_, 18, v_body_1976_);
lean_closure_set(v___f_1993_, 19, v_toBind_1988_);
lean_closure_set(v___f_1993_, 20, v_withNewLemmas_1989_);
lean_closure_set(v___f_1993_, 21, v_val_1981_);
lean_closure_set(v___f_1993_, 22, v___x_1992_);
v___x_1994_ = lean_apply_1(v_dsimp_1990_, v_val_1981_);
v___x_1995_ = lean_apply_4(v_toBind_1988_, lean_box(0), lean_box(0), v___x_1994_, v___f_1993_);
return v___x_1995_;
}
v___jp_1996_:
{
uint8_t v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = 0;
v___x_1998_ = lean_array_get_size(v_fixed_1878_);
v___x_1999_ = lean_nat_dec_lt(v_i_1881_, v___x_1998_);
if (v___x_1999_ == 0)
{
v___y_1986_ = v___x_1997_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = lean_array_fget_borrowed(v_fixed_1878_, v_i_1881_);
v___x_2001_ = lean_unbox(v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v_toApplicative_2002_; lean_object* v_toBind_2003_; lean_object* v_withNewLemmas_2004_; lean_object* v_simp_2005_; lean_object* v___x_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_inc(v___x_2000_);
lean_inc(v_level_1979_);
v_toApplicative_2002_ = lean_ctor_get(v_inst_1873_, 0);
lean_inc_ref(v_toApplicative_2002_);
v_toBind_2003_ = lean_ctor_get(v_inst_1873_, 1);
lean_inc(v_toBind_2003_);
v_withNewLemmas_2004_ = lean_ctor_get(v_inst_1876_, 0);
lean_inc(v_withNewLemmas_2004_);
v_simp_2005_ = lean_ctor_get(v_inst_1876_, 2);
lean_inc(v_simp_2005_);
v___x_2006_ = lean_box(v_nondep_1972_);
lean_inc(v_toBind_2003_);
lean_inc(v_inst_1874_);
lean_inc_ref(v_xs_1882_);
lean_inc_ref(v_toApplicative_2002_);
lean_inc_ref(v_value_1975_);
lean_inc_ref(v_type_1974_);
lean_inc(v_declName_1973_);
v___f_2007_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_2007_, 0, v_decl_1978_);
lean_closure_set(v___f_2007_, 1, v_declName_1973_);
lean_closure_set(v___f_2007_, 2, v_type_1974_);
lean_closure_set(v___f_2007_, 3, v_value_1975_);
lean_closure_set(v___f_2007_, 4, v___x_2006_);
lean_closure_set(v___f_2007_, 5, v_toApplicative_2002_);
lean_closure_set(v___f_2007_, 6, v___x_1983_);
lean_closure_set(v___f_2007_, 7, v_us_1984_);
lean_closure_set(v___f_2007_, 8, v_inst_1873_);
lean_closure_set(v___f_2007_, 9, v_x_1980_);
lean_closure_set(v___f_2007_, 10, v_i_1881_);
lean_closure_set(v___f_2007_, 11, v_xs_1882_);
lean_closure_set(v___f_2007_, 12, v_inst_1874_);
lean_closure_set(v___f_2007_, 13, v_inst_1875_);
lean_closure_set(v___f_2007_, 14, v_inst_1876_);
lean_closure_set(v___f_2007_, 15, v_info_1877_);
lean_closure_set(v___f_2007_, 16, v_fixed_1878_);
lean_closure_set(v___f_2007_, 17, v_used_1879_);
lean_closure_set(v___f_2007_, 18, v_body_1976_);
lean_closure_set(v___f_2007_, 19, v_toBind_2003_);
lean_closure_set(v___f_2007_, 20, v_withNewLemmas_2004_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_2008_, 0, v___f_2007_);
v___x_2009_ = lean_box(v_nondep_1972_);
lean_inc_ref(v_val_1981_);
lean_inc_ref(v___f_2008_);
lean_inc(v_toBind_2003_);
v___f_2010_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_2010_, 0, v_toApplicative_2002_);
lean_closure_set(v___f_2010_, 1, v_level_1979_);
lean_closure_set(v___f_2010_, 2, v___x_1982_);
lean_closure_set(v___f_2010_, 3, v_type_1974_);
lean_closure_set(v___f_2010_, 4, v_value_1975_);
lean_closure_set(v___f_2010_, 5, v___x_2000_);
lean_closure_set(v___f_2010_, 6, v_toBind_2003_);
lean_closure_set(v___f_2010_, 7, v___f_2008_);
lean_closure_set(v___f_2010_, 8, v_xs_1882_);
lean_closure_set(v___f_2010_, 9, v___x_2009_);
lean_closure_set(v___f_2010_, 10, v___f_2008_);
lean_closure_set(v___f_2010_, 11, v_declName_1973_);
lean_closure_set(v___f_2010_, 12, v_val_1981_);
lean_closure_set(v___f_2010_, 13, v_inst_1874_);
v___x_2011_ = lean_apply_1(v_simp_2005_, v_val_1981_);
v___x_2012_ = lean_apply_4(v_toBind_2003_, lean_box(0), lean_box(0), v___x_2011_, v___f_2010_);
return v___x_2012_;
}
else
{
v___y_1986_ = v___x_1997_;
goto v___jp_1985_;
}
}
}
}
else
{
lean_dec_ref(v_e_1880_);
lean_dec_ref(v_xs_1882_);
lean_dec(v_i_1881_);
lean_dec_ref(v_used_1879_);
lean_dec_ref(v_fixed_1878_);
lean_dec_ref(v_info_1877_);
lean_dec_ref(v_inst_1876_);
lean_dec_ref(v_inst_1875_);
lean_dec(v_inst_1874_);
goto v___jp_1883_;
}
}
else
{
lean_dec_ref(v_xs_1882_);
lean_dec(v_i_1881_);
lean_dec_ref(v_e_1880_);
lean_dec_ref(v_used_1879_);
lean_dec_ref(v_fixed_1878_);
lean_dec_ref(v_info_1877_);
lean_dec_ref(v_inst_1876_);
lean_dec_ref(v_inst_1875_);
lean_dec(v_inst_1874_);
goto v___jp_1883_;
}
}
v___jp_1883_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1884_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1885_ = l_instInhabitedOfMonad___redArg(v_inst_1873_, v___x_1884_);
v___x_1886_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1887_ = l_panic___redArg(v___x_1885_, v___x_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_2089_, lean_object* v_declName_2090_, lean_object* v_type_2091_, lean_object* v_value_2092_, lean_object* v_us_2093_, lean_object* v___x_2094_, lean_object* v_toApplicative_2095_, uint8_t v_nondep_2096_, lean_object* v_i_2097_, lean_object* v_xs_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_info_2103_, lean_object* v_fixed_2104_, lean_object* v_used_2105_, lean_object* v_body_2106_, lean_object* v_toBind_2107_, lean_object* v_____r_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v_x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_2110_ = l_Lean_mkConst(v___x_2109_, v___x_2089_);
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_box(v_nondep_2096_);
v___f_2113_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_2113_, 0, v___x_2111_);
lean_closure_set(v___f_2113_, 1, v_declName_2090_);
lean_closure_set(v___f_2113_, 2, v_type_2091_);
lean_closure_set(v___f_2113_, 3, v_value_2092_);
lean_closure_set(v___f_2113_, 4, v_us_2093_);
lean_closure_set(v___f_2113_, 5, v___x_2094_);
lean_closure_set(v___f_2113_, 6, v_toApplicative_2095_);
lean_closure_set(v___f_2113_, 7, v___x_2112_);
v___x_2114_ = lean_nat_add(v_i_2097_, v___x_2111_);
v___x_2115_ = lean_array_push(v_xs_2098_, v_x_2110_);
v___x_2116_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2099_, v_inst_2100_, v_inst_2101_, v_inst_2102_, v_info_2103_, v_fixed_2104_, v_used_2105_, v_body_2106_, v___x_2114_, v___x_2115_);
v___x_2117_ = lean_apply_4(v_toBind_2107_, lean_box(0), lean_box(0), v___x_2116_, v___f_2113_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_info_2123_, lean_object* v_fixed_2124_, lean_object* v_used_2125_, lean_object* v_e_2126_, lean_object* v_i_2127_, lean_object* v_xs_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2119_, v_inst_2120_, v_inst_2121_, v_inst_2122_, v_info_2123_, v_fixed_2124_, v_used_2125_, v_e_2126_, v_i_2127_, v_xs_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_2130_){
_start:
{
switch(v_x_2130_)
{
case 0:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
return v___x_2131_;
}
case 1:
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_unsigned_to_nat(1u);
return v___x_2132_;
}
default: 
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_unsigned_to_nat(2u);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2134_){
_start:
{
uint8_t v_x_boxed_2135_; lean_object* v_res_2136_; 
v_x_boxed_2135_ = lean_unbox(v_x_2134_);
v_res_2136_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t v_x_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object* v_x_2139_){
_start:
{
uint8_t v_x_4__boxed_2140_; lean_object* v_res_2141_; 
v_x_4__boxed_2140_ = lean_unbox(v_x_2139_);
v_res_2141_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_2140_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2142_){
_start:
{
lean_inc(v_k_2142_);
return v_k_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2143_);
lean_dec(v_k_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2145_, lean_object* v_ctorIdx_2146_, uint8_t v_t_2147_, lean_object* v_h_2148_, lean_object* v_k_2149_){
_start:
{
lean_inc(v_k_2149_);
return v_k_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2150_, lean_object* v_ctorIdx_2151_, lean_object* v_t_2152_, lean_object* v_h_2153_, lean_object* v_k_2154_){
_start:
{
uint8_t v_t_boxed_2155_; lean_object* v_res_2156_; 
v_t_boxed_2155_ = lean_unbox(v_t_2152_);
v_res_2156_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2150_, v_ctorIdx_2151_, v_t_boxed_2155_, v_h_2153_, v_k_2154_);
lean_dec(v_k_2154_);
lean_dec(v_ctorIdx_2151_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2157_){
_start:
{
lean_inc(v_no_2157_);
return v_no_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2158_);
lean_dec(v_no_2158_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2160_, uint8_t v_t_2161_, lean_object* v_h_2162_, lean_object* v_no_2163_){
_start:
{
lean_inc(v_no_2163_);
return v_no_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2164_, lean_object* v_t_2165_, lean_object* v_h_2166_, lean_object* v_no_2167_){
_start:
{
uint8_t v_t_boxed_2168_; lean_object* v_res_2169_; 
v_t_boxed_2168_ = lean_unbox(v_t_2165_);
v_res_2169_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2164_, v_t_boxed_2168_, v_h_2166_, v_no_2167_);
lean_dec(v_no_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2170_){
_start:
{
lean_inc(v_singlePass_2170_);
return v_singlePass_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2171_);
lean_dec(v_singlePass_2171_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2173_, uint8_t v_t_2174_, lean_object* v_h_2175_, lean_object* v_singlePass_2176_){
_start:
{
lean_inc(v_singlePass_2176_);
return v_singlePass_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2177_, lean_object* v_t_2178_, lean_object* v_h_2179_, lean_object* v_singlePass_2180_){
_start:
{
uint8_t v_t_boxed_2181_; lean_object* v_res_2182_; 
v_t_boxed_2181_ = lean_unbox(v_t_2178_);
v_res_2182_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2177_, v_t_boxed_2181_, v_h_2179_, v_singlePass_2180_);
lean_dec(v_singlePass_2180_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2183_){
_start:
{
lean_inc(v_twoPasses_2183_);
return v_twoPasses_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2184_);
lean_dec(v_twoPasses_2184_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2186_, uint8_t v_t_2187_, lean_object* v_h_2188_, lean_object* v_twoPasses_2189_){
_start:
{
lean_inc(v_twoPasses_2189_);
return v_twoPasses_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2190_, lean_object* v_t_2191_, lean_object* v_h_2192_, lean_object* v_twoPasses_2193_){
_start:
{
uint8_t v_t_boxed_2194_; lean_object* v_res_2195_; 
v_t_boxed_2194_ = lean_unbox(v_t_2191_);
v_res_2195_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2190_, v_t_boxed_2194_, v_h_2192_, v_twoPasses_2193_);
lean_dec(v_twoPasses_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2196_, lean_object* v_b_2197_, lean_object* v_c_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_apply_7(v_k_2196_, v_b_2197_, v_c_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, lean_box(0));
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2205_, lean_object* v_b_2206_, lean_object* v_c_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2205_, v_b_2206_, v_c_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2214_, lean_object* v_k_2215_, uint8_t v_cleanupAnnotations_2216_, uint8_t v_preserveNondepLet_2217_, uint8_t v_nondepLetOnly_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___f_2224_; uint8_t v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2224_, 0, v_k_2215_);
v___x_2225_ = 0;
v___x_2226_ = 1;
v___x_2227_ = lean_box(0);
v___x_2228_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2214_, v___x_2225_, v___x_2226_, v_preserveNondepLet_2217_, v_nondepLetOnly_2218_, v___x_2227_, v___f_2224_, v_cleanupAnnotations_2216_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_a_2237_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2228_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2228_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2245_, lean_object* v_k_2246_, lean_object* v_cleanupAnnotations_2247_, lean_object* v_preserveNondepLet_2248_, lean_object* v_nondepLetOnly_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2255_; uint8_t v_preserveNondepLet_boxed_2256_; uint8_t v_nondepLetOnly_boxed_2257_; lean_object* v_res_2258_; 
v_cleanupAnnotations_boxed_2255_ = lean_unbox(v_cleanupAnnotations_2247_);
v_preserveNondepLet_boxed_2256_ = lean_unbox(v_preserveNondepLet_2248_);
v_nondepLetOnly_boxed_2257_ = lean_unbox(v_nondepLetOnly_2249_);
v_res_2258_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2245_, v_k_2246_, v_cleanupAnnotations_boxed_2255_, v_preserveNondepLet_boxed_2256_, v_nondepLetOnly_boxed_2257_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2259_, lean_object* v_e_2260_, lean_object* v_k_2261_, uint8_t v_cleanupAnnotations_2262_, uint8_t v_preserveNondepLet_2263_, uint8_t v_nondepLetOnly_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2260_, v_k_2261_, v_cleanupAnnotations_2262_, v_preserveNondepLet_2263_, v_nondepLetOnly_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2271_, lean_object* v_e_2272_, lean_object* v_k_2273_, lean_object* v_cleanupAnnotations_2274_, lean_object* v_preserveNondepLet_2275_, lean_object* v_nondepLetOnly_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2282_; uint8_t v_preserveNondepLet_boxed_2283_; uint8_t v_nondepLetOnly_boxed_2284_; lean_object* v_res_2285_; 
v_cleanupAnnotations_boxed_2282_ = lean_unbox(v_cleanupAnnotations_2274_);
v_preserveNondepLet_boxed_2283_ = lean_unbox(v_preserveNondepLet_2275_);
v_nondepLetOnly_boxed_2284_ = lean_unbox(v_nondepLetOnly_2276_);
v_res_2285_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2271_, v_e_2272_, v_k_2273_, v_cleanupAnnotations_boxed_2282_, v_preserveNondepLet_boxed_2283_, v_nondepLetOnly_boxed_2284_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_snd_2292_; lean_object* v_fst_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2348_; 
v_snd_2292_ = lean_ctor_get(v_b_2287_, 1);
v_fst_2293_ = lean_ctor_get(v_b_2287_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_b_2287_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2295_ = v_b_2287_;
v_isShared_2296_ = v_isSharedCheck_2348_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_snd_2292_);
lean_inc(v_fst_2293_);
lean_dec(v_b_2287_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2348_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; lean_object* v_snd_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2347_; 
v_fst_2297_ = lean_ctor_get(v_snd_2292_, 0);
v_snd_2298_ = lean_ctor_get(v_snd_2292_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_snd_2292_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2300_ = v_snd_2292_;
v_isShared_2301_ = v_isSharedCheck_2347_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_snd_2298_);
lean_inc(v_fst_2297_);
lean_dec(v_snd_2292_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2347_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_nat_dec_lt(v___x_2302_, v_snd_2298_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2305_; 
lean_dec_ref(v___y_2288_);
if (v_isShared_2301_ == 0)
{
v___x_2305_ = v___x_2300_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_snd_2298_);
v___x_2305_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___x_2305_);
v___x_2307_ = v___x_2295_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_fst_2293_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
}
}
else
{
lean_object* v_fvarSet_2311_; lean_object* v___x_2312_; lean_object* v_i_2313_; lean_object* v___x_2314_; lean_object* v_x_2315_; lean_object* v_xFVarId_2316_; uint8_t v___x_2317_; 
v_fvarSet_2311_ = lean_ctor_get(v_fst_2293_, 1);
v___x_2312_ = lean_unsigned_to_nat(1u);
v_i_2313_ = lean_nat_sub(v_snd_2298_, v___x_2312_);
lean_dec(v_snd_2298_);
v___x_2314_ = l_Lean_instInhabitedExpr;
v_x_2315_ = lean_array_get_borrowed(v___x_2314_, v_xs_2286_, v_i_2313_);
v_xFVarId_2316_ = l_Lean_Expr_fvarId_x21(v_x_2315_);
v___x_2317_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_xFVarId_2316_, v_fvarSet_2311_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2319_; 
lean_dec(v_xFVarId_2316_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v_i_2313_);
v___x_2319_ = v___x_2300_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_fst_2297_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_i_2313_);
v___x_2319_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2321_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___x_2319_);
v___x_2321_ = v___x_2295_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2293_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
v_b_2287_ = v___x_2321_;
goto _start;
}
}
}
else
{
lean_object* v___x_2325_; 
lean_inc_ref(v___y_2288_);
v___x_2325_ = l_Lean_FVarId_getDecl___redArg(v_xFVarId_2316_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = l_Lean_LocalDecl_type(v_a_2326_);
v___x_2328_ = l_Lean_collectFVars(v_fst_2293_, v___x_2327_);
v___x_2329_ = l_Lean_LocalDecl_value(v_a_2326_, v___x_2317_);
lean_dec(v_a_2326_);
v___x_2330_ = l_Lean_collectFVars(v___x_2328_, v___x_2329_);
lean_inc(v_x_2315_);
v___x_2331_ = lean_array_push(v_fst_2297_, v_x_2315_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v_i_2313_);
lean_ctor_set(v___x_2300_, 0, v___x_2331_);
v___x_2333_ = v___x_2300_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_i_2313_);
v___x_2333_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___x_2333_);
lean_ctor_set(v___x_2295_, 0, v___x_2330_);
v___x_2335_ = v___x_2295_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
v_b_2287_ = v___x_2335_;
goto _start;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_i_2313_);
lean_del_object(v___x_2300_);
lean_dec(v_fst_2297_);
lean_del_object(v___x_2295_);
lean_dec(v_fst_2293_);
lean_dec_ref(v___y_2288_);
v_a_2339_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2325_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2325_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2349_, v_b_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec_ref(v_xs_2349_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2356_, lean_object* v_e_2357_, lean_object* v_xs_2358_, lean_object* v_body_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_s_2368_; lean_object* v_i_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2356_);
lean_ctor_set(v___x_2367_, 2, v___x_2366_);
lean_inc_ref(v_body_2359_);
v_s_2368_ = l_Lean_collectFVars(v___x_2367_, v_body_2359_);
v_i_2369_ = lean_array_get_size(v_xs_2358_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2366_);
lean_ctor_set(v___x_2370_, 1, v_i_2369_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_s_2368_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
lean_inc_ref(v___y_2360_);
v___x_2372_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2358_, v___x_2371_, v___y_2360_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2388_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2388_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2388_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v_snd_2377_; lean_object* v_fst_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_snd_2377_ = lean_ctor_get(v_a_2373_, 1);
lean_inc(v_snd_2377_);
lean_dec(v_a_2373_);
v_fst_2378_ = lean_ctor_get(v_snd_2377_, 0);
lean_inc(v_fst_2378_);
lean_dec(v_snd_2377_);
v___x_2379_ = lean_array_get_size(v_fst_2378_);
v___x_2380_ = lean_nat_dec_eq(v___x_2379_, v_i_2369_);
if (v___x_2380_ == 0)
{
uint8_t v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; 
lean_del_object(v___x_2375_);
lean_dec_ref(v_e_2357_);
v___x_2381_ = 1;
v___x_2382_ = l_Array_reverse___redArg(v_fst_2378_);
v___x_2383_ = 1;
v___x_2384_ = l_Lean_Meta_mkLetFVars(v___x_2382_, v_body_2359_, v___x_2381_, v___x_2380_, v___x_2383_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v___x_2382_);
return v___x_2384_;
}
else
{
lean_object* v___x_2386_; 
lean_dec(v_fst_2378_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_body_2359_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v_e_2357_);
v___x_2386_ = v___x_2375_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_e_2357_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_body_2359_);
lean_dec_ref(v_e_2357_);
v_a_2389_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2372_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2372_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2397_, lean_object* v_e_2398_, lean_object* v_xs_2399_, lean_object* v_body_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2397_, v_e_2398_, v_xs_2399_, v_body_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v_xs_2399_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v___f_2414_; uint8_t v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2413_ = lean_box(1);
lean_inc_ref(v_e_2407_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2414_, 0, v___x_2413_);
lean_closure_set(v___f_2414_, 1, v_e_2407_);
v___x_2415_ = 0;
v___x_2416_ = 1;
v___x_2417_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2407_, v___f_2414_, v___x_2415_, v___x_2416_, v___x_2415_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_zetaUnused(v_e_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2425_, v_b_2426_, v___y_2427_, v___y_2429_, v___y_2430_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2433_, lean_object* v_b_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2433_, v_b_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v_xs_2433_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2445_, lean_object* v_source_2446_, lean_object* v_result_2447_, uint8_t v_keepUnused_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
uint8_t v_modified_2454_; 
v_modified_2454_ = lean_ctor_get_uint8(v_result_2447_, sizeof(void*)*5);
if (v_modified_2454_ == 0)
{
if (v_keepUnused_2448_ == 0)
{
lean_object* v_exprType_2455_; lean_object* v___x_2456_; 
v_exprType_2455_ = lean_ctor_get(v_result_2447_, 1);
lean_inc_ref(v_exprType_2455_);
lean_dec_ref(v_result_2447_);
lean_inc_ref(v_source_2446_);
v___x_2456_ = l_Lean_Meta_zetaUnused(v_source_2446_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2475_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2475_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2475_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_expr_eqv(v_a_2457_, v_source_2446_);
lean_dec_ref(v_source_2446_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_u_2445_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_mkConst(v___x_2462_, v___x_2464_);
lean_inc(v_a_2457_);
v___x_2466_ = l_Lean_mkAppB(v___x_2465_, v_exprType_2455_, v_a_2457_);
v___x_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2457_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2467_);
v___x_2469_ = v___x_2459_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_dec(v_a_2457_);
lean_dec_ref(v_exprType_2455_);
lean_dec(v_u_2445_);
v___x_2471_ = lean_box(0);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2471_);
v___x_2473_ = v___x_2459_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_exprType_2455_);
lean_dec_ref(v_source_2446_);
lean_dec(v_u_2445_);
v_a_2476_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2456_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2456_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_result_2447_);
lean_dec_ref(v_source_2446_);
lean_dec(v_u_2445_);
v___x_2484_ = lean_box(0);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
else
{
lean_object* v_expr_2486_; lean_object* v_exprType_2487_; lean_object* v_exprInit_2488_; lean_object* v_exprResult_2489_; lean_object* v_proof_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_proof_2498_; 
v_expr_2486_ = lean_ctor_get(v_result_2447_, 0);
lean_inc_ref(v_expr_2486_);
v_exprType_2487_ = lean_ctor_get(v_result_2447_, 1);
lean_inc_ref(v_exprType_2487_);
v_exprInit_2488_ = lean_ctor_get(v_result_2447_, 2);
lean_inc_ref(v_exprInit_2488_);
v_exprResult_2489_ = lean_ctor_get(v_result_2447_, 3);
lean_inc_ref(v_exprResult_2489_);
v_proof_2490_ = lean_ctor_get(v_result_2447_, 4);
lean_inc_ref(v_proof_2490_);
lean_dec_ref(v_result_2447_);
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2492_ = lean_box(0);
v___x_2493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_u_2445_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
lean_inc_ref(v___x_2493_);
v___x_2494_ = l_Lean_mkConst(v___x_2491_, v___x_2493_);
lean_inc_ref(v_exprType_2487_);
lean_inc_ref(v___x_2494_);
v___x_2495_ = l_Lean_mkApp3(v___x_2494_, v_exprType_2487_, v_exprInit_2488_, v_expr_2486_);
v___x_2496_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2490_, v___x_2495_);
lean_inc_ref(v_exprResult_2489_);
lean_inc_ref(v_source_2446_);
lean_inc_ref(v_exprType_2487_);
v___x_2497_ = l_Lean_mkApp3(v___x_2494_, v_exprType_2487_, v_source_2446_, v_exprResult_2489_);
v_proof_2498_ = l_Lean_Meta_mkExpectedPropHint(v___x_2496_, v___x_2497_);
if (v_keepUnused_2448_ == 0)
{
lean_object* v___x_2499_; 
lean_inc_ref(v_exprResult_2489_);
v___x_2499_ = l_Lean_Meta_zetaUnused(v_exprResult_2489_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2519_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2519_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2519_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_expr_eqv(v_a_2500_, v_exprResult_2489_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2493_);
v___x_2506_ = l_Lean_mkConst(v___x_2505_, v___x_2493_);
v___x_2507_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2508_ = l_Lean_mkConst(v___x_2507_, v___x_2493_);
lean_inc(v_a_2500_);
lean_inc_ref(v_exprType_2487_);
v___x_2509_ = l_Lean_mkAppB(v___x_2508_, v_exprType_2487_, v_a_2500_);
lean_inc(v_a_2500_);
v___x_2510_ = l_Lean_mkApp6(v___x_2506_, v_exprType_2487_, v_source_2446_, v_exprResult_2489_, v_a_2500_, v_proof_2498_, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_a_2500_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2511_);
v___x_2513_ = v___x_2502_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
lean_dec(v_a_2500_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_exprType_2487_);
lean_dec_ref(v_source_2446_);
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_exprResult_2489_);
lean_ctor_set(v___x_2515_, 1, v_proof_2498_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2515_);
v___x_2517_ = v___x_2502_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v_proof_2498_);
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_exprResult_2489_);
lean_dec_ref(v_exprType_2487_);
lean_dec_ref(v_source_2446_);
v_a_2520_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2499_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2499_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_exprType_2487_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_source_2446_);
v___x_2528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_exprResult_2489_);
lean_ctor_set(v___x_2528_, 1, v_proof_2498_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2530_, lean_object* v_source_2531_, lean_object* v_result_2532_, lean_object* v_keepUnused_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
uint8_t v_keepUnused_boxed_2539_; lean_object* v_res_2540_; 
v_keepUnused_boxed_2539_ = lean_unbox(v_keepUnused_2533_);
v_res_2540_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2530_, v_source_2531_, v_result_2532_, v_keepUnused_boxed_2539_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2541_, lean_object* v_e_2542_, lean_object* v_inst_2543_, uint8_t v_zetaUnusedMode_2544_, uint8_t v___x_2545_, uint8_t v___x_2546_, lean_object* v_r_2547_){
_start:
{
uint8_t v___y_2549_; 
switch(v_zetaUnusedMode_2544_)
{
case 0:
{
v___y_2549_ = v___x_2545_;
goto v___jp_2548_;
}
case 1:
{
v___y_2549_ = v___x_2545_;
goto v___jp_2548_;
}
default: 
{
v___y_2549_ = v___x_2546_;
goto v___jp_2548_;
}
}
v___jp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_box(v___y_2549_);
v___x_2551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2551_, 0, v_level_2541_);
lean_closure_set(v___x_2551_, 1, v_e_2542_);
lean_closure_set(v___x_2551_, 2, v_r_2547_);
lean_closure_set(v___x_2551_, 3, v___x_2550_);
v___x_2552_ = lean_apply_2(v_inst_2543_, lean_box(0), v___x_2551_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2553_, lean_object* v_e_2554_, lean_object* v_inst_2555_, lean_object* v_zetaUnusedMode_2556_, lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v_r_2559_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2560_; uint8_t v___x_362__boxed_2561_; uint8_t v___x_363__boxed_2562_; lean_object* v_res_2563_; 
v_zetaUnusedMode_boxed_2560_ = lean_unbox(v_zetaUnusedMode_2556_);
v___x_362__boxed_2561_ = lean_unbox(v___x_2557_);
v___x_363__boxed_2562_ = lean_unbox(v___x_2558_);
v_res_2563_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2553_, v_e_2554_, v_inst_2555_, v_zetaUnusedMode_boxed_2560_, v___x_362__boxed_2561_, v___x_363__boxed_2562_, v_r_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_info_2569_, lean_object* v_e_2570_, lean_object* v___x_2571_, lean_object* v_toBind_2572_, lean_object* v___f_2573_, lean_object* v_____x_2574_){
_start:
{
lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_fst_2575_ = lean_ctor_get(v_____x_2574_, 0);
lean_inc(v_fst_2575_);
v_snd_2576_ = lean_ctor_get(v_____x_2574_, 1);
lean_inc(v_snd_2576_);
lean_dec_ref(v_____x_2574_);
v___x_2577_ = lean_mk_empty_array_with_capacity(v___x_2564_);
v___x_2578_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2565_, v_inst_2566_, v_inst_2567_, v_inst_2568_, v_info_2569_, v_fst_2575_, v_snd_2576_, v_e_2570_, v___x_2571_, v___x_2577_);
v___x_2579_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2578_, v___f_2573_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_info_2585_, lean_object* v_e_2586_, lean_object* v___x_2587_, lean_object* v_toBind_2588_, lean_object* v___f_2589_, lean_object* v_____x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2580_, v_inst_2581_, v_inst_2582_, v_inst_2583_, v_inst_2584_, v_info_2585_, v_e_2586_, v___x_2587_, v_toBind_2588_, v___f_2589_, v_____x_2590_);
lean_dec(v___x_2580_);
return v_res_2591_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2594_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2595_ = lean_unsigned_to_nat(2u);
v___x_2596_ = lean_unsigned_to_nat(456u);
v___x_2597_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2599_ = l_mkPanicMessageWithDecl(v___x_2598_, v___x_2597_, v___x_2596_, v___x_2595_, v___x_2594_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2600_, lean_object* v_inst_2601_, uint8_t v_zetaUnusedMode_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_toBind_2606_, lean_object* v_info_2607_){
_start:
{
lean_object* v_haveInfo_2608_; lean_object* v_level_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_haveInfo_2608_ = lean_ctor_get(v_info_2607_, 0);
v_level_2609_ = lean_ctor_get(v_info_2607_, 5);
v___x_2610_ = lean_array_get_size(v_haveInfo_2608_);
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_nat_dec_eq(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; uint8_t v___y_2620_; 
v___x_2613_ = 1;
v___x_2614_ = lean_box(v_zetaUnusedMode_2602_);
v___x_2615_ = lean_box(v___x_2613_);
v___x_2616_ = lean_box(v___x_2612_);
lean_inc(v_inst_2601_);
lean_inc_ref(v_e_2600_);
lean_inc(v_level_2609_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2617_, 0, v_level_2609_);
lean_closure_set(v___f_2617_, 1, v_e_2600_);
lean_closure_set(v___f_2617_, 2, v_inst_2601_);
lean_closure_set(v___f_2617_, 3, v___x_2614_);
lean_closure_set(v___f_2617_, 4, v___x_2615_);
lean_closure_set(v___f_2617_, 5, v___x_2616_);
lean_inc(v_toBind_2606_);
lean_inc_ref(v_info_2607_);
lean_inc(v_inst_2601_);
v___f_2618_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2618_, 0, v___x_2610_);
lean_closure_set(v___f_2618_, 1, v_inst_2603_);
lean_closure_set(v___f_2618_, 2, v_inst_2601_);
lean_closure_set(v___f_2618_, 3, v_inst_2604_);
lean_closure_set(v___f_2618_, 4, v_inst_2605_);
lean_closure_set(v___f_2618_, 5, v_info_2607_);
lean_closure_set(v___f_2618_, 6, v_e_2600_);
lean_closure_set(v___f_2618_, 7, v___x_2611_);
lean_closure_set(v___f_2618_, 8, v_toBind_2606_);
lean_closure_set(v___f_2618_, 9, v___f_2617_);
switch(v_zetaUnusedMode_2602_)
{
case 0:
{
v___y_2620_ = v___x_2613_;
goto v___jp_2619_;
}
case 2:
{
v___y_2620_ = v___x_2613_;
goto v___jp_2619_;
}
default: 
{
v___y_2620_ = v___x_2612_;
goto v___jp_2619_;
}
}
v___jp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_box(v___y_2620_);
v___x_2622_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2622_, 0, v_info_2607_);
lean_closure_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_apply_2(v_inst_2601_, lean_box(0), v___x_2622_);
v___x_2624_ = lean_apply_4(v_toBind_2606_, lean_box(0), lean_box(0), v___x_2623_, v___f_2618_);
return v___x_2624_;
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v_info_2607_);
lean_dec(v_toBind_2606_);
lean_dec_ref(v_inst_2605_);
lean_dec_ref(v_inst_2604_);
lean_dec(v_inst_2601_);
lean_dec_ref(v_e_2600_);
v___x_2625_ = lean_box(0);
v___x_2626_ = l_instInhabitedOfMonad___redArg(v_inst_2603_, v___x_2625_);
v___x_2627_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2628_ = l_panic___redArg(v___x_2626_, v___x_2627_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2629_, lean_object* v_inst_2630_, lean_object* v_zetaUnusedMode_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_toBind_2635_, lean_object* v_info_2636_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2637_; lean_object* v_res_2638_; 
v_zetaUnusedMode_boxed_2637_ = lean_unbox(v_zetaUnusedMode_2631_);
v_res_2638_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2629_, v_inst_2630_, v_zetaUnusedMode_boxed_2637_, v_inst_2632_, v_inst_2633_, v_inst_2634_, v_toBind_2635_, v_info_2636_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_e_2643_, uint8_t v_zetaUnusedMode_2644_){
_start:
{
lean_object* v_toBind_2645_; lean_object* v___x_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_toBind_2645_ = lean_ctor_get(v_inst_2639_, 1);
lean_inc(v_toBind_2645_);
v___x_2646_ = lean_box(v_zetaUnusedMode_2644_);
lean_inc(v_toBind_2645_);
lean_inc(v_inst_2640_);
lean_inc_ref(v_e_2643_);
v___f_2647_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2647_, 0, v_e_2643_);
lean_closure_set(v___f_2647_, 1, v_inst_2640_);
lean_closure_set(v___f_2647_, 2, v___x_2646_);
lean_closure_set(v___f_2647_, 3, v_inst_2639_);
lean_closure_set(v___f_2647_, 4, v_inst_2641_);
lean_closure_set(v___f_2647_, 5, v_inst_2642_);
lean_closure_set(v___f_2647_, 6, v_toBind_2645_);
v___x_2648_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2648_, 0, v_e_2643_);
v___x_2649_ = lean_apply_2(v_inst_2640_, lean_box(0), v___x_2648_);
v___x_2650_ = lean_apply_4(v_toBind_2645_, lean_box(0), lean_box(0), v___x_2649_, v___f_2647_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_e_2655_, lean_object* v_zetaUnusedMode_2656_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2657_; lean_object* v_res_2658_; 
v_zetaUnusedMode_boxed_2657_ = lean_unbox(v_zetaUnusedMode_2656_);
v_res_2658_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2651_, v_inst_2652_, v_inst_2653_, v_inst_2654_, v_e_2655_, v_zetaUnusedMode_boxed_2657_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_e_2664_, uint8_t v_zetaUnusedMode_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2660_, v_inst_2661_, v_inst_2662_, v_inst_2663_, v_e_2664_, v_zetaUnusedMode_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_e_2672_, lean_object* v_zetaUnusedMode_2673_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2674_; lean_object* v_res_2675_; 
v_zetaUnusedMode_boxed_2674_ = lean_unbox(v_zetaUnusedMode_2673_);
v_res_2675_ = l_Lean_Meta_simpHaveTelescope(v_m_2667_, v_inst_2668_, v_inst_2669_, v_inst_2670_, v_inst_2671_, v_e_2672_, v_zetaUnusedMode_boxed_2674_);
return v_res_2675_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MonadSimp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HaveTelescope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default = _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default();
lean_mark_persistent(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default);
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
