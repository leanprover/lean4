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
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "have telescope; simplifying body "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3;
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
lean_object* v_keyedConfig_35_; uint8_t v_trackZetaDelta_36_; lean_object* v_zetaDeltaSet_37_; lean_object* v_localInstances_38_; lean_object* v_defEqCtx_x3f_39_; lean_object* v_synthPendingDepth_40_; lean_object* v_canUnfold_x3f_41_; uint8_t v_univApprox_42_; uint8_t v_inTypeClassResolution_43_; uint8_t v_cacheInferType_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
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
lean_inc(v_canUnfold_x3f_41_);
lean_inc(v_synthPendingDepth_40_);
lean_inc(v_defEqCtx_x3f_39_);
lean_inc_ref(v_localInstances_38_);
lean_inc(v_zetaDeltaSet_37_);
lean_inc_ref(v_keyedConfig_35_);
v___x_45_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_45_, 0, v_keyedConfig_35_);
lean_ctor_set(v___x_45_, 1, v_zetaDeltaSet_37_);
lean_ctor_set(v___x_45_, 2, v_lctx_28_);
lean_ctor_set(v___x_45_, 3, v_localInstances_38_);
lean_ctor_set(v___x_45_, 4, v_defEqCtx_x3f_39_);
lean_ctor_set(v___x_45_, 5, v_synthPendingDepth_40_);
lean_ctor_set(v___x_45_, 6, v_canUnfold_x3f_41_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7, v_trackZetaDelta_36_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7 + 1, v_univApprox_42_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7 + 2, v_inTypeClassResolution_43_);
lean_ctor_set_uint8(v___x_45_, sizeof(void*)*7 + 3, v_cacheInferType_44_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
v___x_46_ = lean_apply_5(v_x_29_, v___x_45_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object* v_lctx_47_, lean_object* v_x_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_47_, v_x_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object* v_00_u03b1_55_, lean_object* v_lctx_56_, lean_object* v_x_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_56_, v_x_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(lean_object* v_00_u03b1_64_, lean_object* v_lctx_65_, lean_object* v_x_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(v_00_u03b1_64_, v_lctx_65_, v_x_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
return v_x_73_;
}
else
{
lean_object* v_key_75_; lean_object* v_value_76_; lean_object* v_tail_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_100_; 
v_key_75_ = lean_ctor_get(v_x_74_, 0);
v_value_76_ = lean_ctor_get(v_x_74_, 1);
v_tail_77_ = lean_ctor_get(v_x_74_, 2);
v_isSharedCheck_100_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_100_ == 0)
{
v___x_79_ = v_x_74_;
v_isShared_80_ = v_isSharedCheck_100_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_tail_77_);
lean_inc(v_value_76_);
lean_inc(v_key_75_);
lean_dec(v_x_74_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_100_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v_fold_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_81_ = lean_array_get_size(v_x_73_);
v___x_82_ = lean_uint64_of_nat(v_key_75_);
v___x_83_ = 32ULL;
v___x_84_ = lean_uint64_shift_right(v___x_82_, v___x_83_);
v_fold_85_ = lean_uint64_xor(v___x_82_, v___x_84_);
v___x_86_ = 16ULL;
v___x_87_ = lean_uint64_shift_right(v_fold_85_, v___x_86_);
v___x_88_ = lean_uint64_xor(v_fold_85_, v___x_87_);
v___x_89_ = lean_uint64_to_usize(v___x_88_);
v___x_90_ = lean_usize_of_nat(v___x_81_);
v___x_91_ = ((size_t)1ULL);
v___x_92_ = lean_usize_sub(v___x_90_, v___x_91_);
v___x_93_ = lean_usize_land(v___x_89_, v___x_92_);
v___x_94_ = lean_array_uget_borrowed(v_x_73_, v___x_93_);
lean_inc(v___x_94_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 2, v___x_94_);
v___x_96_ = v___x_79_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_key_75_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_value_76_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v___x_94_);
v___x_96_ = v_reuseFailAlloc_99_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; 
v___x_97_ = lean_array_uset(v_x_73_, v___x_93_, v___x_96_);
v_x_73_ = v___x_97_;
v_x_74_ = v_tail_77_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(lean_object* v_i_101_, lean_object* v_source_102_, lean_object* v_target_103_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_array_get_size(v_source_102_);
v___x_105_ = lean_nat_dec_lt(v_i_101_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec_ref(v_source_102_);
lean_dec(v_i_101_);
return v_target_103_;
}
else
{
lean_object* v_es_106_; lean_object* v___x_107_; lean_object* v_source_108_; lean_object* v_target_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_es_106_ = lean_array_fget(v_source_102_, v_i_101_);
v___x_107_ = lean_box(0);
v_source_108_ = lean_array_fset(v_source_102_, v_i_101_, v___x_107_);
v_target_109_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_target_103_, v_es_106_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_i_101_, v___x_110_);
lean_dec(v_i_101_);
v_i_101_ = v___x_111_;
v_source_102_ = v_source_108_;
v_target_103_ = v_target_109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(lean_object* v_data_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_nbuckets_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_114_ = lean_array_get_size(v_data_113_);
v___x_115_ = lean_unsigned_to_nat(2u);
v_nbuckets_116_ = lean_nat_mul(v___x_114_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_box(0);
v___x_119_ = lean_mk_array(v_nbuckets_116_, v___x_118_);
v___x_120_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v___x_117_, v_data_113_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object* v_a_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
else
{
lean_object* v_key_124_; lean_object* v_tail_125_; uint8_t v___x_126_; 
v_key_124_ = lean_ctor_get(v_x_122_, 0);
v_tail_125_ = lean_ctor_get(v_x_122_, 2);
v___x_126_ = lean_nat_dec_eq(v_key_124_, v_a_121_);
if (v___x_126_ == 0)
{
v_x_122_ = v_tail_125_;
goto _start;
}
else
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object* v_a_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec(v_a_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object* v_m_132_, lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
lean_object* v_size_135_; lean_object* v_buckets_136_; lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v_size_135_ = lean_ctor_get(v_m_132_, 0);
v_buckets_136_ = lean_ctor_get(v_m_132_, 1);
v___x_137_ = lean_array_get_size(v_buckets_136_);
v___x_138_ = lean_uint64_of_nat(v_a_133_);
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
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_136_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_133_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_172_; 
lean_inc_ref(v_buckets_136_);
lean_inc(v_size_135_);
v_isSharedCheck_172_ = !lean_is_exclusive(v_m_132_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_173_ = lean_ctor_get(v_m_132_, 1);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_m_132_, 0);
lean_dec(v_unused_174_);
v___x_153_ = v_m_132_;
v_isShared_154_ = v_isSharedCheck_172_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_m_132_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_172_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v_size_x27_156_; lean_object* v___x_157_; lean_object* v_buckets_x27_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v_size_x27_156_ = lean_nat_add(v_size_135_, v___x_155_);
lean_dec(v_size_135_);
lean_inc(v_bkt_150_);
v___x_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_157_, 0, v_a_133_);
lean_ctor_set(v___x_157_, 1, v_b_134_);
lean_ctor_set(v___x_157_, 2, v_bkt_150_);
v_buckets_x27_158_ = lean_array_uset(v_buckets_136_, v___x_149_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(4u);
v___x_160_ = lean_nat_mul(v_size_x27_156_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_div(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_array_get_size(v_buckets_x27_158_);
v___x_164_ = lean_nat_dec_le(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v_val_165_; lean_object* v___x_167_; 
v_val_165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_buckets_x27_158_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v_val_165_);
lean_ctor_set(v___x_153_, 0, v_size_x27_156_);
v___x_167_ = v___x_153_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_val_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v_buckets_x27_158_);
lean_ctor_set(v___x_153_, 0, v_size_x27_156_);
v___x_170_ = v___x_153_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_buckets_x27_158_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_dec(v_b_134_);
lean_dec(v_a_133_);
return v_m_132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object* v_numHaves_175_, lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
return v_x_176_;
}
else
{
lean_object* v_key_178_; lean_object* v_tail_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_key_178_ = lean_ctor_get(v_x_177_, 0);
v_tail_179_ = lean_ctor_get(v_x_177_, 2);
v___x_180_ = lean_nat_sub(v_numHaves_175_, v_key_178_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_sub(v___x_180_, v___x_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_x_176_, v___x_182_, v___x_183_);
v_x_176_ = v___x_184_;
v_x_177_ = v_tail_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object* v_numHaves_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_186_, v_x_187_, v_x_188_);
lean_dec(v_x_188_);
lean_dec(v_numHaves_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object* v_numHaves_190_, lean_object* v_as_191_, size_t v_i_192_, size_t v_stop_193_, lean_object* v_b_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_eq(v_i_192_, v_stop_193_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; size_t v___x_198_; size_t v___x_199_; 
v___x_196_ = lean_array_uget_borrowed(v_as_191_, v_i_192_);
v___x_197_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_190_, v_b_194_, v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_192_, v___x_198_);
v_i_192_ = v___x_199_;
v_b_194_ = v___x_197_;
goto _start;
}
else
{
return v_b_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object* v_numHaves_201_, lean_object* v_as_202_, lean_object* v_i_203_, lean_object* v_stop_204_, lean_object* v_b_205_){
_start:
{
size_t v_i_boxed_206_; size_t v_stop_boxed_207_; lean_object* v_res_208_; 
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_stop_boxed_207_ = lean_unbox_usize(v_stop_204_);
lean_dec(v_stop_204_);
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_201_, v_as_202_, v_i_boxed_206_, v_stop_boxed_207_, v_b_205_);
lean_dec_ref(v_as_202_);
lean_dec(v_numHaves_201_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(lean_object* v_numHaves_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_buckets_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_213_ = l_Lean_Expr_collectLooseBVars(v_a_210_, v___x_211_);
v_buckets_214_ = lean_ctor_get(v___x_213_, 1);
lean_inc_ref(v_buckets_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = lean_array_get_size(v_buckets_214_);
v___x_216_ = lean_nat_dec_lt(v___x_211_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v_buckets_214_);
return v___x_212_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_le(v___x_215_, v___x_215_);
if (v___x_217_ == 0)
{
if (v___x_216_ == 0)
{
lean_dec_ref(v_buckets_214_);
return v___x_212_;
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_215_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_209_, v_buckets_214_, v___x_218_, v___x_219_, v___x_212_);
lean_dec_ref(v_buckets_214_);
return v___x_220_;
}
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_215_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_209_, v_buckets_214_, v___x_221_, v___x_222_, v___x_212_);
lean_dec_ref(v_buckets_214_);
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_224_, v_a_225_);
lean_dec(v_numHaves_224_);
return v_res_226_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_227_, lean_object* v_t_228_){
_start:
{
if (lean_obj_tag(v_t_228_) == 0)
{
lean_object* v_k_229_; lean_object* v_l_230_; lean_object* v_r_231_; uint8_t v___x_232_; 
v_k_229_ = lean_ctor_get(v_t_228_, 1);
v_l_230_ = lean_ctor_get(v_t_228_, 3);
v_r_231_ = lean_ctor_get(v_t_228_, 4);
v___x_232_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_227_, v_k_229_);
switch(v___x_232_)
{
case 0:
{
v_t_228_ = v_l_230_;
goto _start;
}
case 1:
{
uint8_t v___x_234_; 
v___x_234_ = 1;
return v___x_234_;
}
default: 
{
v_t_228_ = v_r_231_;
goto _start;
}
}
}
else
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_237_, lean_object* v_t_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_237_, v_t_238_);
lean_dec(v_t_238_);
lean_dec(v_k_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_241_, lean_object* v___x_242_, lean_object* v_n_243_, lean_object* v_j_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_zero_246_; uint8_t v_isZero_247_; 
v_zero_246_ = lean_unsigned_to_nat(0u);
v_isZero_247_ = lean_nat_dec_eq(v_j_244_, v_zero_246_);
if (v_isZero_247_ == 1)
{
lean_dec(v_j_244_);
return v_a_245_;
}
else
{
lean_object* v_one_248_; lean_object* v_n_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_one_248_ = lean_unsigned_to_nat(1u);
v_n_249_ = lean_nat_sub(v_j_244_, v_one_248_);
v___x_250_ = lean_nat_sub(v_n_243_, v_j_244_);
lean_dec(v_j_244_);
v___x_251_ = lean_array_fget_borrowed(v_fvars_241_, v___x_250_);
v___x_252_ = l_Lean_Expr_fvarId_x21(v___x_251_);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_252_, v___x_242_);
lean_dec(v___x_252_);
if (v___x_253_ == 0)
{
lean_dec(v___x_250_);
v_j_244_ = v_n_249_;
goto _start;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_245_, v___x_250_, v___x_255_);
v_j_244_ = v_n_249_;
v_a_245_ = v___x_256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_258_, lean_object* v___x_259_, lean_object* v_n_260_, lean_object* v_j_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_258_, v___x_259_, v_n_260_, v_j_261_, v_a_262_);
lean_dec(v_n_260_);
lean_dec(v___x_259_);
lean_dec_ref(v_fvars_258_);
return v_res_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = lean_unsigned_to_nat(16u);
v___x_266_ = lean_mk_array(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_272_, lean_object* v___x_273_, lean_object* v_fvars_274_, lean_object* v_info_275_, lean_object* v_bodyDeps_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc_ref(v_body_272_);
v___x_282_ = lean_infer_type(v_body_272_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v___x_282_);
lean_inc(v_a_283_);
v___x_284_ = l_Lean_Meta_getLevel(v_a_283_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_312_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_312_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_312_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_312_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_fvarSet_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_haveInfo_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_306_; 
v___x_289_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_273_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_inc(v_a_283_);
v___x_292_ = l_Lean_collectFVars(v___x_291_, v_a_283_);
v_fvarSet_293_ = lean_ctor_get(v___x_292_, 1);
lean_inc(v_fvarSet_293_);
lean_dec_ref(v___x_292_);
v___x_294_ = lean_array_get_size(v_fvars_274_);
v___x_295_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_274_, v_fvarSet_293_, v___x_294_, v___x_294_, v___x_289_);
lean_dec(v_fvarSet_293_);
v_haveInfo_296_ = lean_ctor_get(v_info_275_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_info_275_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; 
v_unused_307_ = lean_ctor_get(v_info_275_, 5);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_info_275_, 4);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_info_275_, 3);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_info_275_, 2);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_info_275_, 1);
lean_dec(v_unused_311_);
v___x_298_ = v_info_275_;
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_haveInfo_296_);
lean_dec(v_info_275_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 5, v_a_285_);
lean_ctor_set(v___x_298_, 4, v_a_283_);
lean_ctor_set(v___x_298_, 3, v_body_272_);
lean_ctor_set(v___x_298_, 2, v___x_295_);
lean_ctor_set(v___x_298_, 1, v_bodyDeps_276_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_haveInfo_296_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_bodyDeps_276_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_body_272_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v_a_283_);
lean_ctor_set(v_reuseFailAlloc_305_, 5, v_a_285_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_301_);
v___x_303_ = v___x_287_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_a_283_);
lean_dec_ref(v_bodyDeps_276_);
lean_dec_ref(v_info_275_);
lean_dec(v___x_273_);
lean_dec_ref(v_body_272_);
v_a_313_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_284_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_284_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec_ref(v_bodyDeps_276_);
lean_dec_ref(v_info_275_);
lean_dec(v___x_273_);
lean_dec_ref(v_body_272_);
v_a_321_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_282_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_282_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_329_, lean_object* v___x_330_, lean_object* v_fvars_331_, lean_object* v_info_332_, lean_object* v_bodyDeps_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_329_, v___x_330_, v_fvars_331_, v_info_332_, v_bodyDeps_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec_ref(v_fvars_331_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v_ngen_343_; lean_object* v_namePrefix_344_; lean_object* v_idx_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_374_; 
v___x_342_ = lean_st_ref_get(v___y_340_);
v_ngen_343_ = lean_ctor_get(v___x_342_, 2);
lean_inc_ref(v_ngen_343_);
lean_dec(v___x_342_);
v_namePrefix_344_ = lean_ctor_get(v_ngen_343_, 0);
v_idx_345_ = lean_ctor_get(v_ngen_343_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_ngen_343_);
if (v_isSharedCheck_374_ == 0)
{
v___x_347_ = v_ngen_343_;
v_isShared_348_ = v_isSharedCheck_374_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_idx_345_);
lean_inc(v_namePrefix_344_);
lean_dec(v_ngen_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_374_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v_env_350_; lean_object* v_nextMacroScope_351_; lean_object* v_auxDeclNGen_352_; lean_object* v_traceState_353_; lean_object* v_cache_354_; lean_object* v_messages_355_; lean_object* v_infoState_356_; lean_object* v_snapshotTasks_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_372_; 
v___x_349_ = lean_st_ref_take(v___y_340_);
v_env_350_ = lean_ctor_get(v___x_349_, 0);
v_nextMacroScope_351_ = lean_ctor_get(v___x_349_, 1);
v_auxDeclNGen_352_ = lean_ctor_get(v___x_349_, 3);
v_traceState_353_ = lean_ctor_get(v___x_349_, 4);
v_cache_354_ = lean_ctor_get(v___x_349_, 5);
v_messages_355_ = lean_ctor_get(v___x_349_, 6);
v_infoState_356_ = lean_ctor_get(v___x_349_, 7);
v_snapshotTasks_357_ = lean_ctor_get(v___x_349_, 8);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_349_, 2);
lean_dec(v_unused_373_);
v___x_359_ = v___x_349_;
v_isShared_360_ = v_isSharedCheck_372_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snapshotTasks_357_);
lean_inc(v_infoState_356_);
lean_inc(v_messages_355_);
lean_inc(v_cache_354_);
lean_inc(v_traceState_353_);
lean_inc(v_auxDeclNGen_352_);
lean_inc(v_nextMacroScope_351_);
lean_inc(v_env_350_);
lean_dec(v___x_349_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_372_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_r_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
lean_inc(v_idx_345_);
lean_inc(v_namePrefix_344_);
v_r_361_ = l_Lean_Name_num___override(v_namePrefix_344_, v_idx_345_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_idx_345_, v___x_362_);
lean_dec(v_idx_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_363_);
v___x_365_ = v___x_347_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_namePrefix_344_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_371_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 2, v___x_365_);
v___x_367_ = v___x_359_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_env_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_nextMacroScope_351_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_auxDeclNGen_352_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_traceState_353_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v_cache_354_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_messages_355_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_infoState_356_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_snapshotTasks_357_);
v___x_367_ = v_reuseFailAlloc_370_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_st_ref_set(v___y_340_, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v_r_361_);
return v___x_369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_375_);
lean_dec(v___y_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v___x_383_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_381_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_398_, lean_object* v_numHaves_399_, lean_object* v_info_400_, lean_object* v_lctx_401_, lean_object* v_fvars_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; 
v___x_408_ = lean_box(1);
if (lean_obj_tag(v_e_398_) == 8)
{
uint8_t v_nondep_418_; 
v_nondep_418_ = lean_ctor_get_uint8(v_e_398_, sizeof(void*)*4 + 8);
if (v_nondep_418_ == 1)
{
lean_object* v_declName_419_; lean_object* v_type_420_; lean_object* v_value_421_; lean_object* v_body_422_; lean_object* v_t_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_declName_419_ = lean_ctor_get(v_e_398_, 0);
lean_inc(v_declName_419_);
v_type_420_ = lean_ctor_get(v_e_398_, 1);
lean_inc_ref(v_type_420_);
v_value_421_ = lean_ctor_get(v_e_398_, 2);
lean_inc_ref(v_value_421_);
v_body_422_ = lean_ctor_get(v_e_398_, 3);
lean_inc_ref(v_body_422_);
lean_dec_ref(v_e_398_);
v_t_423_ = lean_expr_instantiate_rev(v_type_420_, v_fvars_402_);
lean_inc_ref(v_t_423_);
v___x_424_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_424_, 0, v_t_423_);
lean_inc_ref(v_lctx_401_);
v___x_425_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_401_, v___x_424_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_haveInfo_429_; lean_object* v_bodyDeps_430_; lean_object* v_bodyTypeDeps_431_; lean_object* v_body_432_; lean_object* v_bodyType_433_; lean_object* v_level_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_455_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref(v___x_427_);
v_haveInfo_429_ = lean_ctor_get(v_info_400_, 0);
v_bodyDeps_430_ = lean_ctor_get(v_info_400_, 1);
v_bodyTypeDeps_431_ = lean_ctor_get(v_info_400_, 2);
v_body_432_ = lean_ctor_get(v_info_400_, 3);
v_bodyType_433_ = lean_ctor_get(v_info_400_, 4);
v_level_434_ = lean_ctor_get(v_info_400_, 5);
v_isSharedCheck_455_ = !lean_is_exclusive(v_info_400_);
if (v_isSharedCheck_455_ == 0)
{
v___x_436_ = v_info_400_;
v_isShared_437_ = v_isSharedCheck_455_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_level_434_);
lean_inc(v_bodyType_433_);
lean_inc(v_body_432_);
lean_inc(v_bodyTypeDeps_431_);
lean_inc(v_bodyDeps_430_);
lean_inc(v_haveInfo_429_);
lean_dec(v_info_400_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_455_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_typeBackDeps_438_; lean_object* v_valueBackDeps_439_; lean_object* v_v_440_; lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v_typeBackDeps_438_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_399_, v_type_420_);
lean_inc_ref(v_value_421_);
v_valueBackDeps_439_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_399_, v_value_421_);
v_v_440_ = lean_expr_instantiate_rev(v_value_421_, v_fvars_402_);
lean_dec_ref(v_value_421_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = 0;
lean_inc(v_a_428_);
v___x_443_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v_a_428_);
lean_ctor_set(v___x_443_, 2, v_declName_419_);
lean_ctor_set(v___x_443_, 3, v_t_423_);
lean_ctor_set(v___x_443_, 4, v_v_440_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*5, v_nondep_418_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*5 + 1, v___x_442_);
lean_inc_ref(v___x_443_);
v___x_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_444_, 0, v_typeBackDeps_438_);
lean_ctor_set(v___x_444_, 1, v_valueBackDeps_439_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set(v___x_444_, 3, v_a_426_);
v___x_445_ = lean_array_push(v_haveInfo_429_, v___x_444_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_445_);
v___x_447_ = v___x_436_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_bodyDeps_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_bodyTypeDeps_431_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_body_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_bodyType_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_level_434_);
v___x_447_ = v_reuseFailAlloc_454_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = l_Lean_LocalContext_addDecl(v_lctx_401_, v___x_443_);
v___x_449_ = l_Lean_mkFVar(v_a_428_);
v___x_450_ = lean_array_push(v_fvars_402_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_numHaves_399_, v___x_451_);
lean_dec(v_numHaves_399_);
v_e_398_ = v_body_422_;
v_numHaves_399_ = v___x_452_;
v_info_400_ = v___x_447_;
v_lctx_401_ = v___x_448_;
v_fvars_402_ = v___x_450_;
goto _start;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec(v_a_426_);
lean_dec_ref(v_t_423_);
lean_dec_ref(v_body_422_);
lean_dec_ref(v_value_421_);
lean_dec_ref(v_type_420_);
lean_dec(v_declName_419_);
lean_dec_ref(v_fvars_402_);
lean_dec_ref(v_lctx_401_);
lean_dec_ref(v_info_400_);
lean_dec(v_numHaves_399_);
v_a_456_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_427_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_427_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_t_423_);
lean_dec_ref(v_body_422_);
lean_dec_ref(v_value_421_);
lean_dec_ref(v_type_420_);
lean_dec(v_declName_419_);
lean_dec_ref(v_fvars_402_);
lean_dec_ref(v_lctx_401_);
lean_dec_ref(v_info_400_);
lean_dec(v_numHaves_399_);
v_a_464_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_425_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_425_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
v___y_410_ = v_a_403_;
v___y_411_ = v_a_404_;
v___y_412_ = v_a_405_;
v___y_413_ = v_a_406_;
goto v___jp_409_;
}
}
else
{
v___y_410_ = v_a_403_;
v___y_411_ = v_a_404_;
v___y_412_ = v_a_405_;
v___y_413_ = v_a_406_;
goto v___jp_409_;
}
v___jp_409_:
{
lean_object* v_bodyDeps_414_; lean_object* v_body_415_; lean_object* v___f_416_; lean_object* v___x_417_; 
lean_inc_ref(v_e_398_);
v_bodyDeps_414_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_399_, v_e_398_);
lean_dec(v_numHaves_399_);
v_body_415_ = lean_expr_instantiate_rev(v_e_398_, v_fvars_402_);
lean_dec_ref(v_e_398_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_416_, 0, v_body_415_);
lean_closure_set(v___f_416_, 1, v___x_408_);
lean_closure_set(v___f_416_, 2, v_fvars_402_);
lean_closure_set(v___f_416_, 3, v_info_400_);
lean_closure_set(v___f_416_, 4, v_bodyDeps_414_);
v___x_417_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_401_, v___f_416_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_472_, lean_object* v_numHaves_473_, lean_object* v_info_474_, lean_object* v_lctx_475_, lean_object* v_fvars_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_472_, v_numHaves_473_, v_info_474_, v_lctx_475_, v_fvars_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_484_, v_a_485_, v_b_486_);
return v___x_487_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_488_, lean_object* v_k_489_, lean_object* v_t_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_489_, v_t_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_492_, lean_object* v_k_493_, lean_object* v_t_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_492_, v_k_493_, v_t_494_);
lean_dec(v_t_494_);
lean_dec(v_k_493_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_497_, lean_object* v___x_498_, lean_object* v_n_499_, lean_object* v_j_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_497_, v___x_498_, v_n_499_, v_j_500_, v_a_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_504_, lean_object* v___x_505_, lean_object* v_n_506_, lean_object* v_j_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_504_, v___x_505_, v_n_506_, v_j_507_, v_a_508_, v_a_509_);
lean_dec(v_n_506_);
lean_dec(v___x_505_);
lean_dec_ref(v_fvars_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_522_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_524_, v_x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_527_, v_a_528_, v_x_529_);
lean_dec(v_x_529_);
lean_dec(v_a_528_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_532_, lean_object* v_data_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_535_, lean_object* v_i_536_, lean_object* v_source_537_, lean_object* v_target_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_536_, v_source_537_, v_target_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_541_, v_x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Meta_getHaveTelescopeInfo___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_box(0);
v___x_550_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__2));
v___x_551_ = l_Lean_Expr_const___override(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Meta_getHaveTelescopeInfo___closed__4(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__2));
v___x_553_ = l_Lean_Level_param___override(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Meta_getHaveTelescopeInfo___closed__5(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_554_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__4, &l_Lean_Meta_getHaveTelescopeInfo___closed__4_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__4);
v___x_555_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__3, &l_Lean_Meta_getHaveTelescopeInfo___closed__3_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__3);
v___x_556_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_557_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__0));
v___x_558_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
lean_ctor_set(v___x_558_, 2, v___x_556_);
lean_ctor_set(v___x_558_, 3, v___x_555_);
lean_ctor_set(v___x_558_, 4, v___x_555_);
lean_ctor_set(v___x_558_, 5, v___x_554_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_lctx_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_lctx_565_ = lean_ctor_get(v_a_560_, 2);
lean_inc_ref(v_lctx_565_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__0));
v___x_568_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__5, &l_Lean_Meta_getHaveTelescopeInfo___closed__5_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__5);
v___x_569_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_559_, v___x_566_, v___x_568_, v_lctx_565_, v___x_567_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec_ref(v_a_560_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
return v_x_577_;
}
else
{
lean_object* v_key_579_; lean_object* v_tail_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_key_579_ = lean_ctor_get(v_x_578_, 0);
v_tail_580_ = lean_ctor_get(v_x_578_, 2);
v___x_581_ = 1;
v___x_582_ = lean_box(v___x_581_);
v___x_583_ = lean_array_set(v_x_577_, v_key_579_, v___x_582_);
v_x_577_ = v___x_583_;
v_x_578_ = v_tail_580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_585_, v_x_586_);
lean_dec(v_x_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_588_, size_t v_i_589_, size_t v_stop_590_, lean_object* v_b_591_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_eq(v_i_589_, v_stop_590_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; size_t v___x_595_; size_t v___x_596_; 
v___x_593_ = lean_array_uget_borrowed(v_as_588_, v_i_589_);
v___x_594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_591_, v___x_593_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_589_, v___x_595_);
v_i_589_ = v___x_596_;
v_b_591_ = v___x_594_;
goto _start;
}
else
{
return v_b_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_stop_600_, lean_object* v_b_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; lean_object* v_res_604_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_600_);
lean_dec(v_stop_600_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_598_, v_i_boxed_602_, v_stop_boxed_603_, v_b_601_);
lean_dec_ref(v_as_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_605_, lean_object* v_s_606_){
_start:
{
lean_object* v_buckets_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_buckets_607_ = lean_ctor_get(v_s_606_, 1);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_array_get_size(v_buckets_607_);
v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
return v_arr_605_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_le(v___x_609_, v___x_609_);
if (v___x_611_ == 0)
{
if (v___x_610_ == 0)
{
return v_arr_605_;
}
else
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((size_t)0ULL);
v___x_613_ = lean_usize_of_nat(v___x_609_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_607_, v___x_612_, v___x_613_, v_arr_605_);
return v___x_614_;
}
}
else
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((size_t)0ULL);
v___x_616_ = lean_usize_of_nat(v___x_609_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_607_, v___x_615_, v___x_616_, v_arr_605_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_618_, lean_object* v_s_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_618_, v_s_619_);
lean_dec_ref(v_s_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_621_, lean_object* v_numHaves_622_, lean_object* v___x_623_, lean_object* v_a_624_, lean_object* v_b_625_){
_start:
{
lean_object* v_a_628_; uint8_t v___x_632_; 
v___x_632_ = lean_nat_dec_lt(v_a_624_, v_upperBound_621_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v_a_624_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_b_625_);
return v___x_633_;
}
else
{
uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_634_ = 0;
v___x_635_ = lean_nat_sub(v_numHaves_622_, v_a_624_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_sub(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(v___x_634_);
v___x_639_ = lean_array_get_borrowed(v___x_638_, v_b_625_, v___x_637_);
v___x_640_ = lean_unbox(v___x_639_);
if (v___x_640_ == 0)
{
lean_dec(v___x_637_);
v_a_628_ = v_b_625_;
goto v___jp_627_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_typeBackDeps_643_; lean_object* v_valueBackDeps_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_642_ = lean_array_get_borrowed(v___x_641_, v___x_623_, v___x_637_);
lean_dec(v___x_637_);
v_typeBackDeps_643_ = lean_ctor_get(v___x_642_, 0);
v_valueBackDeps_644_ = lean_ctor_get(v___x_642_, 1);
v___x_645_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_625_, v_typeBackDeps_643_);
v___x_646_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_645_, v_valueBackDeps_644_);
v_a_628_ = v___x_646_;
goto v___jp_627_;
}
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_a_624_, v___x_629_);
lean_dec(v_a_624_);
v_a_624_ = v___x_630_;
v_b_625_ = v_a_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_647_, lean_object* v_numHaves_648_, lean_object* v___x_649_, lean_object* v_a_650_, lean_object* v_b_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_647_, v_numHaves_648_, v___x_649_, v_a_650_, v_b_651_);
lean_dec_ref(v___x_649_);
lean_dec(v_numHaves_648_);
lean_dec(v_upperBound_647_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_654_, lean_object* v_init_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_haveInfo_661_; lean_object* v_numHaves_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v_used_665_; lean_object* v___x_666_; lean_object* v_used_667_; lean_object* v___x_668_; 
v_haveInfo_661_ = lean_ctor_get(v_info_654_, 0);
v_numHaves_662_ = lean_array_get_size(v_haveInfo_661_);
v___x_663_ = 0;
v___x_664_ = lean_box(v___x_663_);
v_used_665_ = lean_mk_array(v_numHaves_662_, v___x_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
v_used_667_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_665_, v_init_655_);
v___x_668_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_662_, v_numHaves_662_, v_haveInfo_661_, v___x_666_, v_used_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_669_, lean_object* v_init_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_669_, v_init_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec_ref(v_init_670_);
lean_dec_ref(v_info_669_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_677_, lean_object* v_numHaves_678_, lean_object* v___x_679_, lean_object* v_inst_680_, lean_object* v_R_681_, lean_object* v_a_682_, lean_object* v_b_683_, lean_object* v_c_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_677_, v_numHaves_678_, v___x_679_, v_a_682_, v_b_683_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_691_, lean_object* v_numHaves_692_, lean_object* v___x_693_, lean_object* v_inst_694_, lean_object* v_R_695_, lean_object* v_a_696_, lean_object* v_b_697_, lean_object* v_c_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_691_, v_numHaves_692_, v___x_693_, v_inst_694_, v_R_695_, v_a_696_, v_b_697_, v_c_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___x_693_);
lean_dec(v_numHaves_692_);
lean_dec(v_upperBound_691_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_707_, uint8_t v_keepUnused_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_bodyDeps_714_; lean_object* v_bodyTypeDeps_715_; lean_object* v___x_716_; 
v_bodyDeps_714_ = lean_ctor_get(v_info_707_, 1);
v_bodyTypeDeps_715_ = lean_ctor_get(v_info_707_, 2);
v___x_716_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_707_, v_bodyTypeDeps_715_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_716_) == 0)
{
if (v_keepUnused_708_ == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v___x_716_);
v___x_718_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_707_, v_bodyDeps_714_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_a_717_);
lean_ctor_set(v___x_723_, 1, v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_a_717_);
v_a_728_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_718_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_718_);
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
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_745_; 
v_a_736_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_745_ == 0)
{
v___x_738_ = v___x_716_;
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_716_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_740_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_736_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_716_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_716_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_754_, lean_object* v_keepUnused_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
uint8_t v_keepUnused_boxed_761_; lean_object* v_res_762_; 
v_keepUnused_boxed_761_ = lean_unbox(v_keepUnused_755_);
v_res_762_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_754_, v_keepUnused_boxed_761_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_info_754_);
return v_res_762_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0(void){
_start:
{
uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = 0;
v___x_764_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3);
v___x_765_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
lean_ctor_set(v___x_765_, 4, v___x_764_);
lean_ctor_set_uint8(v___x_765_, sizeof(void*)*5, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default___closed__0);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_toApplicative_784_, lean_object* v_level_785_, lean_object* v_exprType_786_, lean_object* v_e_787_, uint8_t v___x_788_, lean_object* v_xs_789_, lean_object* v_____do__lift_790_){
_start:
{
if (lean_obj_tag(v_____do__lift_790_) == 0)
{
lean_object* v_toPure_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_proof_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_toPure_791_ = lean_ctor_get(v_toApplicative_784_, 1);
lean_inc(v_toPure_791_);
lean_dec_ref(v_toApplicative_784_);
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_793_ = lean_box(0);
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v_level_785_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_mkConst(v___x_792_, v___x_794_);
lean_inc_ref(v_e_787_);
lean_inc_ref(v_exprType_786_);
v_proof_796_ = l_Lean_mkAppB(v___x_795_, v_exprType_786_, v_e_787_);
lean_inc_ref_n(v_e_787_, 2);
v___x_797_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_797_, 0, v_e_787_);
lean_ctor_set(v___x_797_, 1, v_exprType_786_);
lean_ctor_set(v___x_797_, 2, v_e_787_);
lean_ctor_set(v___x_797_, 3, v_e_787_);
lean_ctor_set(v___x_797_, 4, v_proof_796_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*5, v___x_788_);
v___x_798_ = lean_apply_2(v_toPure_791_, lean_box(0), v___x_797_);
return v___x_798_;
}
else
{
lean_object* v_e_799_; lean_object* v_h_800_; lean_object* v_expr_801_; lean_object* v_proof_802_; lean_object* v___x_808_; uint8_t v___x_809_; 
lean_dec(v_level_785_);
v_e_799_ = lean_ctor_get(v_____do__lift_790_, 0);
v_h_800_ = lean_ctor_get(v_____do__lift_790_, 1);
v_expr_801_ = lean_expr_abstract(v_e_799_, v_xs_789_);
v_proof_802_ = lean_expr_abstract(v_h_800_, v_xs_789_);
lean_inc_ref(v_proof_802_);
v___x_808_ = l_Lean_Expr_cleanupAnnotations(v_proof_802_);
v___x_809_ = l_Lean_Expr_isApp(v___x_808_);
if (v___x_809_ == 0)
{
lean_dec_ref(v___x_808_);
goto v___jp_803_;
}
else
{
lean_object* v_arg_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_arg_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc_ref(v_arg_810_);
v___x_811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_808_);
v___x_812_ = l_Lean_Expr_isApp(v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v___x_811_);
lean_dec_ref(v_arg_810_);
goto v___jp_803_;
}
else
{
lean_object* v_arg_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_arg_813_ = lean_ctor_get(v___x_811_, 1);
lean_inc_ref(v_arg_813_);
v___x_814_ = l_Lean_Expr_appFnCleanup___redArg(v___x_811_);
v___x_815_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_816_ = l_Lean_Expr_isConstOf(v___x_814_, v___x_815_);
lean_dec_ref(v___x_814_);
if (v___x_816_ == 0)
{
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_810_);
goto v___jp_803_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_818_ = lean_unsigned_to_nat(3u);
v___x_819_ = l_Lean_Expr_isAppOfArity(v_arg_813_, v___x_817_, v___x_818_);
lean_dec_ref(v_arg_813_);
if (v___x_819_ == 0)
{
lean_dec_ref(v_arg_810_);
goto v___jp_803_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = l_Lean_Expr_cleanupAnnotations(v_arg_810_);
v___x_821_ = l_Lean_Expr_isApp(v___x_820_);
if (v___x_821_ == 0)
{
lean_dec_ref(v___x_820_);
goto v___jp_803_;
}
else
{
lean_object* v_arg_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_arg_822_ = lean_ctor_get(v___x_820_, 1);
lean_inc_ref(v_arg_822_);
v___x_823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_820_);
v___x_824_ = l_Lean_Expr_isApp(v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v___x_823_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v_arg_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_arg_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc_ref(v_arg_825_);
v___x_826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_823_);
v___x_827_ = l_Lean_Expr_isConstOf(v___x_826_, v___x_815_);
lean_dec_ref(v___x_826_);
if (v___x_827_ == 0)
{
lean_dec_ref(v_arg_825_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_Lean_Expr_cleanupAnnotations(v_arg_825_);
v___x_829_ = l_Lean_Expr_isApp(v___x_828_);
if (v___x_829_ == 0)
{
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v_arg_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_arg_830_ = lean_ctor_get(v___x_828_, 1);
lean_inc_ref(v_arg_830_);
v___x_831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_828_);
v___x_832_ = l_Lean_Expr_isApp(v___x_831_);
if (v___x_832_ == 0)
{
lean_dec_ref(v___x_831_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v_arg_833_; uint8_t v___y_835_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_arg_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc_ref(v_arg_833_);
v___x_839_ = l_Lean_Expr_appFnCleanup___redArg(v___x_831_);
v___x_840_ = l_Lean_Expr_isApp(v___x_839_);
if (v___x_840_ == 0)
{
lean_dec_ref(v___x_839_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = l_Lean_Expr_appFnCleanup___redArg(v___x_839_);
v___x_842_ = l_Lean_Expr_isConstOf(v___x_841_, v___x_817_);
lean_dec_ref(v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Expr_getAppFn(v_arg_822_);
if (lean_obj_tag(v___x_843_) == 4)
{
lean_object* v_declName_844_; 
v_declName_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_declName_844_);
lean_dec_ref(v___x_843_);
if (lean_obj_tag(v_declName_844_) == 1)
{
lean_object* v_pre_845_; 
v_pre_845_ = lean_ctor_get(v_declName_844_, 0);
if (lean_obj_tag(v_pre_845_) == 0)
{
lean_object* v_str_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_str_846_ = lean_ctor_get(v_declName_844_, 1);
lean_inc_ref(v_str_846_);
lean_dec_ref(v_declName_844_);
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_848_ = lean_string_dec_eq(v_str_846_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_850_ = lean_string_dec_eq(v_str_846_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_852_ = lean_string_dec_eq(v_str_846_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_854_ = lean_string_dec_eq(v_str_846_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_856_ = lean_string_dec_eq(v_str_846_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_858_ = lean_string_dec_eq(v_str_846_, v___x_857_);
lean_dec_ref(v_str_846_);
if (v___x_858_ == 0)
{
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
v___y_835_ = v___x_816_;
goto v___jp_834_;
}
}
else
{
lean_dec_ref(v_str_846_);
v___y_835_ = v___x_816_;
goto v___jp_834_;
}
}
else
{
lean_dec_ref(v_str_846_);
v___y_835_ = v___x_816_;
goto v___jp_834_;
}
}
else
{
lean_dec_ref(v_str_846_);
v___y_835_ = v___x_816_;
goto v___jp_834_;
}
}
else
{
lean_dec_ref(v_str_846_);
v___y_835_ = v___x_816_;
goto v___jp_834_;
}
}
else
{
lean_dec_ref(v_str_846_);
v___y_835_ = v___x_816_;
goto v___jp_834_;
}
}
else
{
lean_dec_ref(v_declName_844_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
}
else
{
lean_dec(v_declName_844_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
}
else
{
lean_dec_ref(v___x_843_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
}
}
v___jp_834_:
{
if (v___y_835_ == 0)
{
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
lean_dec_ref(v_arg_822_);
goto v___jp_803_;
}
else
{
lean_object* v_toPure_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_proof_802_);
lean_dec_ref(v_e_787_);
v_toPure_836_ = lean_ctor_get(v_toApplicative_784_, 1);
lean_inc(v_toPure_836_);
lean_dec_ref(v_toApplicative_784_);
v___x_837_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_837_, 0, v_arg_830_);
lean_ctor_set(v___x_837_, 1, v_exprType_786_);
lean_ctor_set(v___x_837_, 2, v_arg_833_);
lean_ctor_set(v___x_837_, 3, v_expr_801_);
lean_ctor_set(v___x_837_, 4, v_arg_822_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*5, v___x_816_);
v___x_838_ = lean_apply_2(v_toPure_836_, lean_box(0), v___x_837_);
return v___x_838_;
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
v___jp_803_:
{
lean_object* v_toPure_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_toPure_804_ = lean_ctor_get(v_toApplicative_784_, 1);
lean_inc(v_toPure_804_);
lean_dec_ref(v_toApplicative_784_);
v___x_805_ = 1;
lean_inc_ref(v_expr_801_);
v___x_806_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_806_, 0, v_expr_801_);
lean_ctor_set(v___x_806_, 1, v_exprType_786_);
lean_ctor_set(v___x_806_, 2, v_e_787_);
lean_ctor_set(v___x_806_, 3, v_expr_801_);
lean_ctor_set(v___x_806_, 4, v_proof_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*5, v___x_805_);
v___x_807_ = lean_apply_2(v_toPure_804_, lean_box(0), v___x_806_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_toApplicative_859_, lean_object* v_level_860_, lean_object* v_exprType_861_, lean_object* v_e_862_, lean_object* v___x_863_, lean_object* v_xs_864_, lean_object* v_____do__lift_865_){
_start:
{
uint8_t v___x_10170__boxed_866_; lean_object* v_res_867_; 
v___x_10170__boxed_866_ = lean_unbox(v___x_863_);
v_res_867_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_859_, v_level_860_, v_exprType_861_, v_e_862_, v___x_10170__boxed_866_, v_xs_864_, v_____do__lift_865_);
lean_dec(v_____do__lift_865_);
lean_dec_ref(v_xs_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_868_, lean_object* v_bodyType_869_, lean_object* v_xs_870_, lean_object* v_toApplicative_871_, lean_object* v_level_872_, lean_object* v_e_873_, uint8_t v___x_874_, lean_object* v_body_875_, lean_object* v_toBind_876_, lean_object* v_____r_877_){
_start:
{
lean_object* v_simp_878_; lean_object* v_exprType_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_simp_878_ = lean_ctor_get(v_inst_868_, 2);
lean_inc(v_simp_878_);
lean_dec_ref(v_inst_868_);
v_exprType_879_ = lean_expr_abstract(v_bodyType_869_, v_xs_870_);
v___x_880_ = lean_box(v___x_874_);
v___f_881_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_881_, 0, v_toApplicative_871_);
lean_closure_set(v___f_881_, 1, v_level_872_);
lean_closure_set(v___f_881_, 2, v_exprType_879_);
lean_closure_set(v___f_881_, 3, v_e_873_);
lean_closure_set(v___f_881_, 4, v___x_880_);
lean_closure_set(v___f_881_, 5, v_xs_870_);
v___x_882_ = lean_apply_1(v_simp_878_, v_body_875_);
v___x_883_ = lean_apply_4(v_toBind_876_, lean_box(0), lean_box(0), v___x_882_, v___f_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_884_, lean_object* v_bodyType_885_, lean_object* v_xs_886_, lean_object* v_toApplicative_887_, lean_object* v_level_888_, lean_object* v_e_889_, lean_object* v___x_890_, lean_object* v_body_891_, lean_object* v_toBind_892_, lean_object* v_____r_893_){
_start:
{
uint8_t v___x_10323__boxed_894_; lean_object* v_res_895_; 
v___x_10323__boxed_894_ = lean_unbox(v___x_890_);
v_res_895_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_884_, v_bodyType_885_, v_xs_886_, v_toApplicative_887_, v_level_888_, v_e_889_, v___x_10323__boxed_894_, v_body_891_, v_toBind_892_, v_____r_893_);
lean_dec_ref(v_bodyType_885_);
return v_res_895_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_cls_904_, lean_object* v___x_905_, lean_object* v___f_906_, lean_object* v_body_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_9698__overap_913_; lean_object* v___x_914_; 
lean_inc(v_cls_904_);
lean_inc_ref(v___x_902_);
lean_inc_ref(v___x_901_);
v___x_9698__overap_913_ = l_Lean_isTracingEnabledFor___redArg(v___x_901_, v___x_902_, v___x_903_, v_cls_904_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
v___x_914_ = lean_apply_5(v___x_9698__overap_913_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_936_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_936_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_936_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___x_919_; 
v___x_919_ = lean_unbox(v_a_915_);
lean_dec(v_a_915_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_body_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v_cls_904_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
v___x_920_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_toMonadRef_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_9713__overap_934_; lean_object* v___x_935_; 
lean_del_object(v___x_917_);
v___f_924_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
v___x_926_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_927_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_925_, v___x_905_, v___x_926_);
v___x_928_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_924_, v___f_906_, v___x_927_);
v_toMonadRef_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_ref(v_toMonadRef_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3);
v___x_932_ = l_Lean_MessageData_ofExpr(v_body_907_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_9713__overap_934_ = l_Lean_addTrace___redArg(v___x_901_, v___x_902_, v_toMonadRef_929_, v___x_930_, v_cls_904_, v___x_933_);
v___x_935_ = lean_apply_5(v___x_9713__overap_934_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
return v___x_935_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_body_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v_cls_904_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
v_a_937_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_914_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_914_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v_cls_948_, lean_object* v___x_949_, lean_object* v___f_950_, lean_object* v_body_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v___x_945_, v___x_946_, v___x_947_, v_cls_948_, v___x_949_, v___f_950_, v_body_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_960_, lean_object* v_type_961_, lean_object* v___y_962_, lean_object* v_value_963_, uint8_t v_nondep_964_, lean_object* v_toApplicative_965_, lean_object* v___x_966_, uint8_t v___y_967_, lean_object* v_us_968_, lean_object* v_rb_969_){
_start:
{
lean_object* v_expr_970_; lean_object* v_exprType_971_; lean_object* v_exprInit_972_; lean_object* v_exprResult_973_; lean_object* v_proof_974_; uint8_t v_modified_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1004_; 
v_expr_970_ = lean_ctor_get(v_rb_969_, 0);
v_exprType_971_ = lean_ctor_get(v_rb_969_, 1);
v_exprInit_972_ = lean_ctor_get(v_rb_969_, 2);
v_exprResult_973_ = lean_ctor_get(v_rb_969_, 3);
v_proof_974_ = lean_ctor_get(v_rb_969_, 4);
v_modified_975_ = lean_ctor_get_uint8(v_rb_969_, sizeof(void*)*5);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_rb_969_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_977_ = v_rb_969_;
v_isShared_978_ = v_isSharedCheck_1004_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_proof_974_);
lean_inc(v_exprResult_973_);
lean_inc(v_exprInit_972_);
lean_inc(v_exprType_971_);
lean_inc(v_expr_970_);
lean_dec(v_rb_969_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1004_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v_expr_981_; lean_object* v___x_982_; lean_object* v_exprType_983_; lean_object* v___x_984_; lean_object* v_exprInit_985_; lean_object* v_exprResult_986_; 
v___x_979_ = 0;
lean_inc_ref(v_type_961_);
lean_inc(v_declName_960_);
v___x_980_ = l_Lean_mkLambda(v_declName_960_, v___x_979_, v_type_961_, v_expr_970_);
lean_inc_ref(v___y_962_);
lean_inc_ref(v___x_980_);
v_expr_981_ = l_Lean_Expr_app___override(v___x_980_, v___y_962_);
lean_inc_ref(v_type_961_);
lean_inc(v_declName_960_);
v___x_982_ = l_Lean_mkLambda(v_declName_960_, v___x_979_, v_type_961_, v_exprType_971_);
lean_inc_ref(v___y_962_);
lean_inc_ref(v___x_982_);
v_exprType_983_ = l_Lean_Expr_app___override(v___x_982_, v___y_962_);
lean_inc_ref(v_type_961_);
lean_inc(v_declName_960_);
v___x_984_ = l_Lean_mkLambda(v_declName_960_, v___x_979_, v_type_961_, v_exprInit_972_);
lean_inc_ref(v___x_984_);
v_exprInit_985_ = l_Lean_Expr_app___override(v___x_984_, v_value_963_);
lean_inc_ref(v___y_962_);
lean_inc_ref(v_type_961_);
lean_inc(v_declName_960_);
v_exprResult_986_ = l_Lean_Expr_letE___override(v_declName_960_, v_type_961_, v___y_962_, v_exprResult_973_, v_nondep_964_);
if (v_modified_975_ == 0)
{
lean_object* v_toPure_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_proof_990_; lean_object* v___x_992_; 
lean_dec_ref(v___x_984_);
lean_dec_ref(v___x_982_);
lean_dec_ref(v___x_980_);
lean_dec_ref(v_proof_974_);
lean_dec(v_us_968_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_type_961_);
lean_dec(v_declName_960_);
v_toPure_987_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc(v_toPure_987_);
lean_dec_ref(v_toApplicative_965_);
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_989_ = l_Lean_mkConst(v___x_988_, v___x_966_);
lean_inc_ref(v_expr_981_);
lean_inc_ref(v_exprType_983_);
v_proof_990_ = l_Lean_mkAppB(v___x_989_, v_exprType_983_, v_expr_981_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 4, v_proof_990_);
lean_ctor_set(v___x_977_, 3, v_exprResult_986_);
lean_ctor_set(v___x_977_, 2, v_exprInit_985_);
lean_ctor_set(v___x_977_, 1, v_exprType_983_);
lean_ctor_set(v___x_977_, 0, v_expr_981_);
v___x_992_ = v___x_977_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_expr_981_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_exprType_983_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_exprInit_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_exprResult_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_proof_990_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*5, v___y_967_);
v___x_993_ = lean_apply_2(v_toPure_987_, lean_box(0), v___x_992_);
return v___x_993_;
}
}
else
{
lean_object* v_toPure_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_proof_999_; lean_object* v___x_1001_; 
lean_dec(v___x_966_);
v_toPure_995_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc(v_toPure_995_);
lean_dec_ref(v_toApplicative_965_);
lean_inc_ref(v_type_961_);
v___x_996_ = l_Lean_mkLambda(v_declName_960_, v___x_979_, v_type_961_, v_proof_974_);
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_998_ = l_Lean_mkConst(v___x_997_, v_us_968_);
v_proof_999_ = l_Lean_mkApp6(v___x_998_, v_type_961_, v___x_982_, v___y_962_, v___x_984_, v___x_980_, v___x_996_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 4, v_proof_999_);
lean_ctor_set(v___x_977_, 3, v_exprResult_986_);
lean_ctor_set(v___x_977_, 2, v_exprInit_985_);
lean_ctor_set(v___x_977_, 1, v_exprType_983_);
lean_ctor_set(v___x_977_, 0, v_expr_981_);
v___x_1001_ = v___x_977_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_expr_981_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_exprType_983_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_exprInit_985_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_exprResult_986_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_proof_999_);
v___x_1001_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; 
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*5, v_nondep_964_);
v___x_1002_ = lean_apply_2(v_toPure_995_, lean_box(0), v___x_1001_);
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_1005_, lean_object* v_type_1006_, lean_object* v___y_1007_, lean_object* v_value_1008_, lean_object* v_nondep_1009_, lean_object* v_toApplicative_1010_, lean_object* v___x_1011_, lean_object* v___y_1012_, lean_object* v_us_1013_, lean_object* v_rb_1014_){
_start:
{
uint8_t v_nondep_10459__boxed_1015_; uint8_t v___y_10461__boxed_1016_; lean_object* v_res_1017_; 
v_nondep_10459__boxed_1015_ = lean_unbox(v_nondep_1009_);
v___y_10461__boxed_1016_ = lean_unbox(v___y_1012_);
v_res_1017_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_1005_, v_type_1006_, v___y_1007_, v_value_1008_, v_nondep_10459__boxed_1015_, v_toApplicative_1010_, v___x_1011_, v___y_10461__boxed_1016_, v_us_1013_, v_rb_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1018_, lean_object* v_____x_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_apply_1(v___f_1018_, v_____x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1025_, lean_object* v_declName_1026_, lean_object* v_type_1027_, lean_object* v_value_1028_, lean_object* v_us_1029_, lean_object* v___x_1030_, lean_object* v_toApplicative_1031_, uint8_t v_nondep_1032_, lean_object* v_rb_1033_){
_start:
{
lean_object* v_expr_1034_; lean_object* v_exprType_1035_; lean_object* v_exprInit_1036_; lean_object* v_exprResult_1037_; lean_object* v_proof_1038_; uint8_t v_modified_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1069_; 
v_expr_1034_ = lean_ctor_get(v_rb_1033_, 0);
v_exprType_1035_ = lean_ctor_get(v_rb_1033_, 1);
v_exprInit_1036_ = lean_ctor_get(v_rb_1033_, 2);
v_exprResult_1037_ = lean_ctor_get(v_rb_1033_, 3);
v_proof_1038_ = lean_ctor_get(v_rb_1033_, 4);
v_modified_1039_ = lean_ctor_get_uint8(v_rb_1033_, sizeof(void*)*5);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_rb_1033_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1041_ = v_rb_1033_;
v_isShared_1042_ = v_isSharedCheck_1069_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_proof_1038_);
lean_inc(v_exprResult_1037_);
lean_inc(v_exprInit_1036_);
lean_inc(v_exprType_1035_);
lean_inc(v_expr_1034_);
lean_dec(v_rb_1033_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1069_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_expr_1043_; lean_object* v_exprType_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v_exprInit_1047_; lean_object* v_exprResult_1048_; 
v_expr_1043_ = lean_expr_lower_loose_bvars(v_expr_1034_, v___x_1025_, v___x_1025_);
lean_dec_ref(v_expr_1034_);
v_exprType_1044_ = lean_expr_lower_loose_bvars(v_exprType_1035_, v___x_1025_, v___x_1025_);
lean_dec_ref(v_exprType_1035_);
v___x_1045_ = 0;
lean_inc_ref(v_type_1027_);
lean_inc(v_declName_1026_);
v___x_1046_ = l_Lean_mkLambda(v_declName_1026_, v___x_1045_, v_type_1027_, v_exprInit_1036_);
lean_inc_ref(v_value_1028_);
lean_inc_ref(v___x_1046_);
v_exprInit_1047_ = l_Lean_Expr_app___override(v___x_1046_, v_value_1028_);
v_exprResult_1048_ = lean_expr_lower_loose_bvars(v_exprResult_1037_, v___x_1025_, v___x_1025_);
lean_dec_ref(v_exprResult_1037_);
if (v_modified_1039_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_proof_1054_; lean_object* v_toPure_1055_; lean_object* v___x_1057_; 
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_proof_1038_);
lean_dec(v_declName_1026_);
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1050_ = l_Lean_mkConst(v___x_1049_, v_us_1029_);
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1052_ = l_Lean_mkConst(v___x_1051_, v___x_1030_);
lean_inc_ref(v_expr_1043_);
lean_inc_ref(v_exprType_1044_);
v___x_1053_ = l_Lean_mkAppB(v___x_1052_, v_exprType_1044_, v_expr_1043_);
lean_inc_ref_n(v_expr_1043_, 2);
lean_inc_ref(v_exprType_1044_);
v_proof_1054_ = l_Lean_mkApp6(v___x_1050_, v_type_1027_, v_exprType_1044_, v_value_1028_, v_expr_1043_, v_expr_1043_, v___x_1053_);
v_toPure_1055_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_inc(v_toPure_1055_);
lean_dec_ref(v_toApplicative_1031_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v_proof_1054_);
lean_ctor_set(v___x_1041_, 3, v_exprResult_1048_);
lean_ctor_set(v___x_1041_, 2, v_exprInit_1047_);
lean_ctor_set(v___x_1041_, 1, v_exprType_1044_);
lean_ctor_set(v___x_1041_, 0, v_expr_1043_);
v___x_1057_ = v___x_1041_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_expr_1043_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_exprType_1044_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_exprInit_1047_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v_exprResult_1048_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v_proof_1054_);
v___x_1057_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; 
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*5, v_nondep_1032_);
v___x_1058_ = lean_apply_2(v_toPure_1055_, lean_box(0), v___x_1057_);
return v___x_1058_;
}
}
else
{
lean_object* v_toPure_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_proof_1064_; lean_object* v___x_1066_; 
lean_dec(v___x_1030_);
v_toPure_1060_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_inc(v_toPure_1060_);
lean_dec_ref(v_toApplicative_1031_);
lean_inc_ref(v_type_1027_);
v___x_1061_ = l_Lean_mkLambda(v_declName_1026_, v___x_1045_, v_type_1027_, v_proof_1038_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1063_ = l_Lean_mkConst(v___x_1062_, v_us_1029_);
lean_inc_ref(v_expr_1043_);
lean_inc_ref(v_exprType_1044_);
v_proof_1064_ = l_Lean_mkApp6(v___x_1063_, v_type_1027_, v_exprType_1044_, v_value_1028_, v___x_1046_, v_expr_1043_, v___x_1061_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v_proof_1064_);
lean_ctor_set(v___x_1041_, 3, v_exprResult_1048_);
lean_ctor_set(v___x_1041_, 2, v_exprInit_1047_);
lean_ctor_set(v___x_1041_, 1, v_exprType_1044_);
lean_ctor_set(v___x_1041_, 0, v_expr_1043_);
v___x_1066_ = v___x_1041_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_expr_1043_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_exprType_1044_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_exprInit_1047_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_exprResult_1048_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_proof_1064_);
v___x_1066_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*5, v_nondep_1032_);
v___x_1067_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1066_);
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1070_, lean_object* v_declName_1071_, lean_object* v_type_1072_, lean_object* v_value_1073_, lean_object* v_us_1074_, lean_object* v___x_1075_, lean_object* v_toApplicative_1076_, lean_object* v_nondep_1077_, lean_object* v_rb_1078_){
_start:
{
uint8_t v_nondep_10546__boxed_1079_; lean_object* v_res_1080_; 
v_nondep_10546__boxed_1079_ = lean_unbox(v_nondep_1077_);
v_res_1080_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1070_, v_declName_1071_, v_type_1072_, v_value_1073_, v_us_1074_, v___x_1075_, v_toApplicative_1076_, v_nondep_10546__boxed_1079_, v_rb_1078_);
lean_dec(v___x_1070_);
return v_res_1080_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_cls_1090_, lean_object* v___x_1091_, lean_object* v___f_1092_, lean_object* v_declName_1093_, lean_object* v_val_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_10113__overap_1100_; lean_object* v___x_1101_; 
lean_inc(v_cls_1090_);
lean_inc_ref(v___x_1088_);
lean_inc_ref(v___x_1087_);
v___x_10113__overap_1100_ = l_Lean_isTracingEnabledFor___redArg(v___x_1087_, v___x_1088_, v___x_1089_, v_cls_1090_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
v___x_1101_ = lean_apply_5(v___x_10113__overap_1100_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1127_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1127_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1127_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_unbox(v_a_1102_);
lean_dec(v_a_1102_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_val_1094_);
lean_dec(v_declName_1093_);
lean_dec(v___f_1092_);
lean_dec(v___x_1091_);
lean_dec(v_cls_1090_);
lean_dec_ref(v___x_1088_);
lean_dec_ref(v___x_1087_);
v___x_1107_ = lean_box(0);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
else
{
lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_toMonadRef_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_10133__overap_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1104_);
v___f_1111_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
v___x_1113_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1114_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1112_, v___x_1091_, v___x_1113_);
v___x_1115_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1111_, v___f_1092_, v___x_1114_);
v_toMonadRef_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_toMonadRef_1116_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1118_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1119_ = l_Lean_MessageData_ofName(v_declName_1093_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_MessageData_ofExpr(v_val_1094_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_10133__overap_1125_ = l_Lean_addTrace___redArg(v___x_1087_, v___x_1088_, v_toMonadRef_1116_, v___x_1117_, v_cls_1090_, v___x_1124_);
v___x_1126_ = lean_apply_5(v___x_10133__overap_1125_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, lean_box(0));
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_val_1094_);
lean_dec(v_declName_1093_);
lean_dec(v___f_1092_);
lean_dec(v___x_1091_);
lean_dec(v_cls_1090_);
lean_dec_ref(v___x_1088_);
lean_dec_ref(v___x_1087_);
v_a_1128_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1101_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1101_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v_cls_1139_, lean_object* v___x_1140_, lean_object* v___f_1141_, lean_object* v_declName_1142_, lean_object* v_val_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v___x_1136_, v___x_1137_, v___x_1138_, v_cls_1139_, v___x_1140_, v___f_1141_, v_declName_1142_, v_val_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v_res_1149_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v_cls_1159_, lean_object* v___x_1160_, lean_object* v___f_1161_, lean_object* v_declName_1162_, lean_object* v_val_1163_, lean_object* v_val_x27_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_9782__overap_1170_; lean_object* v___x_1171_; 
lean_inc(v_cls_1159_);
lean_inc_ref(v___x_1157_);
lean_inc_ref(v___x_1156_);
v___x_9782__overap_1170_ = l_Lean_isTracingEnabledFor___redArg(v___x_1156_, v___x_1157_, v___x_1158_, v_cls_1159_);
lean_inc(v___y_1168_);
lean_inc_ref(v___y_1167_);
lean_inc(v___y_1166_);
lean_inc_ref(v___y_1165_);
v___x_1171_ = lean_apply_5(v___x_9782__overap_1170_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, lean_box(0));
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1201_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1201_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1201_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_unbox(v_a_1172_);
lean_dec(v_a_1172_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v_val_x27_1164_);
lean_dec_ref(v_val_1163_);
lean_dec(v_declName_1162_);
lean_dec(v___f_1161_);
lean_dec(v___x_1160_);
lean_dec(v_cls_1159_);
lean_dec_ref(v___x_1157_);
lean_dec_ref(v___x_1156_);
v___x_1177_ = lean_box(0);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
else
{
lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_toMonadRef_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_9807__overap_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1174_);
v___f_1181_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_1182_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
v___x_1183_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1184_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1182_, v___x_1160_, v___x_1183_);
v___x_1185_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1181_, v___f_1161_, v___x_1184_);
v_toMonadRef_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_toMonadRef_1186_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1188_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1189_ = l_Lean_MessageData_ofName(v_declName_1162_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_MessageData_ofExpr(v_val_1163_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_MessageData_ofExpr(v_val_x27_1164_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_9807__overap_1199_ = l_Lean_addTrace___redArg(v___x_1156_, v___x_1157_, v_toMonadRef_1186_, v___x_1187_, v_cls_1159_, v___x_1198_);
v___x_1200_ = lean_apply_5(v___x_9807__overap_1199_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, lean_box(0));
return v___x_1200_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v_val_x27_1164_);
lean_dec_ref(v_val_1163_);
lean_dec(v_declName_1162_);
lean_dec(v___f_1161_);
lean_dec(v___x_1160_);
lean_dec(v_cls_1159_);
lean_dec_ref(v___x_1157_);
lean_dec_ref(v___x_1156_);
v_a_1202_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1171_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1171_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v___x_1210_, lean_object* v___x_1211_, lean_object* v___x_1212_, lean_object* v_cls_1213_, lean_object* v___x_1214_, lean_object* v___f_1215_, lean_object* v_declName_1216_, lean_object* v_val_1217_, lean_object* v_val_x27_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v___x_1210_, v___x_1211_, v___x_1212_, v_cls_1213_, v___x_1214_, v___f_1215_, v_declName_1216_, v_val_1217_, v_val_x27_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_toApplicative_1225_, lean_object* v_e_1226_, lean_object* v_xs_1227_, lean_object* v_h_1228_, uint8_t v_nondep_1229_, lean_object* v_toBind_1230_, lean_object* v___f_1231_, lean_object* v_____r_1232_){
_start:
{
lean_object* v_toPure_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_toPure_1233_ = lean_ctor_get(v_toApplicative_1225_, 1);
lean_inc(v_toPure_1233_);
lean_dec_ref(v_toApplicative_1225_);
v___x_1234_ = lean_expr_abstract(v_e_1226_, v_xs_1227_);
v___x_1235_ = lean_expr_abstract(v_h_1228_, v_xs_1227_);
v___x_1236_ = lean_box(v_nondep_1229_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___x_1235_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1234_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_apply_2(v_toPure_1233_, lean_box(0), v___x_1238_);
v___x_1240_ = lean_apply_4(v_toBind_1230_, lean_box(0), lean_box(0), v___x_1239_, v___f_1231_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_toApplicative_1241_, lean_object* v_e_1242_, lean_object* v_xs_1243_, lean_object* v_h_1244_, lean_object* v_nondep_1245_, lean_object* v_toBind_1246_, lean_object* v___f_1247_, lean_object* v_____r_1248_){
_start:
{
uint8_t v_nondep_10864__boxed_1249_; lean_object* v_res_1250_; 
v_nondep_10864__boxed_1249_ = lean_unbox(v_nondep_1245_);
v_res_1250_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1241_, v_e_1242_, v_xs_1243_, v_h_1244_, v_nondep_10864__boxed_1249_, v_toBind_1246_, v___f_1247_, v_____r_1248_);
lean_dec_ref(v_h_1244_);
lean_dec_ref(v_xs_1243_);
lean_dec_ref(v_e_1242_);
return v_res_1250_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v___x_1256_, lean_object* v_cls_1257_, lean_object* v___x_1258_, lean_object* v___f_1259_, lean_object* v_declName_1260_, lean_object* v_val_1261_, lean_object* v_e_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_9966__overap_1268_; lean_object* v___x_1269_; 
lean_inc(v_cls_1257_);
lean_inc_ref(v___x_1255_);
lean_inc_ref(v___x_1254_);
v___x_9966__overap_1268_ = l_Lean_isTracingEnabledFor___redArg(v___x_1254_, v___x_1255_, v___x_1256_, v_cls_1257_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
v___x_1269_ = lean_apply_5(v___x_9966__overap_1268_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, lean_box(0));
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1299_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1299_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1299_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_e_1262_);
lean_dec_ref(v_val_1261_);
lean_dec(v_declName_1260_);
lean_dec(v___f_1259_);
lean_dec(v___x_1258_);
lean_dec(v_cls_1257_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v___x_1254_);
v___x_1275_ = lean_box(0);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1275_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_toMonadRef_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_9991__overap_1297_; lean_object* v___x_1298_; 
lean_del_object(v___x_1272_);
v___f_1279_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0));
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
v___x_1281_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1282_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1280_, v___x_1258_, v___x_1281_);
v___x_1283_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1279_, v___f_1259_, v___x_1282_);
v_toMonadRef_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_toMonadRef_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1286_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1287_ = l_Lean_MessageData_ofName(v_declName_1260_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_MessageData_ofExpr(v_val_1261_);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_MessageData_ofExpr(v_e_1262_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_9991__overap_1297_ = l_Lean_addTrace___redArg(v___x_1254_, v___x_1255_, v_toMonadRef_1284_, v___x_1285_, v_cls_1257_, v___x_1296_);
v___x_1298_ = lean_apply_5(v___x_9991__overap_1297_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, lean_box(0));
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_e_1262_);
lean_dec_ref(v_val_1261_);
lean_dec(v_declName_1260_);
lean_dec(v___f_1259_);
lean_dec(v___x_1258_);
lean_dec(v_cls_1257_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v___x_1254_);
v_a_1300_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1269_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1269_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v_cls_1311_, lean_object* v___x_1312_, lean_object* v___f_1313_, lean_object* v_declName_1314_, lean_object* v_val_1315_, lean_object* v_e_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v___x_1308_, v___x_1309_, v___x_1310_, v_cls_1311_, v___x_1312_, v___f_1313_, v_declName_1314_, v_val_1315_, v_e_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v_res_1322_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_instMonadEIO(lean_box(0));
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
v___x_1325_ = l_StateRefT_x27_instMonad___redArg(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1342_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1343_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1342_, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
v___f_1345_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1346_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1345_, v___x_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_toApplicative_1352_, lean_object* v_level_1353_, lean_object* v___x_1354_, lean_object* v_type_1355_, lean_object* v_value_1356_, uint8_t v___x_1357_, lean_object* v_toBind_1358_, lean_object* v___f_1359_, lean_object* v_xs_1360_, uint8_t v_nondep_1361_, lean_object* v___f_1362_, lean_object* v_declName_1363_, lean_object* v_val_1364_, lean_object* v_inst_1365_, lean_object* v_____do__lift_1366_){
_start:
{
if (lean_obj_tag(v_____do__lift_1366_) == 0)
{
lean_object* v_toPure_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_inst_1365_);
lean_dec_ref(v_val_1364_);
lean_dec(v_declName_1363_);
lean_dec(v___f_1362_);
lean_dec_ref(v_xs_1360_);
v_toPure_1367_ = lean_ctor_get(v_toApplicative_1352_, 1);
lean_inc(v_toPure_1367_);
lean_dec_ref(v_toApplicative_1352_);
v___x_1368_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_level_1353_);
lean_ctor_set(v___x_1369_, 1, v___x_1354_);
v___x_1370_ = l_Lean_mkConst(v___x_1368_, v___x_1369_);
lean_inc_ref(v_value_1356_);
v___x_1371_ = l_Lean_mkAppB(v___x_1370_, v_type_1355_, v_value_1356_);
v___x_1372_ = lean_box(v___x_1357_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1371_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_value_1356_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1374_);
v___x_1376_ = lean_apply_4(v_toBind_1358_, lean_box(0), lean_box(0), v___x_1375_, v___f_1359_);
return v___x_1376_;
}
else
{
lean_object* v_e_1377_; lean_object* v_h_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v___f_1359_);
lean_dec_ref(v_value_1356_);
lean_dec_ref(v_type_1355_);
lean_dec(v___x_1354_);
lean_dec(v_level_1353_);
v_e_1377_ = lean_ctor_get(v_____do__lift_1366_, 0);
v_h_1378_ = lean_ctor_get(v_____do__lift_1366_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_____do__lift_1366_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1380_ = v_____do__lift_1366_;
v_isShared_1381_ = v_isSharedCheck_1454_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_h_1378_);
lean_inc(v_e_1377_);
lean_dec(v_____do__lift_1366_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1454_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v_toApplicative_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1452_; 
v___x_1382_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v___x_1382_, 1);
lean_dec(v_unused_1453_);
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1452_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_toApplicative_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1452_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_toFunctor_1387_; lean_object* v_toSeq_1388_; lean_object* v_toSeqLeft_1389_; lean_object* v_toSeqRight_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1450_; 
v_toFunctor_1387_ = lean_ctor_get(v_toApplicative_1383_, 0);
v_toSeq_1388_ = lean_ctor_get(v_toApplicative_1383_, 2);
v_toSeqLeft_1389_ = lean_ctor_get(v_toApplicative_1383_, 3);
v_toSeqRight_1390_ = lean_ctor_get(v_toApplicative_1383_, 4);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_toApplicative_1383_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_toApplicative_1383_, 1);
lean_dec(v_unused_1451_);
v___x_1392_ = v_toApplicative_1383_;
v_isShared_1393_ = v_isSharedCheck_1450_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_toSeqRight_1390_);
lean_inc(v_toSeqLeft_1389_);
lean_inc(v_toSeq_1388_);
lean_inc(v_toFunctor_1387_);
lean_dec(v_toApplicative_1383_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1450_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___f_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; lean_object* v___f_1397_; lean_object* v___x_1399_; 
v___f_1394_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1395_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_1387_);
v___f_1396_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1396_, 0, v_toFunctor_1387_);
v___f_1397_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1397_, 0, v_toFunctor_1387_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 0);
lean_ctor_set(v___x_1380_, 1, v___f_1397_);
lean_ctor_set(v___x_1380_, 0, v___f_1396_);
v___x_1399_ = v___x_1380_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___f_1396_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___f_1397_);
v___x_1399_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___f_1400_; lean_object* v___f_1401_; lean_object* v___f_1402_; lean_object* v___x_1404_; 
v___f_1400_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1400_, 0, v_toSeqRight_1390_);
v___f_1401_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1401_, 0, v_toSeqLeft_1389_);
v___f_1402_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1402_, 0, v_toSeq_1388_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___f_1400_);
lean_ctor_set(v___x_1392_, 3, v___f_1401_);
lean_ctor_set(v___x_1392_, 2, v___f_1402_);
lean_ctor_set(v___x_1392_, 1, v___f_1394_);
lean_ctor_set(v___x_1392_, 0, v___x_1399_);
v___x_1404_ = v___x_1392_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___f_1394_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v___f_1402_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v___f_1401_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___f_1400_);
v___x_1404_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___f_1395_);
lean_ctor_set(v___x_1385_, 0, v___x_1404_);
v___x_1406_ = v___x_1385_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___f_1395_);
v___x_1406_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v_toApplicative_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1445_; 
v___x_1407_ = l_StateRefT_x27_instMonad___redArg(v___x_1406_);
v_toApplicative_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1407_, 1);
lean_dec(v_unused_1446_);
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1445_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_toApplicative_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1445_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_toFunctor_1412_; lean_object* v_toSeq_1413_; lean_object* v_toSeqLeft_1414_; lean_object* v_toSeqRight_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1443_; 
v_toFunctor_1412_ = lean_ctor_get(v_toApplicative_1408_, 0);
v_toSeq_1413_ = lean_ctor_get(v_toApplicative_1408_, 2);
v_toSeqLeft_1414_ = lean_ctor_get(v_toApplicative_1408_, 3);
v_toSeqRight_1415_ = lean_ctor_get(v_toApplicative_1408_, 4);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_toApplicative_1408_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_toApplicative_1408_, 1);
lean_dec(v_unused_1444_);
v___x_1417_ = v_toApplicative_1408_;
v_isShared_1418_ = v_isSharedCheck_1443_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_toSeqRight_1415_);
lean_inc(v_toSeqLeft_1414_);
lean_inc(v_toSeq_1413_);
lean_inc(v_toFunctor_1412_);
lean_dec(v_toApplicative_1408_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1443_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v_cls_1421_; lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___f_1428_; lean_object* v___f_1429_; lean_object* v___x_1431_; 
v___x_1419_ = lean_box(v_nondep_1361_);
lean_inc(v_toBind_1358_);
lean_inc_ref(v_e_1377_);
v___f_1420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1420_, 0, v_toApplicative_1352_);
lean_closure_set(v___f_1420_, 1, v_e_1377_);
lean_closure_set(v___f_1420_, 2, v_xs_1360_);
lean_closure_set(v___f_1420_, 3, v_h_1378_);
lean_closure_set(v___f_1420_, 4, v___x_1419_);
lean_closure_set(v___f_1420_, 5, v_toBind_1358_);
lean_closure_set(v___f_1420_, 6, v___f_1362_);
v_cls_1421_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1422_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1423_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1412_);
v___f_1424_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1424_, 0, v_toFunctor_1412_);
v___f_1425_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1425_, 0, v_toFunctor_1412_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___f_1424_);
lean_ctor_set(v___x_1426_, 1, v___f_1425_);
v___f_1427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1427_, 0, v_toSeqRight_1415_);
v___f_1428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1428_, 0, v_toSeqLeft_1414_);
v___f_1429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1429_, 0, v_toSeq_1413_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 4, v___f_1427_);
lean_ctor_set(v___x_1417_, 3, v___f_1428_);
lean_ctor_set(v___x_1417_, 2, v___f_1429_);
lean_ctor_set(v___x_1417_, 1, v___f_1422_);
lean_ctor_set(v___x_1417_, 0, v___x_1426_);
v___x_1431_ = v___x_1417_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___f_1422_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___f_1429_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v___f_1428_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___f_1427_);
v___x_1431_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___f_1423_);
lean_ctor_set(v___x_1410_, 0, v___x_1431_);
v___x_1433_ = v___x_1410_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___f_1423_);
v___x_1433_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___f_1434_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1435_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1436_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_1437_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_1438_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 14, 9);
lean_closure_set(v___f_1438_, 0, v___x_1433_);
lean_closure_set(v___f_1438_, 1, v___x_1436_);
lean_closure_set(v___f_1438_, 2, v___x_1437_);
lean_closure_set(v___f_1438_, 3, v_cls_1421_);
lean_closure_set(v___f_1438_, 4, v___x_1435_);
lean_closure_set(v___f_1438_, 5, v___f_1434_);
lean_closure_set(v___f_1438_, 6, v_declName_1363_);
lean_closure_set(v___f_1438_, 7, v_val_1364_);
lean_closure_set(v___f_1438_, 8, v_e_1377_);
v___x_1439_ = lean_apply_2(v_inst_1365_, lean_box(0), v___f_1438_);
v___x_1440_ = lean_apply_4(v_toBind_1358_, lean_box(0), lean_box(0), v___x_1439_, v___f_1420_);
return v___x_1440_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object* v_toApplicative_1455_, lean_object* v_level_1456_, lean_object* v___x_1457_, lean_object* v_type_1458_, lean_object* v_value_1459_, lean_object* v___x_1460_, lean_object* v_toBind_1461_, lean_object* v___f_1462_, lean_object* v_xs_1463_, lean_object* v_nondep_1464_, lean_object* v___f_1465_, lean_object* v_declName_1466_, lean_object* v_val_1467_, lean_object* v_inst_1468_, lean_object* v_____do__lift_1469_){
_start:
{
uint8_t v___x_11087__boxed_1470_; uint8_t v_nondep_11089__boxed_1471_; lean_object* v_res_1472_; 
v___x_11087__boxed_1470_ = lean_unbox(v___x_1460_);
v_nondep_11089__boxed_1471_ = lean_unbox(v_nondep_1464_);
v_res_1472_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1455_, v_level_1456_, v___x_1457_, v_type_1458_, v_value_1459_, v___x_11087__boxed_1470_, v_toBind_1461_, v___f_1462_, v_xs_1463_, v_nondep_11089__boxed_1471_, v___f_1465_, v_declName_1466_, v_val_1467_, v_inst_1468_, v_____do__lift_1469_);
return v_res_1472_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1482_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1483_ = lean_unsigned_to_nat(8u);
v___x_1484_ = lean_unsigned_to_nat(287u);
v___x_1485_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1486_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1487_ = l_mkPanicMessageWithDecl(v___x_1486_, v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1488_, lean_object* v_type_1489_, lean_object* v_fst_1490_, lean_object* v___x_1491_, lean_object* v_value_1492_, uint8_t v_nondep_1493_, uint8_t v_fst_1494_, lean_object* v_toApplicative_1495_, lean_object* v___x_1496_, lean_object* v_us_1497_, lean_object* v_snd_1498_, lean_object* v_inst_1499_, lean_object* v_rb_1500_){
_start:
{
lean_object* v_expr_1501_; lean_object* v_exprType_1502_; lean_object* v_exprInit_1503_; lean_object* v_exprResult_1504_; lean_object* v_proof_1505_; uint8_t v_modified_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1557_; 
v_expr_1501_ = lean_ctor_get(v_rb_1500_, 0);
v_exprType_1502_ = lean_ctor_get(v_rb_1500_, 1);
v_exprInit_1503_ = lean_ctor_get(v_rb_1500_, 2);
v_exprResult_1504_ = lean_ctor_get(v_rb_1500_, 3);
v_proof_1505_ = lean_ctor_get(v_rb_1500_, 4);
v_modified_1506_ = lean_ctor_get_uint8(v_rb_1500_, sizeof(void*)*5);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_rb_1500_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1508_ = v_rb_1500_;
v_isShared_1509_ = v_isSharedCheck_1557_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_proof_1505_);
lean_inc(v_exprResult_1504_);
lean_inc(v_exprInit_1503_);
lean_inc(v_exprType_1502_);
lean_inc(v_expr_1501_);
lean_dec(v_rb_1500_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1557_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_expr_has_loose_bvar(v_exprType_1502_, v___x_1510_);
if (v___x_1511_ == 0)
{
uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v_expr_1514_; lean_object* v_exprType_1515_; lean_object* v___x_1516_; lean_object* v_exprInit_1517_; lean_object* v_exprResult_1518_; 
lean_dec_ref(v_inst_1499_);
v___x_1512_ = 0;
lean_inc_ref(v_type_1489_);
lean_inc(v_declName_1488_);
v___x_1513_ = l_Lean_mkLambda(v_declName_1488_, v___x_1512_, v_type_1489_, v_expr_1501_);
lean_inc_ref(v_fst_1490_);
lean_inc_ref(v___x_1513_);
v_expr_1514_ = l_Lean_Expr_app___override(v___x_1513_, v_fst_1490_);
v_exprType_1515_ = lean_expr_lower_loose_bvars(v_exprType_1502_, v___x_1491_, v___x_1491_);
lean_dec_ref(v_exprType_1502_);
lean_inc_ref(v_type_1489_);
lean_inc(v_declName_1488_);
v___x_1516_ = l_Lean_mkLambda(v_declName_1488_, v___x_1512_, v_type_1489_, v_exprInit_1503_);
lean_inc_ref(v_value_1492_);
lean_inc_ref(v___x_1516_);
v_exprInit_1517_ = l_Lean_Expr_app___override(v___x_1516_, v_value_1492_);
lean_inc_ref(v_fst_1490_);
lean_inc_ref(v_type_1489_);
lean_inc(v_declName_1488_);
v_exprResult_1518_ = l_Lean_Expr_letE___override(v_declName_1488_, v_type_1489_, v_fst_1490_, v_exprResult_1504_, v_nondep_1493_);
if (v_fst_1494_ == 0)
{
lean_dec_ref(v_snd_1498_);
lean_dec_ref(v_fst_1490_);
if (v_modified_1506_ == 0)
{
lean_object* v_toPure_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_proof_1522_; lean_object* v___x_1524_; 
lean_dec_ref(v___x_1516_);
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_proof_1505_);
lean_dec(v_us_1497_);
lean_dec_ref(v_value_1492_);
lean_dec_ref(v_type_1489_);
lean_dec(v_declName_1488_);
v_toPure_1519_ = lean_ctor_get(v_toApplicative_1495_, 1);
lean_inc(v_toPure_1519_);
lean_dec_ref(v_toApplicative_1495_);
v___x_1520_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1521_ = l_Lean_mkConst(v___x_1520_, v___x_1496_);
lean_inc_ref(v_expr_1514_);
lean_inc_ref(v_exprType_1515_);
v_proof_1522_ = l_Lean_mkAppB(v___x_1521_, v_exprType_1515_, v_expr_1514_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_proof_1522_);
lean_ctor_set(v___x_1508_, 3, v_exprResult_1518_);
lean_ctor_set(v___x_1508_, 2, v_exprInit_1517_);
lean_ctor_set(v___x_1508_, 1, v_exprType_1515_);
lean_ctor_set(v___x_1508_, 0, v_expr_1514_);
v___x_1524_ = v___x_1508_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_expr_1514_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_exprType_1515_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_exprInit_1517_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_exprResult_1518_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_proof_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*5, v_modified_1506_);
v___x_1524_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_apply_2(v_toPure_1519_, lean_box(0), v___x_1524_);
return v___x_1525_;
}
}
else
{
lean_object* v_toPure_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_proof_1531_; lean_object* v___x_1533_; 
lean_dec(v___x_1496_);
v_toPure_1527_ = lean_ctor_get(v_toApplicative_1495_, 1);
lean_inc(v_toPure_1527_);
lean_dec_ref(v_toApplicative_1495_);
lean_inc_ref(v_type_1489_);
v___x_1528_ = l_Lean_mkLambda(v_declName_1488_, v___x_1512_, v_type_1489_, v_proof_1505_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1530_ = l_Lean_mkConst(v___x_1529_, v_us_1497_);
lean_inc_ref(v_exprType_1515_);
v_proof_1531_ = l_Lean_mkApp6(v___x_1530_, v_type_1489_, v_exprType_1515_, v_value_1492_, v___x_1516_, v___x_1513_, v___x_1528_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_proof_1531_);
lean_ctor_set(v___x_1508_, 3, v_exprResult_1518_);
lean_ctor_set(v___x_1508_, 2, v_exprInit_1517_);
lean_ctor_set(v___x_1508_, 1, v_exprType_1515_);
lean_ctor_set(v___x_1508_, 0, v_expr_1514_);
v___x_1533_ = v___x_1508_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_expr_1514_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_exprType_1515_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_exprInit_1517_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_exprResult_1518_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_proof_1531_);
v___x_1533_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; 
lean_ctor_set_uint8(v___x_1533_, sizeof(void*)*5, v_nondep_1493_);
v___x_1534_ = lean_apply_2(v_toPure_1527_, lean_box(0), v___x_1533_);
return v___x_1534_;
}
}
}
else
{
lean_dec(v___x_1496_);
if (v_modified_1506_ == 0)
{
lean_object* v_toPure_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_proof_1539_; lean_object* v___x_1541_; 
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_proof_1505_);
lean_dec(v_declName_1488_);
v_toPure_1536_ = lean_ctor_get(v_toApplicative_1495_, 1);
lean_inc(v_toPure_1536_);
lean_dec_ref(v_toApplicative_1495_);
v___x_1537_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1538_ = l_Lean_mkConst(v___x_1537_, v_us_1497_);
lean_inc_ref(v_exprType_1515_);
v_proof_1539_ = l_Lean_mkApp6(v___x_1538_, v_type_1489_, v_exprType_1515_, v_value_1492_, v_fst_1490_, v___x_1516_, v_snd_1498_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_proof_1539_);
lean_ctor_set(v___x_1508_, 3, v_exprResult_1518_);
lean_ctor_set(v___x_1508_, 2, v_exprInit_1517_);
lean_ctor_set(v___x_1508_, 1, v_exprType_1515_);
lean_ctor_set(v___x_1508_, 0, v_expr_1514_);
v___x_1541_ = v___x_1508_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_expr_1514_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_exprType_1515_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_exprInit_1517_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_exprResult_1518_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_proof_1539_);
v___x_1541_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; 
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*5, v_nondep_1493_);
v___x_1542_ = lean_apply_2(v_toPure_1536_, lean_box(0), v___x_1541_);
return v___x_1542_;
}
}
else
{
lean_object* v_toPure_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_proof_1548_; lean_object* v___x_1550_; 
v_toPure_1544_ = lean_ctor_get(v_toApplicative_1495_, 1);
lean_inc(v_toPure_1544_);
lean_dec_ref(v_toApplicative_1495_);
lean_inc_ref(v_type_1489_);
v___x_1545_ = l_Lean_mkLambda(v_declName_1488_, v___x_1512_, v_type_1489_, v_proof_1505_);
v___x_1546_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1547_ = l_Lean_mkConst(v___x_1546_, v_us_1497_);
lean_inc_ref(v_exprType_1515_);
v_proof_1548_ = l_Lean_mkApp8(v___x_1547_, v_type_1489_, v_exprType_1515_, v_value_1492_, v_fst_1490_, v___x_1516_, v___x_1513_, v_snd_1498_, v___x_1545_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 4, v_proof_1548_);
lean_ctor_set(v___x_1508_, 3, v_exprResult_1518_);
lean_ctor_set(v___x_1508_, 2, v_exprInit_1517_);
lean_ctor_set(v___x_1508_, 1, v_exprType_1515_);
lean_ctor_set(v___x_1508_, 0, v_expr_1514_);
v___x_1550_ = v___x_1508_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_expr_1514_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_exprType_1515_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_exprInit_1517_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_exprResult_1518_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_proof_1548_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*5, v_nondep_1493_);
v___x_1551_ = lean_apply_2(v_toPure_1544_, lean_box(0), v___x_1550_);
return v___x_1551_;
}
}
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_del_object(v___x_1508_);
lean_dec_ref(v_proof_1505_);
lean_dec_ref(v_exprResult_1504_);
lean_dec_ref(v_exprInit_1503_);
lean_dec_ref(v_exprType_1502_);
lean_dec_ref(v_expr_1501_);
lean_dec_ref(v_snd_1498_);
lean_dec(v_us_1497_);
lean_dec(v___x_1496_);
lean_dec_ref(v_toApplicative_1495_);
lean_dec_ref(v_value_1492_);
lean_dec_ref(v_fst_1490_);
lean_dec_ref(v_type_1489_);
lean_dec(v_declName_1488_);
v___x_1553_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1554_ = l_instInhabitedOfMonad___redArg(v_inst_1499_, v___x_1553_);
v___x_1555_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1556_ = l_panic___redArg(v___x_1554_, v___x_1555_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1558_, lean_object* v_type_1559_, lean_object* v_fst_1560_, lean_object* v___x_1561_, lean_object* v_value_1562_, lean_object* v_nondep_1563_, lean_object* v_fst_1564_, lean_object* v_toApplicative_1565_, lean_object* v___x_1566_, lean_object* v_us_1567_, lean_object* v_snd_1568_, lean_object* v_inst_1569_, lean_object* v_rb_1570_){
_start:
{
uint8_t v_nondep_11340__boxed_1571_; uint8_t v_fst_11341__boxed_1572_; lean_object* v_res_1573_; 
v_nondep_11340__boxed_1571_ = lean_unbox(v_nondep_1563_);
v_fst_11341__boxed_1572_ = lean_unbox(v_fst_1564_);
v_res_1573_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1558_, v_type_1559_, v_fst_1560_, v___x_1561_, v_value_1562_, v_nondep_11340__boxed_1571_, v_fst_11341__boxed_1572_, v_toApplicative_1565_, v___x_1566_, v_us_1567_, v_snd_1568_, v_inst_1569_, v_rb_1570_);
lean_dec(v___x_1561_);
return v_res_1573_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0));
v___x_1579_ = lean_unsigned_to_nat(34u);
v___x_1580_ = lean_unsigned_to_nat(217u);
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1582_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1583_ = l_mkPanicMessageWithDecl(v___x_1582_, v___x_1581_, v___x_1580_, v___x_1579_, v___x_1578_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1584_, lean_object* v_type_1585_, lean_object* v_value_1586_, uint8_t v_nondep_1587_, lean_object* v_toApplicative_1588_, lean_object* v___x_1589_, lean_object* v_us_1590_, lean_object* v_decl_1591_, lean_object* v_x_1592_, lean_object* v_i_1593_, lean_object* v_xs_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_info_1599_, lean_object* v_fixed_1600_, lean_object* v_used_1601_, lean_object* v_body_1602_, lean_object* v_toBind_1603_, lean_object* v_withNewLemmas_1604_, lean_object* v_val_x27_1605_, lean_object* v_val_1606_, uint8_t v___x_1607_, lean_object* v_____r_1608_){
_start:
{
uint8_t v___y_1610_; lean_object* v___y_1611_; uint8_t v___y_1627_; uint8_t v___x_1629_; 
v___x_1629_ = lean_expr_eqv(v_val_1606_, v_val_x27_1605_);
if (v___x_1629_ == 0)
{
v___y_1627_ = v_nondep_1587_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v___x_1607_;
goto v___jp_1626_;
}
v___jp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1612_ = lean_box(v_nondep_1587_);
v___x_1613_ = lean_box(v___y_1610_);
v___f_1614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1614_, 0, v_declName_1584_);
lean_closure_set(v___f_1614_, 1, v_type_1585_);
lean_closure_set(v___f_1614_, 2, v___y_1611_);
lean_closure_set(v___f_1614_, 3, v_value_1586_);
lean_closure_set(v___f_1614_, 4, v___x_1612_);
lean_closure_set(v___f_1614_, 5, v_toApplicative_1588_);
lean_closure_set(v___f_1614_, 6, v___x_1589_);
lean_closure_set(v___f_1614_, 7, v___x_1613_);
lean_closure_set(v___f_1614_, 8, v_us_1590_);
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_decl_1591_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_mk_empty_array_with_capacity(v___x_1617_);
lean_inc_ref(v_x_1592_);
v___x_1619_ = lean_array_push(v___x_1618_, v_x_1592_);
v___x_1620_ = lean_nat_add(v_i_1593_, v___x_1617_);
v___x_1621_ = lean_array_push(v_xs_1594_, v_x_1592_);
lean_inc_ref(v_inst_1597_);
lean_inc_ref(v_inst_1595_);
v___x_1622_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1595_, v_inst_1596_, v_inst_1597_, v_inst_1598_, v_info_1599_, v_fixed_1600_, v_used_1601_, v_body_1602_, v___x_1620_, v___x_1621_);
v___x_1623_ = lean_apply_4(v_toBind_1603_, lean_box(0), lean_box(0), v___x_1622_, v___f_1614_);
v___x_1624_ = lean_apply_3(v_withNewLemmas_1604_, lean_box(0), v___x_1619_, v___x_1623_);
v___x_1625_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1597_, v_inst_1595_, v___x_1616_, v___x_1624_);
return v___x_1625_;
}
v___jp_1626_:
{
if (v___y_1627_ == 0)
{
lean_inc_ref(v_value_1586_);
v___y_1610_ = v___y_1627_;
v___y_1611_ = v_value_1586_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_expr_abstract(v_val_x27_1605_, v_xs_1594_);
v___y_1610_ = v___y_1627_;
v___y_1611_ = v___x_1628_;
goto v___jp_1609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1630_ = _args[0];
lean_object* v_type_1631_ = _args[1];
lean_object* v_value_1632_ = _args[2];
lean_object* v_nondep_1633_ = _args[3];
lean_object* v_toApplicative_1634_ = _args[4];
lean_object* v___x_1635_ = _args[5];
lean_object* v_us_1636_ = _args[6];
lean_object* v_decl_1637_ = _args[7];
lean_object* v_x_1638_ = _args[8];
lean_object* v_i_1639_ = _args[9];
lean_object* v_xs_1640_ = _args[10];
lean_object* v_inst_1641_ = _args[11];
lean_object* v_inst_1642_ = _args[12];
lean_object* v_inst_1643_ = _args[13];
lean_object* v_inst_1644_ = _args[14];
lean_object* v_info_1645_ = _args[15];
lean_object* v_fixed_1646_ = _args[16];
lean_object* v_used_1647_ = _args[17];
lean_object* v_body_1648_ = _args[18];
lean_object* v_toBind_1649_ = _args[19];
lean_object* v_withNewLemmas_1650_ = _args[20];
lean_object* v_val_x27_1651_ = _args[21];
lean_object* v_val_1652_ = _args[22];
lean_object* v___x_1653_ = _args[23];
lean_object* v_____r_1654_ = _args[24];
_start:
{
uint8_t v_nondep_11611__boxed_1655_; uint8_t v___x_11618__boxed_1656_; lean_object* v_res_1657_; 
v_nondep_11611__boxed_1655_ = lean_unbox(v_nondep_1633_);
v___x_11618__boxed_1656_ = lean_unbox(v___x_1653_);
v_res_1657_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1630_, v_type_1631_, v_value_1632_, v_nondep_11611__boxed_1655_, v_toApplicative_1634_, v___x_1635_, v_us_1636_, v_decl_1637_, v_x_1638_, v_i_1639_, v_xs_1640_, v_inst_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_info_1645_, v_fixed_1646_, v_used_1647_, v_body_1648_, v_toBind_1649_, v_withNewLemmas_1650_, v_val_x27_1651_, v_val_1652_, v___x_11618__boxed_1656_, v_____r_1654_);
lean_dec_ref(v_val_1652_);
lean_dec_ref(v_val_x27_1651_);
lean_dec(v_i_1639_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1658_, lean_object* v_type_1659_, lean_object* v_value_1660_, uint8_t v_nondep_1661_, lean_object* v_toApplicative_1662_, lean_object* v___x_1663_, lean_object* v_us_1664_, lean_object* v_decl_1665_, lean_object* v_x_1666_, lean_object* v_i_1667_, lean_object* v_xs_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_info_1673_, lean_object* v_fixed_1674_, lean_object* v_used_1675_, lean_object* v_body_1676_, lean_object* v_toBind_1677_, lean_object* v_withNewLemmas_1678_, lean_object* v_val_1679_, uint8_t v___x_1680_, lean_object* v_val_x27_1681_){
_start:
{
lean_object* v___x_1682_; lean_object* v_toApplicative_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1751_; 
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v___x_1682_, 1);
lean_dec(v_unused_1752_);
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1751_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_toApplicative_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1751_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_toFunctor_1687_; lean_object* v_toSeq_1688_; lean_object* v_toSeqLeft_1689_; lean_object* v_toSeqRight_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1749_; 
v_toFunctor_1687_ = lean_ctor_get(v_toApplicative_1683_, 0);
v_toSeq_1688_ = lean_ctor_get(v_toApplicative_1683_, 2);
v_toSeqLeft_1689_ = lean_ctor_get(v_toApplicative_1683_, 3);
v_toSeqRight_1690_ = lean_ctor_get(v_toApplicative_1683_, 4);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_toApplicative_1683_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v_toApplicative_1683_, 1);
lean_dec(v_unused_1750_);
v___x_1692_ = v_toApplicative_1683_;
v_isShared_1693_ = v_isSharedCheck_1749_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_toSeqRight_1690_);
lean_inc(v_toSeqLeft_1689_);
lean_inc(v_toSeq_1688_);
lean_inc(v_toFunctor_1687_);
lean_dec(v_toApplicative_1683_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1749_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___x_1703_; 
v___f_1694_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1695_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_1687_);
v___f_1696_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1696_, 0, v_toFunctor_1687_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toFunctor_1687_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___f_1696_);
lean_ctor_set(v___x_1698_, 1, v___f_1697_);
v___f_1699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1699_, 0, v_toSeqRight_1690_);
v___f_1700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1700_, 0, v_toSeqLeft_1689_);
v___f_1701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1701_, 0, v_toSeq_1688_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 4, v___f_1699_);
lean_ctor_set(v___x_1692_, 3, v___f_1700_);
lean_ctor_set(v___x_1692_, 2, v___f_1701_);
lean_ctor_set(v___x_1692_, 1, v___f_1694_);
lean_ctor_set(v___x_1692_, 0, v___x_1698_);
v___x_1703_ = v___x_1692_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___f_1694_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v___f_1701_);
lean_ctor_set(v_reuseFailAlloc_1748_, 3, v___f_1700_);
lean_ctor_set(v_reuseFailAlloc_1748_, 4, v___f_1699_);
v___x_1703_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___f_1695_);
lean_ctor_set(v___x_1685_, 0, v___x_1703_);
v___x_1705_ = v___x_1685_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___f_1695_);
v___x_1705_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v_toApplicative_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1745_; 
v___x_1706_ = l_StateRefT_x27_instMonad___redArg(v___x_1705_);
v_toApplicative_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v___x_1706_, 1);
lean_dec(v_unused_1746_);
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1745_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_toApplicative_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1745_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_toFunctor_1711_; lean_object* v_toSeq_1712_; lean_object* v_toSeqLeft_1713_; lean_object* v_toSeqRight_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1743_; 
v_toFunctor_1711_ = lean_ctor_get(v_toApplicative_1707_, 0);
v_toSeq_1712_ = lean_ctor_get(v_toApplicative_1707_, 2);
v_toSeqLeft_1713_ = lean_ctor_get(v_toApplicative_1707_, 3);
v_toSeqRight_1714_ = lean_ctor_get(v_toApplicative_1707_, 4);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_toApplicative_1707_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v_toApplicative_1707_, 1);
lean_dec(v_unused_1744_);
v___x_1716_ = v_toApplicative_1707_;
v_isShared_1717_ = v_isSharedCheck_1743_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_toSeqRight_1714_);
lean_inc(v_toSeqLeft_1713_);
lean_inc(v_toSeq_1712_);
lean_inc(v_toFunctor_1711_);
lean_dec(v_toApplicative_1707_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1743_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v_cls_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___f_1728_; lean_object* v___f_1729_; lean_object* v___x_1731_; 
v___x_1718_ = lean_box(v_nondep_1661_);
v___x_1719_ = lean_box(v___x_1680_);
lean_inc_ref(v_val_1679_);
lean_inc_ref(v_val_x27_1681_);
lean_inc(v_toBind_1677_);
lean_inc(v_inst_1670_);
lean_inc(v_declName_1658_);
v___f_1720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 25, 24);
lean_closure_set(v___f_1720_, 0, v_declName_1658_);
lean_closure_set(v___f_1720_, 1, v_type_1659_);
lean_closure_set(v___f_1720_, 2, v_value_1660_);
lean_closure_set(v___f_1720_, 3, v___x_1718_);
lean_closure_set(v___f_1720_, 4, v_toApplicative_1662_);
lean_closure_set(v___f_1720_, 5, v___x_1663_);
lean_closure_set(v___f_1720_, 6, v_us_1664_);
lean_closure_set(v___f_1720_, 7, v_decl_1665_);
lean_closure_set(v___f_1720_, 8, v_x_1666_);
lean_closure_set(v___f_1720_, 9, v_i_1667_);
lean_closure_set(v___f_1720_, 10, v_xs_1668_);
lean_closure_set(v___f_1720_, 11, v_inst_1669_);
lean_closure_set(v___f_1720_, 12, v_inst_1670_);
lean_closure_set(v___f_1720_, 13, v_inst_1671_);
lean_closure_set(v___f_1720_, 14, v_inst_1672_);
lean_closure_set(v___f_1720_, 15, v_info_1673_);
lean_closure_set(v___f_1720_, 16, v_fixed_1674_);
lean_closure_set(v___f_1720_, 17, v_used_1675_);
lean_closure_set(v___f_1720_, 18, v_body_1676_);
lean_closure_set(v___f_1720_, 19, v_toBind_1677_);
lean_closure_set(v___f_1720_, 20, v_withNewLemmas_1678_);
lean_closure_set(v___f_1720_, 21, v_val_x27_1681_);
lean_closure_set(v___f_1720_, 22, v_val_1679_);
lean_closure_set(v___f_1720_, 23, v___x_1719_);
v_cls_1721_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1722_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1723_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1711_);
v___f_1724_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1724_, 0, v_toFunctor_1711_);
v___f_1725_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1725_, 0, v_toFunctor_1711_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___f_1724_);
lean_ctor_set(v___x_1726_, 1, v___f_1725_);
v___f_1727_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1727_, 0, v_toSeqRight_1714_);
v___f_1728_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1728_, 0, v_toSeqLeft_1713_);
v___f_1729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1729_, 0, v_toSeq_1712_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 4, v___f_1727_);
lean_ctor_set(v___x_1716_, 3, v___f_1728_);
lean_ctor_set(v___x_1716_, 2, v___f_1729_);
lean_ctor_set(v___x_1716_, 1, v___f_1722_);
lean_ctor_set(v___x_1716_, 0, v___x_1726_);
v___x_1731_ = v___x_1716_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___f_1722_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v___f_1729_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v___f_1728_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v___f_1727_);
v___x_1731_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v___f_1723_);
lean_ctor_set(v___x_1709_, 0, v___x_1731_);
v___x_1733_ = v___x_1709_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___f_1723_);
v___x_1733_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___f_1734_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1736_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_1738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 14, 9);
lean_closure_set(v___f_1738_, 0, v___x_1733_);
lean_closure_set(v___f_1738_, 1, v___x_1736_);
lean_closure_set(v___f_1738_, 2, v___x_1737_);
lean_closure_set(v___f_1738_, 3, v_cls_1721_);
lean_closure_set(v___f_1738_, 4, v___x_1735_);
lean_closure_set(v___f_1738_, 5, v___f_1734_);
lean_closure_set(v___f_1738_, 6, v_declName_1658_);
lean_closure_set(v___f_1738_, 7, v_val_1679_);
lean_closure_set(v___f_1738_, 8, v_val_x27_1681_);
v___x_1739_ = lean_apply_2(v_inst_1670_, lean_box(0), v___f_1738_);
v___x_1740_ = lean_apply_4(v_toBind_1677_, lean_box(0), lean_box(0), v___x_1739_, v___f_1720_);
return v___x_1740_;
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
lean_object* v_declName_1753_ = _args[0];
lean_object* v_type_1754_ = _args[1];
lean_object* v_value_1755_ = _args[2];
lean_object* v_nondep_1756_ = _args[3];
lean_object* v_toApplicative_1757_ = _args[4];
lean_object* v___x_1758_ = _args[5];
lean_object* v_us_1759_ = _args[6];
lean_object* v_decl_1760_ = _args[7];
lean_object* v_x_1761_ = _args[8];
lean_object* v_i_1762_ = _args[9];
lean_object* v_xs_1763_ = _args[10];
lean_object* v_inst_1764_ = _args[11];
lean_object* v_inst_1765_ = _args[12];
lean_object* v_inst_1766_ = _args[13];
lean_object* v_inst_1767_ = _args[14];
lean_object* v_info_1768_ = _args[15];
lean_object* v_fixed_1769_ = _args[16];
lean_object* v_used_1770_ = _args[17];
lean_object* v_body_1771_ = _args[18];
lean_object* v_toBind_1772_ = _args[19];
lean_object* v_withNewLemmas_1773_ = _args[20];
lean_object* v_val_1774_ = _args[21];
lean_object* v___x_1775_ = _args[22];
lean_object* v_val_x27_1776_ = _args[23];
_start:
{
uint8_t v_nondep_11642__boxed_1777_; uint8_t v___x_11649__boxed_1778_; lean_object* v_res_1779_; 
v_nondep_11642__boxed_1777_ = lean_unbox(v_nondep_1756_);
v___x_11649__boxed_1778_ = lean_unbox(v___x_1775_);
v_res_1779_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1753_, v_type_1754_, v_value_1755_, v_nondep_11642__boxed_1777_, v_toApplicative_1757_, v___x_1758_, v_us_1759_, v_decl_1760_, v_x_1761_, v_i_1762_, v_xs_1763_, v_inst_1764_, v_inst_1765_, v_inst_1766_, v_inst_1767_, v_info_1768_, v_fixed_1769_, v_used_1770_, v_body_1771_, v_toBind_1772_, v_withNewLemmas_1773_, v_val_1774_, v___x_11649__boxed_1778_, v_val_x27_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1780_, lean_object* v_declName_1781_, lean_object* v_type_1782_, lean_object* v_value_1783_, uint8_t v_nondep_1784_, lean_object* v_toApplicative_1785_, lean_object* v___x_1786_, lean_object* v_us_1787_, lean_object* v_inst_1788_, lean_object* v_x_1789_, lean_object* v_i_1790_, lean_object* v_xs_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_info_1795_, lean_object* v_fixed_1796_, lean_object* v_used_1797_, lean_object* v_body_1798_, lean_object* v_toBind_1799_, lean_object* v_withNewLemmas_1800_, lean_object* v_____x_1801_){
_start:
{
lean_object* v_snd_1802_; lean_object* v_fst_1803_; lean_object* v_fst_1804_; lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1824_; 
v_snd_1802_ = lean_ctor_get(v_____x_1801_, 1);
lean_inc(v_snd_1802_);
v_fst_1803_ = lean_ctor_get(v_____x_1801_, 0);
lean_inc(v_fst_1803_);
lean_dec_ref(v_____x_1801_);
v_fst_1804_ = lean_ctor_get(v_snd_1802_, 0);
v_snd_1805_ = lean_ctor_get(v_snd_1802_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_snd_1802_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1807_ = v_snd_1802_;
v_isShared_1808_ = v_isSharedCheck_1824_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_inc(v_fst_1804_);
lean_dec(v_snd_1802_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1824_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_box(0);
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
lean_ctor_set(v___x_1807_, 1, v___x_1809_);
lean_ctor_set(v___x_1807_, 0, v_decl_1780_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_decl_1780_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_box(v_nondep_1784_);
lean_inc_ref(v_inst_1788_);
v___f_1814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1814_, 0, v_declName_1781_);
lean_closure_set(v___f_1814_, 1, v_type_1782_);
lean_closure_set(v___f_1814_, 2, v_fst_1803_);
lean_closure_set(v___f_1814_, 3, v___x_1812_);
lean_closure_set(v___f_1814_, 4, v_value_1783_);
lean_closure_set(v___f_1814_, 5, v___x_1813_);
lean_closure_set(v___f_1814_, 6, v_fst_1804_);
lean_closure_set(v___f_1814_, 7, v_toApplicative_1785_);
lean_closure_set(v___f_1814_, 8, v___x_1786_);
lean_closure_set(v___f_1814_, 9, v_us_1787_);
lean_closure_set(v___f_1814_, 10, v_snd_1805_);
lean_closure_set(v___f_1814_, 11, v_inst_1788_);
v___x_1815_ = lean_mk_empty_array_with_capacity(v___x_1812_);
lean_inc_ref(v_x_1789_);
v___x_1816_ = lean_array_push(v___x_1815_, v_x_1789_);
v___x_1817_ = lean_nat_add(v_i_1790_, v___x_1812_);
v___x_1818_ = lean_array_push(v_xs_1791_, v_x_1789_);
lean_inc_ref(v_inst_1793_);
lean_inc_ref(v_inst_1788_);
v___x_1819_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1788_, v_inst_1792_, v_inst_1793_, v_inst_1794_, v_info_1795_, v_fixed_1796_, v_used_1797_, v_body_1798_, v___x_1817_, v___x_1818_);
v___x_1820_ = lean_apply_4(v_toBind_1799_, lean_box(0), lean_box(0), v___x_1819_, v___f_1814_);
v___x_1821_ = lean_apply_3(v_withNewLemmas_1800_, lean_box(0), v___x_1816_, v___x_1820_);
v___x_1822_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1793_, v_inst_1788_, v___x_1811_, v___x_1821_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1825_ = _args[0];
lean_object* v_declName_1826_ = _args[1];
lean_object* v_type_1827_ = _args[2];
lean_object* v_value_1828_ = _args[3];
lean_object* v_nondep_1829_ = _args[4];
lean_object* v_toApplicative_1830_ = _args[5];
lean_object* v___x_1831_ = _args[6];
lean_object* v_us_1832_ = _args[7];
lean_object* v_inst_1833_ = _args[8];
lean_object* v_x_1834_ = _args[9];
lean_object* v_i_1835_ = _args[10];
lean_object* v_xs_1836_ = _args[11];
lean_object* v_inst_1837_ = _args[12];
lean_object* v_inst_1838_ = _args[13];
lean_object* v_inst_1839_ = _args[14];
lean_object* v_info_1840_ = _args[15];
lean_object* v_fixed_1841_ = _args[16];
lean_object* v_used_1842_ = _args[17];
lean_object* v_body_1843_ = _args[18];
lean_object* v_toBind_1844_ = _args[19];
lean_object* v_withNewLemmas_1845_ = _args[20];
lean_object* v_____x_1846_ = _args[21];
_start:
{
uint8_t v_nondep_11584__boxed_1847_; lean_object* v_res_1848_; 
v_nondep_11584__boxed_1847_ = lean_unbox(v_nondep_1829_);
v_res_1848_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1825_, v_declName_1826_, v_type_1827_, v_value_1828_, v_nondep_11584__boxed_1847_, v_toApplicative_1830_, v___x_1831_, v_us_1832_, v_inst_1833_, v_x_1834_, v_i_1835_, v_xs_1836_, v_inst_1837_, v_inst_1838_, v_inst_1839_, v_info_1840_, v_fixed_1841_, v_used_1842_, v_body_1843_, v_toBind_1844_, v_withNewLemmas_1845_, v_____x_1846_);
lean_dec(v_i_1835_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1849_ = _args[0];
lean_object* v_declName_1850_ = _args[1];
lean_object* v_type_1851_ = _args[2];
lean_object* v_value_1852_ = _args[3];
lean_object* v_us_1853_ = _args[4];
lean_object* v___x_1854_ = _args[5];
lean_object* v_toApplicative_1855_ = _args[6];
lean_object* v_nondep_1856_ = _args[7];
lean_object* v_i_1857_ = _args[8];
lean_object* v_xs_1858_ = _args[9];
lean_object* v_inst_1859_ = _args[10];
lean_object* v_inst_1860_ = _args[11];
lean_object* v_inst_1861_ = _args[12];
lean_object* v_inst_1862_ = _args[13];
lean_object* v_info_1863_ = _args[14];
lean_object* v_fixed_1864_ = _args[15];
lean_object* v_used_1865_ = _args[16];
lean_object* v_body_1866_ = _args[17];
lean_object* v_toBind_1867_ = _args[18];
lean_object* v_____r_1868_ = _args[19];
_start:
{
uint8_t v_nondep_11567__boxed_1869_; lean_object* v_res_1870_; 
v_nondep_11567__boxed_1869_ = lean_unbox(v_nondep_1856_);
v_res_1870_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1849_, v_declName_1850_, v_type_1851_, v_value_1852_, v_us_1853_, v___x_1854_, v_toApplicative_1855_, v_nondep_11567__boxed_1869_, v_i_1857_, v_xs_1858_, v_inst_1859_, v_inst_1860_, v_inst_1861_, v_inst_1862_, v_info_1863_, v_fixed_1864_, v_used_1865_, v_body_1866_, v_toBind_1867_, v_____r_1868_);
lean_dec(v_i_1857_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_info_1875_, lean_object* v_fixed_1876_, lean_object* v_used_1877_, lean_object* v_e_1878_, lean_object* v_i_1879_, lean_object* v_xs_1880_){
_start:
{
lean_object* v_haveInfo_1886_; lean_object* v_body_1887_; lean_object* v_bodyType_1888_; lean_object* v_level_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_haveInfo_1886_ = lean_ctor_get(v_info_1875_, 0);
v_body_1887_ = lean_ctor_get(v_info_1875_, 3);
v_bodyType_1888_ = lean_ctor_get(v_info_1875_, 4);
v_level_1889_ = lean_ctor_get(v_info_1875_, 5);
v___x_1890_ = lean_array_get_size(v_haveInfo_1886_);
v___x_1891_ = lean_nat_dec_lt(v_i_1879_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v_toApplicative_1892_; lean_object* v_toBind_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1969_; 
lean_inc(v_level_1889_);
lean_inc_ref(v_bodyType_1888_);
lean_inc_ref(v_body_1887_);
lean_dec(v_i_1879_);
lean_dec_ref(v_used_1877_);
lean_dec_ref(v_fixed_1876_);
lean_dec_ref(v_info_1875_);
lean_dec_ref(v_inst_1873_);
v_toApplicative_1892_ = lean_ctor_get(v_inst_1871_, 0);
v_toBind_1893_ = lean_ctor_get(v_inst_1871_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_inst_1871_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1895_ = v_inst_1871_;
v_isShared_1896_ = v_isSharedCheck_1969_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_toBind_1893_);
lean_inc(v_toApplicative_1892_);
lean_dec(v_inst_1871_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1969_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v_toApplicative_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1967_; 
v___x_1897_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1897_, 1);
lean_dec(v_unused_1968_);
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1967_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_toApplicative_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1967_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_toFunctor_1902_; lean_object* v_toSeq_1903_; lean_object* v_toSeqLeft_1904_; lean_object* v_toSeqRight_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1965_; 
v_toFunctor_1902_ = lean_ctor_get(v_toApplicative_1898_, 0);
v_toSeq_1903_ = lean_ctor_get(v_toApplicative_1898_, 2);
v_toSeqLeft_1904_ = lean_ctor_get(v_toApplicative_1898_, 3);
v_toSeqRight_1905_ = lean_ctor_get(v_toApplicative_1898_, 4);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_toApplicative_1898_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v_toApplicative_1898_, 1);
lean_dec(v_unused_1966_);
v___x_1907_ = v_toApplicative_1898_;
v_isShared_1908_ = v_isSharedCheck_1965_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_toSeqRight_1905_);
lean_inc(v_toSeqLeft_1904_);
lean_inc(v_toSeq_1903_);
lean_inc(v_toFunctor_1902_);
lean_dec(v_toApplicative_1898_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1965_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___f_1911_; lean_object* v___f_1912_; lean_object* v___x_1914_; 
v___f_1909_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1910_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_1902_);
v___f_1911_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1911_, 0, v_toFunctor_1902_);
v___f_1912_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1912_, 0, v_toFunctor_1902_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 1, v___f_1912_);
lean_ctor_set(v___x_1895_, 0, v___f_1911_);
v___x_1914_ = v___x_1895_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___f_1911_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___f_1912_);
v___x_1914_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___f_1915_; lean_object* v___f_1916_; lean_object* v___f_1917_; lean_object* v___x_1919_; 
v___f_1915_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1915_, 0, v_toSeqRight_1905_);
v___f_1916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1916_, 0, v_toSeqLeft_1904_);
v___f_1917_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1917_, 0, v_toSeq_1903_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v___f_1915_);
lean_ctor_set(v___x_1907_, 3, v___f_1916_);
lean_ctor_set(v___x_1907_, 2, v___f_1917_);
lean_ctor_set(v___x_1907_, 1, v___f_1909_);
lean_ctor_set(v___x_1907_, 0, v___x_1914_);
v___x_1919_ = v___x_1907_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___f_1909_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v___f_1917_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v___f_1916_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v___f_1915_);
v___x_1919_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___f_1910_);
lean_ctor_set(v___x_1900_, 0, v___x_1919_);
v___x_1921_ = v___x_1900_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___f_1910_);
v___x_1921_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v_toApplicative_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1960_; 
v___x_1922_ = l_StateRefT_x27_instMonad___redArg(v___x_1921_);
v_toApplicative_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v___x_1922_, 1);
lean_dec(v_unused_1961_);
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1960_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_toApplicative_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1960_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_toFunctor_1927_; lean_object* v_toSeq_1928_; lean_object* v_toSeqLeft_1929_; lean_object* v_toSeqRight_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1958_; 
v_toFunctor_1927_ = lean_ctor_get(v_toApplicative_1923_, 0);
v_toSeq_1928_ = lean_ctor_get(v_toApplicative_1923_, 2);
v_toSeqLeft_1929_ = lean_ctor_get(v_toApplicative_1923_, 3);
v_toSeqRight_1930_ = lean_ctor_get(v_toApplicative_1923_, 4);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_toApplicative_1923_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v_toApplicative_1923_, 1);
lean_dec(v_unused_1959_);
v___x_1932_ = v_toApplicative_1923_;
v_isShared_1933_ = v_isSharedCheck_1958_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_toSeqRight_1930_);
lean_inc(v_toSeqLeft_1929_);
lean_inc(v_toSeq_1928_);
lean_inc(v_toFunctor_1927_);
lean_dec(v_toApplicative_1923_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1958_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v_cls_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___x_1946_; 
v___x_1934_ = lean_box(v___x_1891_);
lean_inc(v_toBind_1893_);
lean_inc_ref(v_body_1887_);
v___f_1935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1935_, 0, v_inst_1874_);
lean_closure_set(v___f_1935_, 1, v_bodyType_1888_);
lean_closure_set(v___f_1935_, 2, v_xs_1880_);
lean_closure_set(v___f_1935_, 3, v_toApplicative_1892_);
lean_closure_set(v___f_1935_, 4, v_level_1889_);
lean_closure_set(v___f_1935_, 5, v_e_1878_);
lean_closure_set(v___f_1935_, 6, v___x_1934_);
lean_closure_set(v___f_1935_, 7, v_body_1887_);
lean_closure_set(v___f_1935_, 8, v_toBind_1893_);
v_cls_1936_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1937_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1938_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1927_);
v___f_1939_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1939_, 0, v_toFunctor_1927_);
v___f_1940_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1940_, 0, v_toFunctor_1927_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___f_1939_);
lean_ctor_set(v___x_1941_, 1, v___f_1940_);
v___f_1942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1942_, 0, v_toSeqRight_1930_);
v___f_1943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1943_, 0, v_toSeqLeft_1929_);
v___f_1944_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1944_, 0, v_toSeq_1928_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v___f_1942_);
lean_ctor_set(v___x_1932_, 3, v___f_1943_);
lean_ctor_set(v___x_1932_, 2, v___f_1944_);
lean_ctor_set(v___x_1932_, 1, v___f_1937_);
lean_ctor_set(v___x_1932_, 0, v___x_1941_);
v___x_1946_ = v___x_1932_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___f_1937_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v___f_1944_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v___f_1943_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v___f_1942_);
v___x_1946_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v___f_1938_);
lean_ctor_set(v___x_1925_, 0, v___x_1946_);
v___x_1948_ = v___x_1925_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___f_1938_);
v___x_1948_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___f_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___f_1949_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1951_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_1953_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 12, 7);
lean_closure_set(v___f_1953_, 0, v___x_1948_);
lean_closure_set(v___f_1953_, 1, v___x_1951_);
lean_closure_set(v___f_1953_, 2, v___x_1952_);
lean_closure_set(v___f_1953_, 3, v_cls_1936_);
lean_closure_set(v___f_1953_, 4, v___x_1950_);
lean_closure_set(v___f_1953_, 5, v___f_1949_);
lean_closure_set(v___f_1953_, 6, v_body_1887_);
v___x_1954_ = lean_apply_2(v_inst_1872_, lean_box(0), v___f_1953_);
v___x_1955_ = lean_apply_4(v_toBind_1893_, lean_box(0), lean_box(0), v___x_1954_, v___f_1935_);
return v___x_1955_;
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
if (lean_obj_tag(v_e_1878_) == 8)
{
uint8_t v_nondep_1970_; 
v_nondep_1970_ = lean_ctor_get_uint8(v_e_1878_, sizeof(void*)*4 + 8);
if (v_nondep_1970_ == 1)
{
lean_object* v_declName_1971_; lean_object* v_type_1972_; lean_object* v_value_1973_; lean_object* v_body_1974_; lean_object* v_hinfo_1975_; lean_object* v_decl_1976_; lean_object* v_level_1977_; lean_object* v_x_1978_; lean_object* v_val_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v_us_1982_; uint8_t v___y_1984_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_declName_1971_ = lean_ctor_get(v_e_1878_, 0);
lean_inc(v_declName_1971_);
v_type_1972_ = lean_ctor_get(v_e_1878_, 1);
lean_inc_ref(v_type_1972_);
v_value_1973_ = lean_ctor_get(v_e_1878_, 2);
lean_inc_ref(v_value_1973_);
v_body_1974_ = lean_ctor_get(v_e_1878_, 3);
lean_inc_ref(v_body_1974_);
lean_dec_ref(v_e_1878_);
v_hinfo_1975_ = lean_array_fget_borrowed(v_haveInfo_1886_, v_i_1879_);
v_decl_1976_ = lean_ctor_get(v_hinfo_1975_, 2);
v_level_1977_ = lean_ctor_get(v_hinfo_1975_, 3);
lean_inc_ref(v_decl_1976_);
v_x_1978_ = l_Lean_LocalDecl_toExpr(v_decl_1976_);
v_val_1979_ = l_Lean_LocalDecl_value(v_decl_1976_, v_nondep_1970_);
v___x_1980_ = lean_box(0);
lean_inc(v_level_1889_);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_level_1889_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
lean_inc_ref(v___x_1981_);
lean_inc(v_level_1977_);
v_us_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1982_, 0, v_level_1977_);
lean_ctor_set(v_us_1982_, 1, v___x_1981_);
v___x_2011_ = lean_array_get_size(v_used_1877_);
v___x_2012_ = lean_nat_dec_lt(v_i_1879_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_inc_ref(v_decl_1976_);
goto v___jp_1994_;
}
else
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = lean_array_fget_borrowed(v_used_1877_, v_i_1879_);
v___x_2014_ = lean_unbox(v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v_toApplicative_2015_; lean_object* v_toBind_2016_; lean_object* v___x_2017_; lean_object* v_toApplicative_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_x_1978_);
v_toApplicative_2015_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc_ref(v_toApplicative_2015_);
v_toBind_2016_ = lean_ctor_get(v_inst_1871_, 1);
lean_inc(v_toBind_2016_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2017_, 1);
lean_dec(v_unused_2086_);
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2085_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_toApplicative_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2085_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_toFunctor_2022_; lean_object* v_toSeq_2023_; lean_object* v_toSeqLeft_2024_; lean_object* v_toSeqRight_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2083_; 
v_toFunctor_2022_ = lean_ctor_get(v_toApplicative_2018_, 0);
v_toSeq_2023_ = lean_ctor_get(v_toApplicative_2018_, 2);
v_toSeqLeft_2024_ = lean_ctor_get(v_toApplicative_2018_, 3);
v_toSeqRight_2025_ = lean_ctor_get(v_toApplicative_2018_, 4);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_toApplicative_2018_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_toApplicative_2018_, 1);
lean_dec(v_unused_2084_);
v___x_2027_ = v_toApplicative_2018_;
v_isShared_2028_ = v_isSharedCheck_2083_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_toSeqRight_2025_);
lean_inc(v_toSeqLeft_2024_);
lean_inc(v_toSeq_2023_);
lean_inc(v_toFunctor_2022_);
lean_dec(v_toApplicative_2018_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2083_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___f_2029_; lean_object* v___f_2030_; lean_object* v___f_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; lean_object* v___f_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___x_2038_; 
v___f_2029_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_2030_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref(v_toFunctor_2022_);
v___f_2031_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2031_, 0, v_toFunctor_2022_);
v___f_2032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2032_, 0, v_toFunctor_2022_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___f_2031_);
lean_ctor_set(v___x_2033_, 1, v___f_2032_);
v___f_2034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2034_, 0, v_toSeqRight_2025_);
v___f_2035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2035_, 0, v_toSeqLeft_2024_);
v___f_2036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2036_, 0, v_toSeq_2023_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 4, v___f_2034_);
lean_ctor_set(v___x_2027_, 3, v___f_2035_);
lean_ctor_set(v___x_2027_, 2, v___f_2036_);
lean_ctor_set(v___x_2027_, 1, v___f_2029_);
lean_ctor_set(v___x_2027_, 0, v___x_2033_);
v___x_2038_ = v___x_2027_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___f_2029_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v___f_2036_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v___f_2035_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v___f_2034_);
v___x_2038_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___f_2030_);
lean_ctor_set(v___x_2020_, 0, v___x_2038_);
v___x_2040_ = v___x_2020_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___f_2030_);
v___x_2040_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v_toApplicative_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2079_; 
v___x_2041_ = l_StateRefT_x27_instMonad___redArg(v___x_2040_);
v_toApplicative_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v___x_2041_, 1);
lean_dec(v_unused_2080_);
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2079_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_toApplicative_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2079_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_toFunctor_2046_; lean_object* v_toSeq_2047_; lean_object* v_toSeqLeft_2048_; lean_object* v_toSeqRight_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2077_; 
v_toFunctor_2046_ = lean_ctor_get(v_toApplicative_2042_, 0);
v_toSeq_2047_ = lean_ctor_get(v_toApplicative_2042_, 2);
v_toSeqLeft_2048_ = lean_ctor_get(v_toApplicative_2042_, 3);
v_toSeqRight_2049_ = lean_ctor_get(v_toApplicative_2042_, 4);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_toApplicative_2042_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_toApplicative_2042_, 1);
lean_dec(v_unused_2078_);
v___x_2051_ = v_toApplicative_2042_;
v_isShared_2052_ = v_isSharedCheck_2077_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_toSeqRight_2049_);
lean_inc(v_toSeqLeft_2048_);
lean_inc(v_toSeq_2047_);
lean_inc(v_toFunctor_2046_);
lean_dec(v_toApplicative_2042_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2077_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___f_2054_; lean_object* v_cls_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___f_2061_; lean_object* v___f_2062_; lean_object* v___f_2063_; lean_object* v___x_2065_; 
v___x_2053_ = lean_box(v_nondep_1970_);
lean_inc(v_toBind_2016_);
lean_inc(v_inst_1872_);
lean_inc(v_declName_1971_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2054_, 0, v___x_1980_);
lean_closure_set(v___f_2054_, 1, v_declName_1971_);
lean_closure_set(v___f_2054_, 2, v_type_1972_);
lean_closure_set(v___f_2054_, 3, v_value_1973_);
lean_closure_set(v___f_2054_, 4, v_us_1982_);
lean_closure_set(v___f_2054_, 5, v___x_1981_);
lean_closure_set(v___f_2054_, 6, v_toApplicative_2015_);
lean_closure_set(v___f_2054_, 7, v___x_2053_);
lean_closure_set(v___f_2054_, 8, v_i_1879_);
lean_closure_set(v___f_2054_, 9, v_xs_1880_);
lean_closure_set(v___f_2054_, 10, v_inst_1871_);
lean_closure_set(v___f_2054_, 11, v_inst_1872_);
lean_closure_set(v___f_2054_, 12, v_inst_1873_);
lean_closure_set(v___f_2054_, 13, v_inst_1874_);
lean_closure_set(v___f_2054_, 14, v_info_1875_);
lean_closure_set(v___f_2054_, 15, v_fixed_1876_);
lean_closure_set(v___f_2054_, 16, v_used_1877_);
lean_closure_set(v___f_2054_, 17, v_body_1974_);
lean_closure_set(v___f_2054_, 18, v_toBind_2016_);
v_cls_2055_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_2056_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_2057_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_2046_);
v___f_2058_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2058_, 0, v_toFunctor_2046_);
v___f_2059_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2059_, 0, v_toFunctor_2046_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___f_2058_);
lean_ctor_set(v___x_2060_, 1, v___f_2059_);
v___f_2061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2061_, 0, v_toSeqRight_2049_);
v___f_2062_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2062_, 0, v_toSeqLeft_2048_);
v___f_2063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2063_, 0, v_toSeq_2047_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 4, v___f_2061_);
lean_ctor_set(v___x_2051_, 3, v___f_2062_);
lean_ctor_set(v___x_2051_, 2, v___f_2063_);
lean_ctor_set(v___x_2051_, 1, v___f_2056_);
lean_ctor_set(v___x_2051_, 0, v___x_2060_);
v___x_2065_ = v___x_2051_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___f_2056_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v___f_2063_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v___f_2062_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v___f_2061_);
v___x_2065_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___f_2057_);
lean_ctor_set(v___x_2044_, 0, v___x_2065_);
v___x_2067_ = v___x_2044_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___f_2057_);
v___x_2067_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___f_2068_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_2070_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__17));
v___f_2072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 13, 8);
lean_closure_set(v___f_2072_, 0, v___x_2067_);
lean_closure_set(v___f_2072_, 1, v___x_2070_);
lean_closure_set(v___f_2072_, 2, v___x_2071_);
lean_closure_set(v___f_2072_, 3, v_cls_2055_);
lean_closure_set(v___f_2072_, 4, v___x_2069_);
lean_closure_set(v___f_2072_, 5, v___f_2068_);
lean_closure_set(v___f_2072_, 6, v_declName_1971_);
lean_closure_set(v___f_2072_, 7, v_val_1979_);
v___x_2073_ = lean_apply_2(v_inst_1872_, lean_box(0), v___f_2072_);
v___x_2074_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v___x_2073_, v___f_2054_);
return v___x_2074_;
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
lean_inc_ref(v_decl_1976_);
goto v___jp_1994_;
}
}
v___jp_1983_:
{
lean_object* v_toApplicative_1985_; lean_object* v_toBind_1986_; lean_object* v_withNewLemmas_1987_; lean_object* v_dsimp_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_toApplicative_1985_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc_ref(v_toApplicative_1985_);
v_toBind_1986_ = lean_ctor_get(v_inst_1871_, 1);
lean_inc(v_toBind_1986_);
v_withNewLemmas_1987_ = lean_ctor_get(v_inst_1874_, 0);
lean_inc(v_withNewLemmas_1987_);
v_dsimp_1988_ = lean_ctor_get(v_inst_1874_, 1);
lean_inc(v_dsimp_1988_);
v___x_1989_ = lean_box(v_nondep_1970_);
v___x_1990_ = lean_box(v___y_1984_);
lean_inc_ref(v_val_1979_);
lean_inc(v_toBind_1986_);
v___f_1991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 24, 23);
lean_closure_set(v___f_1991_, 0, v_declName_1971_);
lean_closure_set(v___f_1991_, 1, v_type_1972_);
lean_closure_set(v___f_1991_, 2, v_value_1973_);
lean_closure_set(v___f_1991_, 3, v___x_1989_);
lean_closure_set(v___f_1991_, 4, v_toApplicative_1985_);
lean_closure_set(v___f_1991_, 5, v___x_1981_);
lean_closure_set(v___f_1991_, 6, v_us_1982_);
lean_closure_set(v___f_1991_, 7, v_decl_1976_);
lean_closure_set(v___f_1991_, 8, v_x_1978_);
lean_closure_set(v___f_1991_, 9, v_i_1879_);
lean_closure_set(v___f_1991_, 10, v_xs_1880_);
lean_closure_set(v___f_1991_, 11, v_inst_1871_);
lean_closure_set(v___f_1991_, 12, v_inst_1872_);
lean_closure_set(v___f_1991_, 13, v_inst_1873_);
lean_closure_set(v___f_1991_, 14, v_inst_1874_);
lean_closure_set(v___f_1991_, 15, v_info_1875_);
lean_closure_set(v___f_1991_, 16, v_fixed_1876_);
lean_closure_set(v___f_1991_, 17, v_used_1877_);
lean_closure_set(v___f_1991_, 18, v_body_1974_);
lean_closure_set(v___f_1991_, 19, v_toBind_1986_);
lean_closure_set(v___f_1991_, 20, v_withNewLemmas_1987_);
lean_closure_set(v___f_1991_, 21, v_val_1979_);
lean_closure_set(v___f_1991_, 22, v___x_1990_);
v___x_1992_ = lean_apply_1(v_dsimp_1988_, v_val_1979_);
v___x_1993_ = lean_apply_4(v_toBind_1986_, lean_box(0), lean_box(0), v___x_1992_, v___f_1991_);
return v___x_1993_;
}
v___jp_1994_:
{
uint8_t v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = 0;
v___x_1996_ = lean_array_get_size(v_fixed_1876_);
v___x_1997_ = lean_nat_dec_lt(v_i_1879_, v___x_1996_);
if (v___x_1997_ == 0)
{
v___y_1984_ = v___x_1995_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = lean_array_fget_borrowed(v_fixed_1876_, v_i_1879_);
v___x_1999_ = lean_unbox(v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v_toApplicative_2000_; lean_object* v_toBind_2001_; lean_object* v_withNewLemmas_2002_; lean_object* v_simp_2003_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_inc(v___x_1998_);
lean_inc(v_level_1977_);
v_toApplicative_2000_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc_ref(v_toApplicative_2000_);
v_toBind_2001_ = lean_ctor_get(v_inst_1871_, 1);
lean_inc(v_toBind_2001_);
v_withNewLemmas_2002_ = lean_ctor_get(v_inst_1874_, 0);
lean_inc(v_withNewLemmas_2002_);
v_simp_2003_ = lean_ctor_get(v_inst_1874_, 2);
lean_inc(v_simp_2003_);
v___x_2004_ = lean_box(v_nondep_1970_);
lean_inc(v_toBind_2001_);
lean_inc(v_inst_1872_);
lean_inc_ref(v_xs_1880_);
lean_inc_ref(v_toApplicative_2000_);
lean_inc_ref(v_value_1973_);
lean_inc_ref(v_type_1972_);
lean_inc(v_declName_1971_);
v___f_2005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_2005_, 0, v_decl_1976_);
lean_closure_set(v___f_2005_, 1, v_declName_1971_);
lean_closure_set(v___f_2005_, 2, v_type_1972_);
lean_closure_set(v___f_2005_, 3, v_value_1973_);
lean_closure_set(v___f_2005_, 4, v___x_2004_);
lean_closure_set(v___f_2005_, 5, v_toApplicative_2000_);
lean_closure_set(v___f_2005_, 6, v___x_1981_);
lean_closure_set(v___f_2005_, 7, v_us_1982_);
lean_closure_set(v___f_2005_, 8, v_inst_1871_);
lean_closure_set(v___f_2005_, 9, v_x_1978_);
lean_closure_set(v___f_2005_, 10, v_i_1879_);
lean_closure_set(v___f_2005_, 11, v_xs_1880_);
lean_closure_set(v___f_2005_, 12, v_inst_1872_);
lean_closure_set(v___f_2005_, 13, v_inst_1873_);
lean_closure_set(v___f_2005_, 14, v_inst_1874_);
lean_closure_set(v___f_2005_, 15, v_info_1875_);
lean_closure_set(v___f_2005_, 16, v_fixed_1876_);
lean_closure_set(v___f_2005_, 17, v_used_1877_);
lean_closure_set(v___f_2005_, 18, v_body_1974_);
lean_closure_set(v___f_2005_, 19, v_toBind_2001_);
lean_closure_set(v___f_2005_, 20, v_withNewLemmas_2002_);
v___f_2006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_2006_, 0, v___f_2005_);
v___x_2007_ = lean_box(v_nondep_1970_);
lean_inc_ref(v_val_1979_);
lean_inc_ref(v___f_2006_);
lean_inc(v_toBind_2001_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_2008_, 0, v_toApplicative_2000_);
lean_closure_set(v___f_2008_, 1, v_level_1977_);
lean_closure_set(v___f_2008_, 2, v___x_1980_);
lean_closure_set(v___f_2008_, 3, v_type_1972_);
lean_closure_set(v___f_2008_, 4, v_value_1973_);
lean_closure_set(v___f_2008_, 5, v___x_1998_);
lean_closure_set(v___f_2008_, 6, v_toBind_2001_);
lean_closure_set(v___f_2008_, 7, v___f_2006_);
lean_closure_set(v___f_2008_, 8, v_xs_1880_);
lean_closure_set(v___f_2008_, 9, v___x_2007_);
lean_closure_set(v___f_2008_, 10, v___f_2006_);
lean_closure_set(v___f_2008_, 11, v_declName_1971_);
lean_closure_set(v___f_2008_, 12, v_val_1979_);
lean_closure_set(v___f_2008_, 13, v_inst_1872_);
v___x_2009_ = lean_apply_1(v_simp_2003_, v_val_1979_);
v___x_2010_ = lean_apply_4(v_toBind_2001_, lean_box(0), lean_box(0), v___x_2009_, v___f_2008_);
return v___x_2010_;
}
else
{
v___y_1984_ = v___x_1995_;
goto v___jp_1983_;
}
}
}
}
else
{
lean_dec_ref(v_e_1878_);
lean_dec_ref(v_xs_1880_);
lean_dec(v_i_1879_);
lean_dec_ref(v_used_1877_);
lean_dec_ref(v_fixed_1876_);
lean_dec_ref(v_info_1875_);
lean_dec_ref(v_inst_1874_);
lean_dec_ref(v_inst_1873_);
lean_dec(v_inst_1872_);
goto v___jp_1881_;
}
}
else
{
lean_dec_ref(v_xs_1880_);
lean_dec(v_i_1879_);
lean_dec_ref(v_e_1878_);
lean_dec_ref(v_used_1877_);
lean_dec_ref(v_fixed_1876_);
lean_dec_ref(v_info_1875_);
lean_dec_ref(v_inst_1874_);
lean_dec_ref(v_inst_1873_);
lean_dec(v_inst_1872_);
goto v___jp_1881_;
}
}
v___jp_1881_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1882_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1883_ = l_instInhabitedOfMonad___redArg(v_inst_1871_, v___x_1882_);
v___x_1884_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1885_ = l_panic___redArg(v___x_1883_, v___x_1884_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_2087_, lean_object* v_declName_2088_, lean_object* v_type_2089_, lean_object* v_value_2090_, lean_object* v_us_2091_, lean_object* v___x_2092_, lean_object* v_toApplicative_2093_, uint8_t v_nondep_2094_, lean_object* v_i_2095_, lean_object* v_xs_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_info_2101_, lean_object* v_fixed_2102_, lean_object* v_used_2103_, lean_object* v_body_2104_, lean_object* v_toBind_2105_, lean_object* v_____r_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v_x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_2108_ = l_Lean_mkConst(v___x_2107_, v___x_2087_);
v___x_2109_ = lean_unsigned_to_nat(1u);
v___x_2110_ = lean_box(v_nondep_2094_);
v___f_2111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_2111_, 0, v___x_2109_);
lean_closure_set(v___f_2111_, 1, v_declName_2088_);
lean_closure_set(v___f_2111_, 2, v_type_2089_);
lean_closure_set(v___f_2111_, 3, v_value_2090_);
lean_closure_set(v___f_2111_, 4, v_us_2091_);
lean_closure_set(v___f_2111_, 5, v___x_2092_);
lean_closure_set(v___f_2111_, 6, v_toApplicative_2093_);
lean_closure_set(v___f_2111_, 7, v___x_2110_);
v___x_2112_ = lean_nat_add(v_i_2095_, v___x_2109_);
v___x_2113_ = lean_array_push(v_xs_2096_, v_x_2108_);
v___x_2114_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2097_, v_inst_2098_, v_inst_2099_, v_inst_2100_, v_info_2101_, v_fixed_2102_, v_used_2103_, v_body_2104_, v___x_2112_, v___x_2113_);
v___x_2115_ = lean_apply_4(v_toBind_2105_, lean_box(0), lean_box(0), v___x_2114_, v___f_2111_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_info_2121_, lean_object* v_fixed_2122_, lean_object* v_used_2123_, lean_object* v_e_2124_, lean_object* v_i_2125_, lean_object* v_xs_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2117_, v_inst_2118_, v_inst_2119_, v_inst_2120_, v_info_2121_, v_fixed_2122_, v_used_2123_, v_e_2124_, v_i_2125_, v_xs_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_2128_){
_start:
{
switch(v_x_2128_)
{
case 0:
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
return v___x_2129_;
}
case 1:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_unsigned_to_nat(1u);
return v___x_2130_;
}
default: 
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_unsigned_to_nat(2u);
return v___x_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2132_){
_start:
{
uint8_t v_x_boxed_2133_; lean_object* v_res_2134_; 
v_x_boxed_2133_ = lean_unbox(v_x_2132_);
v_res_2134_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2133_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t v_x_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object* v_x_2137_){
_start:
{
uint8_t v_x_4__boxed_2138_; lean_object* v_res_2139_; 
v_x_4__boxed_2138_ = lean_unbox(v_x_2137_);
v_res_2139_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_2138_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2140_){
_start:
{
lean_inc(v_k_2140_);
return v_k_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2141_);
lean_dec(v_k_2141_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2143_, lean_object* v_ctorIdx_2144_, uint8_t v_t_2145_, lean_object* v_h_2146_, lean_object* v_k_2147_){
_start:
{
lean_inc(v_k_2147_);
return v_k_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2148_, lean_object* v_ctorIdx_2149_, lean_object* v_t_2150_, lean_object* v_h_2151_, lean_object* v_k_2152_){
_start:
{
uint8_t v_t_boxed_2153_; lean_object* v_res_2154_; 
v_t_boxed_2153_ = lean_unbox(v_t_2150_);
v_res_2154_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2148_, v_ctorIdx_2149_, v_t_boxed_2153_, v_h_2151_, v_k_2152_);
lean_dec(v_k_2152_);
lean_dec(v_ctorIdx_2149_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2155_){
_start:
{
lean_inc(v_no_2155_);
return v_no_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2156_);
lean_dec(v_no_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2158_, uint8_t v_t_2159_, lean_object* v_h_2160_, lean_object* v_no_2161_){
_start:
{
lean_inc(v_no_2161_);
return v_no_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2162_, lean_object* v_t_2163_, lean_object* v_h_2164_, lean_object* v_no_2165_){
_start:
{
uint8_t v_t_boxed_2166_; lean_object* v_res_2167_; 
v_t_boxed_2166_ = lean_unbox(v_t_2163_);
v_res_2167_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2162_, v_t_boxed_2166_, v_h_2164_, v_no_2165_);
lean_dec(v_no_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2168_){
_start:
{
lean_inc(v_singlePass_2168_);
return v_singlePass_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2169_);
lean_dec(v_singlePass_2169_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2171_, uint8_t v_t_2172_, lean_object* v_h_2173_, lean_object* v_singlePass_2174_){
_start:
{
lean_inc(v_singlePass_2174_);
return v_singlePass_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2175_, lean_object* v_t_2176_, lean_object* v_h_2177_, lean_object* v_singlePass_2178_){
_start:
{
uint8_t v_t_boxed_2179_; lean_object* v_res_2180_; 
v_t_boxed_2179_ = lean_unbox(v_t_2176_);
v_res_2180_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2175_, v_t_boxed_2179_, v_h_2177_, v_singlePass_2178_);
lean_dec(v_singlePass_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2181_){
_start:
{
lean_inc(v_twoPasses_2181_);
return v_twoPasses_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2182_);
lean_dec(v_twoPasses_2182_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2184_, uint8_t v_t_2185_, lean_object* v_h_2186_, lean_object* v_twoPasses_2187_){
_start:
{
lean_inc(v_twoPasses_2187_);
return v_twoPasses_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2188_, lean_object* v_t_2189_, lean_object* v_h_2190_, lean_object* v_twoPasses_2191_){
_start:
{
uint8_t v_t_boxed_2192_; lean_object* v_res_2193_; 
v_t_boxed_2192_ = lean_unbox(v_t_2189_);
v_res_2193_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2188_, v_t_boxed_2192_, v_h_2190_, v_twoPasses_2191_);
lean_dec(v_twoPasses_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2194_, lean_object* v_b_2195_, lean_object* v_c_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2202_; 
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
v___x_2202_ = lean_apply_7(v_k_2194_, v_b_2195_, v_c_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, lean_box(0));
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2203_, lean_object* v_b_2204_, lean_object* v_c_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2203_, v_b_2204_, v_c_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2212_, lean_object* v_k_2213_, uint8_t v_cleanupAnnotations_2214_, uint8_t v_preserveNondepLet_2215_, uint8_t v_nondepLetOnly_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___f_2222_; uint8_t v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___f_2222_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2222_, 0, v_k_2213_);
v___x_2223_ = 0;
v___x_2224_ = 1;
v___x_2225_ = lean_box(0);
v___x_2226_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2212_, v___x_2223_, v___x_2224_, v_preserveNondepLet_2215_, v_nondepLetOnly_2216_, v___x_2225_, v___f_2222_, v_cleanupAnnotations_2214_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_a_2235_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2226_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2226_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2243_, lean_object* v_k_2244_, lean_object* v_cleanupAnnotations_2245_, lean_object* v_preserveNondepLet_2246_, lean_object* v_nondepLetOnly_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2253_; uint8_t v_preserveNondepLet_boxed_2254_; uint8_t v_nondepLetOnly_boxed_2255_; lean_object* v_res_2256_; 
v_cleanupAnnotations_boxed_2253_ = lean_unbox(v_cleanupAnnotations_2245_);
v_preserveNondepLet_boxed_2254_ = lean_unbox(v_preserveNondepLet_2246_);
v_nondepLetOnly_boxed_2255_ = lean_unbox(v_nondepLetOnly_2247_);
v_res_2256_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2243_, v_k_2244_, v_cleanupAnnotations_boxed_2253_, v_preserveNondepLet_boxed_2254_, v_nondepLetOnly_boxed_2255_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2257_, lean_object* v_e_2258_, lean_object* v_k_2259_, uint8_t v_cleanupAnnotations_2260_, uint8_t v_preserveNondepLet_2261_, uint8_t v_nondepLetOnly_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2258_, v_k_2259_, v_cleanupAnnotations_2260_, v_preserveNondepLet_2261_, v_nondepLetOnly_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_e_2270_, lean_object* v_k_2271_, lean_object* v_cleanupAnnotations_2272_, lean_object* v_preserveNondepLet_2273_, lean_object* v_nondepLetOnly_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2280_; uint8_t v_preserveNondepLet_boxed_2281_; uint8_t v_nondepLetOnly_boxed_2282_; lean_object* v_res_2283_; 
v_cleanupAnnotations_boxed_2280_ = lean_unbox(v_cleanupAnnotations_2272_);
v_preserveNondepLet_boxed_2281_ = lean_unbox(v_preserveNondepLet_2273_);
v_nondepLetOnly_boxed_2282_ = lean_unbox(v_nondepLetOnly_2274_);
v_res_2283_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2269_, v_e_2270_, v_k_2271_, v_cleanupAnnotations_boxed_2280_, v_preserveNondepLet_boxed_2281_, v_nondepLetOnly_boxed_2282_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2284_, lean_object* v_b_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_snd_2290_; lean_object* v_fst_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2346_; 
v_snd_2290_ = lean_ctor_get(v_b_2285_, 1);
v_fst_2291_ = lean_ctor_get(v_b_2285_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_b_2285_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2293_ = v_b_2285_;
v_isShared_2294_ = v_isSharedCheck_2346_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snd_2290_);
lean_inc(v_fst_2291_);
lean_dec(v_b_2285_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2346_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_fst_2295_; lean_object* v_snd_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2345_; 
v_fst_2295_ = lean_ctor_get(v_snd_2290_, 0);
v_snd_2296_ = lean_ctor_get(v_snd_2290_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_snd_2290_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2298_ = v_snd_2290_;
v_isShared_2299_ = v_isSharedCheck_2345_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_snd_2296_);
lean_inc(v_fst_2295_);
lean_dec(v_snd_2290_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2345_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_nat_dec_lt(v___x_2300_, v_snd_2296_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2303_; 
if (v_isShared_2299_ == 0)
{
v___x_2303_ = v___x_2298_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_fst_2295_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_snd_2296_);
v___x_2303_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2303_);
v___x_2305_ = v___x_2293_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
}
else
{
lean_object* v_fvarSet_2309_; lean_object* v___x_2310_; lean_object* v_i_2311_; lean_object* v___x_2312_; lean_object* v_x_2313_; lean_object* v_xFVarId_2314_; uint8_t v___x_2315_; 
v_fvarSet_2309_ = lean_ctor_get(v_fst_2291_, 1);
v___x_2310_ = lean_unsigned_to_nat(1u);
v_i_2311_ = lean_nat_sub(v_snd_2296_, v___x_2310_);
lean_dec(v_snd_2296_);
v___x_2312_ = l_Lean_instInhabitedExpr;
v_x_2313_ = lean_array_get_borrowed(v___x_2312_, v_xs_2284_, v_i_2311_);
v_xFVarId_2314_ = l_Lean_Expr_fvarId_x21(v_x_2313_);
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_xFVarId_2314_, v_fvarSet_2309_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2317_; 
lean_dec(v_xFVarId_2314_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_i_2311_);
v___x_2317_ = v___x_2298_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_fst_2295_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_i_2311_);
v___x_2317_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2317_);
v___x_2319_ = v___x_2293_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
v_b_2285_ = v___x_2319_;
goto _start;
}
}
}
else
{
lean_object* v___x_2323_; 
lean_inc_ref(v___y_2286_);
v___x_2323_ = l_Lean_FVarId_getDecl___redArg(v_xFVarId_2314_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = l_Lean_LocalDecl_type(v_a_2324_);
v___x_2326_ = l_Lean_collectFVars(v_fst_2291_, v___x_2325_);
v___x_2327_ = l_Lean_LocalDecl_value(v_a_2324_, v___x_2315_);
lean_dec(v_a_2324_);
v___x_2328_ = l_Lean_collectFVars(v___x_2326_, v___x_2327_);
lean_inc(v_x_2313_);
v___x_2329_ = lean_array_push(v_fst_2295_, v_x_2313_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_i_2311_);
lean_ctor_set(v___x_2298_, 0, v___x_2329_);
v___x_2331_ = v___x_2298_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_i_2311_);
v___x_2331_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2331_);
lean_ctor_set(v___x_2293_, 0, v___x_2328_);
v___x_2333_ = v___x_2293_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v_b_2285_ = v___x_2333_;
goto _start;
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_i_2311_);
lean_del_object(v___x_2298_);
lean_dec(v_fst_2295_);
lean_del_object(v___x_2293_);
lean_dec(v_fst_2291_);
v_a_2337_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2323_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2323_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2347_, lean_object* v_b_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2347_, v_b_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_xs_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2354_, lean_object* v_e_2355_, lean_object* v_xs_2356_, lean_object* v_body_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_s_2366_; lean_object* v_i_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2363_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2354_);
lean_ctor_set(v___x_2365_, 2, v___x_2364_);
lean_inc_ref(v_body_2357_);
v_s_2366_ = l_Lean_collectFVars(v___x_2365_, v_body_2357_);
v_i_2367_ = lean_array_get_size(v_xs_2356_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2364_);
lean_ctor_set(v___x_2368_, 1, v_i_2367_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_s_2366_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2356_, v___x_2369_, v___y_2358_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2386_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2386_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2386_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v_snd_2375_; lean_object* v_fst_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_snd_2375_ = lean_ctor_get(v_a_2371_, 1);
lean_inc(v_snd_2375_);
lean_dec(v_a_2371_);
v_fst_2376_ = lean_ctor_get(v_snd_2375_, 0);
lean_inc(v_fst_2376_);
lean_dec(v_snd_2375_);
v___x_2377_ = lean_array_get_size(v_fst_2376_);
v___x_2378_ = lean_nat_dec_eq(v___x_2377_, v_i_2367_);
if (v___x_2378_ == 0)
{
uint8_t v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; 
lean_del_object(v___x_2373_);
lean_dec_ref(v_e_2355_);
v___x_2379_ = 1;
v___x_2380_ = l_Array_reverse___redArg(v_fst_2376_);
v___x_2381_ = 1;
v___x_2382_ = l_Lean_Meta_mkLetFVars(v___x_2380_, v_body_2357_, v___x_2379_, v___x_2378_, v___x_2381_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec_ref(v___x_2380_);
return v___x_2382_;
}
else
{
lean_object* v___x_2384_; 
lean_dec(v_fst_2376_);
lean_dec_ref(v_body_2357_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v_e_2355_);
v___x_2384_ = v___x_2373_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_e_2355_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v_body_2357_);
lean_dec_ref(v_e_2355_);
v_a_2387_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2370_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2370_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2395_, lean_object* v_e_2396_, lean_object* v_xs_2397_, lean_object* v_body_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2395_, v_e_2396_, v_xs_2397_, v_body_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_xs_2397_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v___f_2412_; uint8_t v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2411_ = lean_box(1);
lean_inc_ref(v_e_2405_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2412_, 0, v___x_2411_);
lean_closure_set(v___f_2412_, 1, v_e_2405_);
v___x_2413_ = 0;
v___x_2414_ = 1;
v___x_2415_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2405_, v___f_2412_, v___x_2413_, v___x_2414_, v___x_2413_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_zetaUnused(v_e_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2423_, v_b_2424_, v___y_2425_, v___y_2427_, v___y_2428_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2431_, lean_object* v_b_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2431_, v_b_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec_ref(v_xs_2431_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2443_, lean_object* v_source_2444_, lean_object* v_result_2445_, uint8_t v_keepUnused_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
uint8_t v_modified_2452_; 
v_modified_2452_ = lean_ctor_get_uint8(v_result_2445_, sizeof(void*)*5);
if (v_modified_2452_ == 0)
{
if (v_keepUnused_2446_ == 0)
{
lean_object* v_exprType_2453_; lean_object* v___x_2454_; 
v_exprType_2453_ = lean_ctor_get(v_result_2445_, 1);
lean_inc_ref(v_exprType_2453_);
lean_dec_ref(v_result_2445_);
lean_inc_ref(v_source_2444_);
v___x_2454_ = l_Lean_Meta_zetaUnused(v_source_2444_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2473_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2473_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2473_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_expr_eqv(v_a_2455_, v_source_2444_);
lean_dec_ref(v_source_2444_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_u_2443_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_mkConst(v___x_2460_, v___x_2462_);
lean_inc(v_a_2455_);
v___x_2464_ = l_Lean_mkAppB(v___x_2463_, v_exprType_2453_, v_a_2455_);
v___x_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2455_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2465_);
v___x_2467_ = v___x_2457_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_dec(v_a_2455_);
lean_dec_ref(v_exprType_2453_);
lean_dec(v_u_2443_);
v___x_2469_ = lean_box(0);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2469_);
v___x_2471_ = v___x_2457_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_exprType_2453_);
lean_dec_ref(v_source_2444_);
lean_dec(v_u_2443_);
v_a_2474_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2454_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2454_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref(v_result_2445_);
lean_dec_ref(v_source_2444_);
lean_dec(v_u_2443_);
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
else
{
lean_object* v_expr_2484_; lean_object* v_exprType_2485_; lean_object* v_exprInit_2486_; lean_object* v_exprResult_2487_; lean_object* v_proof_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_proof_2496_; 
v_expr_2484_ = lean_ctor_get(v_result_2445_, 0);
lean_inc_ref(v_expr_2484_);
v_exprType_2485_ = lean_ctor_get(v_result_2445_, 1);
lean_inc_ref(v_exprType_2485_);
v_exprInit_2486_ = lean_ctor_get(v_result_2445_, 2);
lean_inc_ref(v_exprInit_2486_);
v_exprResult_2487_ = lean_ctor_get(v_result_2445_, 3);
lean_inc_ref(v_exprResult_2487_);
v_proof_2488_ = lean_ctor_get(v_result_2445_, 4);
lean_inc_ref(v_proof_2488_);
lean_dec_ref(v_result_2445_);
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2491_, 0, v_u_2443_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
lean_inc_ref(v___x_2491_);
v___x_2492_ = l_Lean_mkConst(v___x_2489_, v___x_2491_);
lean_inc_ref(v_exprType_2485_);
lean_inc_ref(v___x_2492_);
v___x_2493_ = l_Lean_mkApp3(v___x_2492_, v_exprType_2485_, v_exprInit_2486_, v_expr_2484_);
v___x_2494_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2488_, v___x_2493_);
lean_inc_ref(v_exprResult_2487_);
lean_inc_ref(v_source_2444_);
lean_inc_ref(v_exprType_2485_);
v___x_2495_ = l_Lean_mkApp3(v___x_2492_, v_exprType_2485_, v_source_2444_, v_exprResult_2487_);
v_proof_2496_ = l_Lean_Meta_mkExpectedPropHint(v___x_2494_, v___x_2495_);
if (v_keepUnused_2446_ == 0)
{
lean_object* v___x_2497_; 
lean_inc_ref(v_exprResult_2487_);
v___x_2497_ = l_Lean_Meta_zetaUnused(v_exprResult_2487_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2517_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2517_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2517_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_expr_eqv(v_a_2498_, v_exprResult_2487_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2491_);
v___x_2504_ = l_Lean_mkConst(v___x_2503_, v___x_2491_);
v___x_2505_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2506_ = l_Lean_mkConst(v___x_2505_, v___x_2491_);
lean_inc(v_a_2498_);
lean_inc_ref(v_exprType_2485_);
v___x_2507_ = l_Lean_mkAppB(v___x_2506_, v_exprType_2485_, v_a_2498_);
lean_inc(v_a_2498_);
v___x_2508_ = l_Lean_mkApp6(v___x_2504_, v_exprType_2485_, v_source_2444_, v_exprResult_2487_, v_a_2498_, v_proof_2496_, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_a_2498_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2509_);
v___x_2511_ = v___x_2500_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
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
lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v_a_2498_);
lean_dec_ref(v___x_2491_);
lean_dec_ref(v_exprType_2485_);
lean_dec_ref(v_source_2444_);
v___x_2513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2513_, 0, v_exprResult_2487_);
lean_ctor_set(v___x_2513_, 1, v_proof_2496_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2513_);
v___x_2515_ = v___x_2500_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_proof_2496_);
lean_dec_ref(v___x_2491_);
lean_dec_ref(v_exprResult_2487_);
lean_dec_ref(v_exprType_2485_);
lean_dec_ref(v_source_2444_);
v_a_2518_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2497_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2497_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec_ref(v___x_2491_);
lean_dec_ref(v_exprType_2485_);
lean_dec_ref(v_source_2444_);
v___x_2526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_exprResult_2487_);
lean_ctor_set(v___x_2526_, 1, v_proof_2496_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2528_, lean_object* v_source_2529_, lean_object* v_result_2530_, lean_object* v_keepUnused_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
uint8_t v_keepUnused_boxed_2537_; lean_object* v_res_2538_; 
v_keepUnused_boxed_2537_ = lean_unbox(v_keepUnused_2531_);
v_res_2538_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2528_, v_source_2529_, v_result_2530_, v_keepUnused_boxed_2537_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2539_, lean_object* v_e_2540_, lean_object* v_inst_2541_, uint8_t v_zetaUnusedMode_2542_, uint8_t v___x_2543_, uint8_t v___x_2544_, lean_object* v_r_2545_){
_start:
{
uint8_t v___y_2547_; 
switch(v_zetaUnusedMode_2542_)
{
case 0:
{
v___y_2547_ = v___x_2543_;
goto v___jp_2546_;
}
case 1:
{
v___y_2547_ = v___x_2543_;
goto v___jp_2546_;
}
default: 
{
v___y_2547_ = v___x_2544_;
goto v___jp_2546_;
}
}
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_box(v___y_2547_);
v___x_2549_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2549_, 0, v_level_2539_);
lean_closure_set(v___x_2549_, 1, v_e_2540_);
lean_closure_set(v___x_2549_, 2, v_r_2545_);
lean_closure_set(v___x_2549_, 3, v___x_2548_);
v___x_2550_ = lean_apply_2(v_inst_2541_, lean_box(0), v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2551_, lean_object* v_e_2552_, lean_object* v_inst_2553_, lean_object* v_zetaUnusedMode_2554_, lean_object* v___x_2555_, lean_object* v___x_2556_, lean_object* v_r_2557_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2558_; uint8_t v___x_363__boxed_2559_; uint8_t v___x_364__boxed_2560_; lean_object* v_res_2561_; 
v_zetaUnusedMode_boxed_2558_ = lean_unbox(v_zetaUnusedMode_2554_);
v___x_363__boxed_2559_ = lean_unbox(v___x_2555_);
v___x_364__boxed_2560_ = lean_unbox(v___x_2556_);
v_res_2561_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2551_, v_e_2552_, v_inst_2553_, v_zetaUnusedMode_boxed_2558_, v___x_363__boxed_2559_, v___x_364__boxed_2560_, v_r_2557_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_info_2567_, lean_object* v_e_2568_, lean_object* v___x_2569_, lean_object* v_toBind_2570_, lean_object* v___f_2571_, lean_object* v_____x_2572_){
_start:
{
lean_object* v_fst_2573_; lean_object* v_snd_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_fst_2573_ = lean_ctor_get(v_____x_2572_, 0);
lean_inc(v_fst_2573_);
v_snd_2574_ = lean_ctor_get(v_____x_2572_, 1);
lean_inc(v_snd_2574_);
lean_dec_ref(v_____x_2572_);
v___x_2575_ = lean_mk_empty_array_with_capacity(v___x_2562_);
v___x_2576_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2563_, v_inst_2564_, v_inst_2565_, v_inst_2566_, v_info_2567_, v_fst_2573_, v_snd_2574_, v_e_2568_, v___x_2569_, v___x_2575_);
v___x_2577_ = lean_apply_4(v_toBind_2570_, lean_box(0), lean_box(0), v___x_2576_, v___f_2571_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_info_2583_, lean_object* v_e_2584_, lean_object* v___x_2585_, lean_object* v_toBind_2586_, lean_object* v___f_2587_, lean_object* v_____x_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2578_, v_inst_2579_, v_inst_2580_, v_inst_2581_, v_inst_2582_, v_info_2583_, v_e_2584_, v___x_2585_, v_toBind_2586_, v___f_2587_, v_____x_2588_);
lean_dec(v___x_2578_);
return v_res_2589_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2592_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2593_ = lean_unsigned_to_nat(2u);
v___x_2594_ = lean_unsigned_to_nat(456u);
v___x_2595_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2596_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2597_ = l_mkPanicMessageWithDecl(v___x_2596_, v___x_2595_, v___x_2594_, v___x_2593_, v___x_2592_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2598_, lean_object* v_inst_2599_, uint8_t v_zetaUnusedMode_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_toBind_2604_, lean_object* v_info_2605_){
_start:
{
lean_object* v_haveInfo_2606_; lean_object* v_level_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_haveInfo_2606_ = lean_ctor_get(v_info_2605_, 0);
v_level_2607_ = lean_ctor_get(v_info_2605_, 5);
v___x_2608_ = lean_array_get_size(v_haveInfo_2606_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_nat_dec_eq(v___x_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; uint8_t v___y_2618_; 
v___x_2611_ = 1;
v___x_2612_ = lean_box(v_zetaUnusedMode_2600_);
v___x_2613_ = lean_box(v___x_2611_);
v___x_2614_ = lean_box(v___x_2610_);
lean_inc(v_inst_2599_);
lean_inc_ref(v_e_2598_);
lean_inc(v_level_2607_);
v___f_2615_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2615_, 0, v_level_2607_);
lean_closure_set(v___f_2615_, 1, v_e_2598_);
lean_closure_set(v___f_2615_, 2, v_inst_2599_);
lean_closure_set(v___f_2615_, 3, v___x_2612_);
lean_closure_set(v___f_2615_, 4, v___x_2613_);
lean_closure_set(v___f_2615_, 5, v___x_2614_);
lean_inc(v_toBind_2604_);
lean_inc_ref(v_info_2605_);
lean_inc(v_inst_2599_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2616_, 0, v___x_2608_);
lean_closure_set(v___f_2616_, 1, v_inst_2601_);
lean_closure_set(v___f_2616_, 2, v_inst_2599_);
lean_closure_set(v___f_2616_, 3, v_inst_2602_);
lean_closure_set(v___f_2616_, 4, v_inst_2603_);
lean_closure_set(v___f_2616_, 5, v_info_2605_);
lean_closure_set(v___f_2616_, 6, v_e_2598_);
lean_closure_set(v___f_2616_, 7, v___x_2609_);
lean_closure_set(v___f_2616_, 8, v_toBind_2604_);
lean_closure_set(v___f_2616_, 9, v___f_2615_);
switch(v_zetaUnusedMode_2600_)
{
case 0:
{
v___y_2618_ = v___x_2611_;
goto v___jp_2617_;
}
case 2:
{
v___y_2618_ = v___x_2611_;
goto v___jp_2617_;
}
default: 
{
v___y_2618_ = v___x_2610_;
goto v___jp_2617_;
}
}
v___jp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2619_ = lean_box(v___y_2618_);
v___x_2620_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2620_, 0, v_info_2605_);
lean_closure_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_apply_2(v_inst_2599_, lean_box(0), v___x_2620_);
v___x_2622_ = lean_apply_4(v_toBind_2604_, lean_box(0), lean_box(0), v___x_2621_, v___f_2616_);
return v___x_2622_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_info_2605_);
lean_dec(v_toBind_2604_);
lean_dec_ref(v_inst_2603_);
lean_dec_ref(v_inst_2602_);
lean_dec(v_inst_2599_);
lean_dec_ref(v_e_2598_);
v___x_2623_ = lean_box(0);
v___x_2624_ = l_instInhabitedOfMonad___redArg(v_inst_2601_, v___x_2623_);
v___x_2625_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2626_ = l_panic___redArg(v___x_2624_, v___x_2625_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2627_, lean_object* v_inst_2628_, lean_object* v_zetaUnusedMode_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_toBind_2633_, lean_object* v_info_2634_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2635_; lean_object* v_res_2636_; 
v_zetaUnusedMode_boxed_2635_ = lean_unbox(v_zetaUnusedMode_2629_);
v_res_2636_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2627_, v_inst_2628_, v_zetaUnusedMode_boxed_2635_, v_inst_2630_, v_inst_2631_, v_inst_2632_, v_toBind_2633_, v_info_2634_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_e_2641_, uint8_t v_zetaUnusedMode_2642_){
_start:
{
lean_object* v_toBind_2643_; lean_object* v___x_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_toBind_2643_ = lean_ctor_get(v_inst_2637_, 1);
lean_inc(v_toBind_2643_);
v___x_2644_ = lean_box(v_zetaUnusedMode_2642_);
lean_inc(v_toBind_2643_);
lean_inc(v_inst_2638_);
lean_inc_ref(v_e_2641_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2645_, 0, v_e_2641_);
lean_closure_set(v___f_2645_, 1, v_inst_2638_);
lean_closure_set(v___f_2645_, 2, v___x_2644_);
lean_closure_set(v___f_2645_, 3, v_inst_2637_);
lean_closure_set(v___f_2645_, 4, v_inst_2639_);
lean_closure_set(v___f_2645_, 5, v_inst_2640_);
lean_closure_set(v___f_2645_, 6, v_toBind_2643_);
v___x_2646_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2646_, 0, v_e_2641_);
v___x_2647_ = lean_apply_2(v_inst_2638_, lean_box(0), v___x_2646_);
v___x_2648_ = lean_apply_4(v_toBind_2643_, lean_box(0), lean_box(0), v___x_2647_, v___f_2645_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_e_2653_, lean_object* v_zetaUnusedMode_2654_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2655_; lean_object* v_res_2656_; 
v_zetaUnusedMode_boxed_2655_ = lean_unbox(v_zetaUnusedMode_2654_);
v_res_2656_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2649_, v_inst_2650_, v_inst_2651_, v_inst_2652_, v_e_2653_, v_zetaUnusedMode_boxed_2655_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_e_2662_, uint8_t v_zetaUnusedMode_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2658_, v_inst_2659_, v_inst_2660_, v_inst_2661_, v_e_2662_, v_zetaUnusedMode_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_e_2670_, lean_object* v_zetaUnusedMode_2671_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2672_; lean_object* v_res_2673_; 
v_zetaUnusedMode_boxed_2672_ = lean_unbox(v_zetaUnusedMode_2671_);
v_res_2673_ = l_Lean_Meta_simpHaveTelescope(v_m_2665_, v_inst_2666_, v_inst_2667_, v_inst_2668_, v_inst_2669_, v_e_2670_, v_zetaUnusedMode_boxed_2672_);
return v_res_2673_;
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
