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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectLooseBVars(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withExistingLocalDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "have telescope; simplifying body "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(224, 171, 76, 175, 220, 234, 86, 123)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(203, 102, 186, 241, 230, 68, 112, 189)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(231, 39, 204, 185, 148, 242, 27, 8)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "have telescope; non-fixed "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3_value),LEAN_SCALAR_PTR_LITERAL(66, 96, 215, 110, 82, 218, 253, 207)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "_simp_let_unused_dummy"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 140, 102, 13, 80, 16, 156, 102)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__2));
v___x_22_ = l_Lean_Level_param___override(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__4);
v___x_24_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__3);
v___x_25_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_26_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_27_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_25_);
lean_ctor_set(v___x_27_, 2, v___x_25_);
lean_ctor_set(v___x_27_, 3, v___x_24_);
lean_ctor_set(v___x_27_, 4, v___x_24_);
lean_ctor_set(v___x_27_, 5, v___x_23_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_instInhabitedHaveTelescopeInfo_default;
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(lean_object* v_lctx_30_, lean_object* v_x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_keyedConfig_37_; uint8_t v_trackZetaDelta_38_; lean_object* v_zetaDeltaSet_39_; lean_object* v_localInstances_40_; lean_object* v_defEqCtx_x3f_41_; lean_object* v_synthPendingDepth_42_; lean_object* v_customCanUnfoldPredicate_x3f_43_; uint8_t v_univApprox_44_; uint8_t v_inTypeClassResolution_45_; uint8_t v_cacheInferType_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_keyedConfig_37_ = lean_ctor_get(v___y_32_, 0);
v_trackZetaDelta_38_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7);
v_zetaDeltaSet_39_ = lean_ctor_get(v___y_32_, 1);
v_localInstances_40_ = lean_ctor_get(v___y_32_, 3);
v_defEqCtx_x3f_41_ = lean_ctor_get(v___y_32_, 4);
v_synthPendingDepth_42_ = lean_ctor_get(v___y_32_, 5);
v_customCanUnfoldPredicate_x3f_43_ = lean_ctor_get(v___y_32_, 6);
v_univApprox_44_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_45_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7 + 2);
v_cacheInferType_46_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_43_);
lean_inc(v_synthPendingDepth_42_);
lean_inc(v_defEqCtx_x3f_41_);
lean_inc_ref(v_localInstances_40_);
lean_inc(v_zetaDeltaSet_39_);
lean_inc_ref(v_keyedConfig_37_);
v___x_47_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_47_, 0, v_keyedConfig_37_);
lean_ctor_set(v___x_47_, 1, v_zetaDeltaSet_39_);
lean_ctor_set(v___x_47_, 2, v_lctx_30_);
lean_ctor_set(v___x_47_, 3, v_localInstances_40_);
lean_ctor_set(v___x_47_, 4, v_defEqCtx_x3f_41_);
lean_ctor_set(v___x_47_, 5, v_synthPendingDepth_42_);
lean_ctor_set(v___x_47_, 6, v_customCanUnfoldPredicate_x3f_43_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*7, v_trackZetaDelta_38_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*7 + 1, v_univApprox_44_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*7 + 2, v_inTypeClassResolution_45_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*7 + 3, v_cacheInferType_46_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
v___x_48_ = lean_apply_5(v_x_31_, v___x_47_, v___y_33_, v___y_34_, v___y_35_, lean_box(0));
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object* v_lctx_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object* v_00_u03b1_57_, lean_object* v_lctx_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_58_, v_x_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___boxed(lean_object* v_00_u03b1_66_, lean_object* v_lctx_67_, lean_object* v_x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(v_00_u03b1_66_, v_lctx_67_, v_x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
return v_x_75_;
}
else
{
lean_object* v_key_77_; lean_object* v_value_78_; lean_object* v_tail_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_102_; 
v_key_77_ = lean_ctor_get(v_x_76_, 0);
v_value_78_ = lean_ctor_get(v_x_76_, 1);
v_tail_79_ = lean_ctor_get(v_x_76_, 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_102_ == 0)
{
v___x_81_ = v_x_76_;
v_isShared_82_ = v_isSharedCheck_102_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_tail_79_);
lean_inc(v_value_78_);
lean_inc(v_key_77_);
lean_dec(v_x_76_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_102_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v_fold_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_83_ = lean_array_get_size(v_x_75_);
v___x_84_ = lean_uint64_of_nat(v_key_77_);
v___x_85_ = 32ULL;
v___x_86_ = lean_uint64_shift_right(v___x_84_, v___x_85_);
v_fold_87_ = lean_uint64_xor(v___x_84_, v___x_86_);
v___x_88_ = 16ULL;
v___x_89_ = lean_uint64_shift_right(v_fold_87_, v___x_88_);
v___x_90_ = lean_uint64_xor(v_fold_87_, v___x_89_);
v___x_91_ = lean_uint64_to_usize(v___x_90_);
v___x_92_ = lean_usize_of_nat(v___x_83_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_sub(v___x_92_, v___x_93_);
v___x_95_ = lean_usize_land(v___x_91_, v___x_94_);
v___x_96_ = lean_array_uget_borrowed(v_x_75_, v___x_95_);
lean_inc(v___x_96_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 2, v___x_96_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_key_77_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_value_78_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v___x_96_);
v___x_98_ = v_reuseFailAlloc_101_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_array_uset(v_x_75_, v___x_95_, v___x_98_);
v_x_75_ = v___x_99_;
v_x_76_ = v_tail_79_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(lean_object* v_i_103_, lean_object* v_source_104_, lean_object* v_target_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_array_get_size(v_source_104_);
v___x_107_ = lean_nat_dec_lt(v_i_103_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_source_104_);
lean_dec(v_i_103_);
return v_target_105_;
}
else
{
lean_object* v_es_108_; lean_object* v___x_109_; lean_object* v_source_110_; lean_object* v_target_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_es_108_ = lean_array_fget(v_source_104_, v_i_103_);
v___x_109_ = lean_box(0);
v_source_110_ = lean_array_fset(v_source_104_, v_i_103_, v___x_109_);
v_target_111_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_target_105_, v_es_108_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_i_103_, v___x_112_);
lean_dec(v_i_103_);
v_i_103_ = v___x_113_;
v_source_104_ = v_source_110_;
v_target_105_ = v_target_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(lean_object* v_data_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_nbuckets_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_116_ = lean_array_get_size(v_data_115_);
v___x_117_ = lean_unsigned_to_nat(2u);
v_nbuckets_118_ = lean_nat_mul(v___x_116_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_box(0);
v___x_121_ = lean_mk_array(v_nbuckets_118_, v___x_120_);
v___x_122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v___x_119_, v_data_115_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object* v_a_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
else
{
lean_object* v_key_126_; lean_object* v_tail_127_; uint8_t v___x_128_; 
v_key_126_ = lean_ctor_get(v_x_124_, 0);
v_tail_127_ = lean_ctor_get(v_x_124_, 2);
v___x_128_ = lean_nat_dec_eq(v_key_126_, v_a_123_);
if (v___x_128_ == 0)
{
v_x_124_ = v_tail_127_;
goto _start;
}
else
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object* v_a_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_130_, v_x_131_);
lean_dec(v_x_131_);
lean_dec(v_a_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object* v_m_134_, lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
lean_object* v_size_137_; lean_object* v_buckets_138_; lean_object* v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v_fold_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; lean_object* v_bkt_152_; uint8_t v___x_153_; 
v_size_137_ = lean_ctor_get(v_m_134_, 0);
v_buckets_138_ = lean_ctor_get(v_m_134_, 1);
v___x_139_ = lean_array_get_size(v_buckets_138_);
v___x_140_ = lean_uint64_of_nat(v_a_135_);
v___x_141_ = 32ULL;
v___x_142_ = lean_uint64_shift_right(v___x_140_, v___x_141_);
v_fold_143_ = lean_uint64_xor(v___x_140_, v___x_142_);
v___x_144_ = 16ULL;
v___x_145_ = lean_uint64_shift_right(v_fold_143_, v___x_144_);
v___x_146_ = lean_uint64_xor(v_fold_143_, v___x_145_);
v___x_147_ = lean_uint64_to_usize(v___x_146_);
v___x_148_ = lean_usize_of_nat(v___x_139_);
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_sub(v___x_148_, v___x_149_);
v___x_151_ = lean_usize_land(v___x_147_, v___x_150_);
v_bkt_152_ = lean_array_uget_borrowed(v_buckets_138_, v___x_151_);
v___x_153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_135_, v_bkt_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_174_; 
lean_inc_ref(v_buckets_138_);
lean_inc(v_size_137_);
v_isSharedCheck_174_ = !lean_is_exclusive(v_m_134_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; lean_object* v_unused_176_; 
v_unused_175_ = lean_ctor_get(v_m_134_, 1);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_m_134_, 0);
lean_dec(v_unused_176_);
v___x_155_ = v_m_134_;
v_isShared_156_ = v_isSharedCheck_174_;
goto v_resetjp_154_;
}
else
{
lean_dec(v_m_134_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_174_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v_size_x27_158_; lean_object* v___x_159_; lean_object* v_buckets_x27_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v_size_x27_158_ = lean_nat_add(v_size_137_, v___x_157_);
lean_dec(v_size_137_);
lean_inc(v_bkt_152_);
v___x_159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_159_, 0, v_a_135_);
lean_ctor_set(v___x_159_, 1, v_b_136_);
lean_ctor_set(v___x_159_, 2, v_bkt_152_);
v_buckets_x27_160_ = lean_array_uset(v_buckets_138_, v___x_151_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_mul(v_size_x27_158_, v___x_161_);
v___x_163_ = lean_unsigned_to_nat(3u);
v___x_164_ = lean_nat_div(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_array_get_size(v_buckets_x27_160_);
v___x_166_ = lean_nat_dec_le(v___x_164_, v___x_165_);
lean_dec(v___x_164_);
if (v___x_166_ == 0)
{
lean_object* v_val_167_; lean_object* v___x_169_; 
v_val_167_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_buckets_x27_160_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v_val_167_);
lean_ctor_set(v___x_155_, 0, v_size_x27_158_);
v___x_169_ = v___x_155_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_x27_158_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_val_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
else
{
lean_object* v___x_172_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v_buckets_x27_160_);
lean_ctor_set(v___x_155_, 0, v_size_x27_158_);
v___x_172_ = v___x_155_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_size_x27_158_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_buckets_x27_160_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_dec(v_b_136_);
lean_dec(v_a_135_);
return v_m_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object* v_numHaves_177_, lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
return v_x_178_;
}
else
{
lean_object* v_key_180_; lean_object* v_tail_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_key_180_ = lean_ctor_get(v_x_179_, 0);
v_tail_181_ = lean_ctor_get(v_x_179_, 2);
v___x_182_ = lean_nat_sub(v_numHaves_177_, v_key_180_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v___x_182_, v___x_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_x_178_, v___x_184_, v___x_185_);
v_x_178_ = v___x_186_;
v_x_179_ = v_tail_181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object* v_numHaves_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_188_, v_x_189_, v_x_190_);
lean_dec(v_x_190_);
lean_dec(v_numHaves_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object* v_numHaves_192_, lean_object* v_as_193_, size_t v_i_194_, size_t v_stop_195_, lean_object* v_b_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_194_, v_stop_195_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; size_t v___x_200_; size_t v___x_201_; 
v___x_198_ = lean_array_uget_borrowed(v_as_193_, v_i_194_);
v___x_199_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_192_, v_b_196_, v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_add(v_i_194_, v___x_200_);
v_i_194_ = v___x_201_;
v_b_196_ = v___x_199_;
goto _start;
}
else
{
return v_b_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object* v_numHaves_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_, lean_object* v_b_207_){
_start:
{
size_t v_i_boxed_208_; size_t v_stop_boxed_209_; lean_object* v_res_210_; 
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_203_, v_as_204_, v_i_boxed_208_, v_stop_boxed_209_, v_b_207_);
lean_dec_ref(v_as_204_);
lean_dec(v_numHaves_203_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(lean_object* v_numHaves_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_buckets_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_215_ = l_Lean_Expr_collectLooseBVars(v_a_212_, v___x_213_);
v_buckets_216_ = lean_ctor_get(v___x_215_, 1);
lean_inc_ref(v_buckets_216_);
lean_dec_ref(v___x_215_);
v___x_217_ = lean_array_get_size(v_buckets_216_);
v___x_218_ = lean_nat_dec_lt(v___x_213_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v_buckets_216_);
return v___x_214_;
}
else
{
size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((size_t)0ULL);
v___x_220_ = lean_usize_of_nat(v___x_217_);
v___x_221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_211_, v_buckets_216_, v___x_219_, v___x_220_, v___x_214_);
lean_dec_ref(v_buckets_216_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_222_, v_a_223_);
lean_dec(v_numHaves_222_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_225_, lean_object* v_t_226_){
_start:
{
if (lean_obj_tag(v_t_226_) == 0)
{
lean_object* v_k_227_; lean_object* v_l_228_; lean_object* v_r_229_; uint8_t v___x_230_; 
v_k_227_ = lean_ctor_get(v_t_226_, 1);
v_l_228_ = lean_ctor_get(v_t_226_, 3);
v_r_229_ = lean_ctor_get(v_t_226_, 4);
v___x_230_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_225_, v_k_227_);
switch(v___x_230_)
{
case 0:
{
v_t_226_ = v_l_228_;
goto _start;
}
case 1:
{
uint8_t v___x_232_; 
v___x_232_ = 1;
return v___x_232_;
}
default: 
{
v_t_226_ = v_r_229_;
goto _start;
}
}
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_235_, lean_object* v_t_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_235_, v_t_236_);
lean_dec(v_t_236_);
lean_dec(v_k_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_239_, lean_object* v___x_240_, lean_object* v_n_241_, lean_object* v_j_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_zero_244_; uint8_t v_isZero_245_; 
v_zero_244_ = lean_unsigned_to_nat(0u);
v_isZero_245_ = lean_nat_dec_eq(v_j_242_, v_zero_244_);
if (v_isZero_245_ == 1)
{
lean_dec(v_j_242_);
return v_a_243_;
}
else
{
lean_object* v_one_246_; lean_object* v_n_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_one_246_ = lean_unsigned_to_nat(1u);
v_n_247_ = lean_nat_sub(v_j_242_, v_one_246_);
v___x_248_ = lean_nat_sub(v_n_241_, v_j_242_);
lean_dec(v_j_242_);
v___x_249_ = lean_array_fget_borrowed(v_fvars_239_, v___x_248_);
v___x_250_ = l_Lean_Expr_fvarId_x21(v___x_249_);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_250_, v___x_240_);
lean_dec(v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v___x_248_);
v_j_242_ = v_n_247_;
goto _start;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_box(0);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_243_, v___x_248_, v___x_253_);
v_j_242_ = v_n_247_;
v_a_243_ = v___x_254_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_256_, lean_object* v___x_257_, lean_object* v_n_258_, lean_object* v_j_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_256_, v___x_257_, v_n_258_, v_j_259_, v_a_260_);
lean_dec(v_n_258_);
lean_dec(v___x_257_);
lean_dec_ref(v_fvars_256_);
return v_res_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
v___x_263_ = lean_unsigned_to_nat(16u);
v___x_264_ = lean_mk_array(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_270_, lean_object* v___x_271_, lean_object* v_fvars_272_, lean_object* v_info_273_, lean_object* v_bodyDeps_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc_ref(v___y_275_);
lean_inc_ref(v_body_270_);
v___x_280_ = lean_infer_type(v_body_270_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_n(v_a_281_, 2);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_Lean_Meta_getLevel(v_a_281_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_310_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_310_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_310_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_310_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_fvarSet_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_haveInfo_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v___x_287_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_271_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
lean_inc(v_a_281_);
v___x_290_ = l_Lean_collectFVars(v___x_289_, v_a_281_);
v_fvarSet_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_fvarSet_291_);
lean_dec_ref(v___x_290_);
v___x_292_ = lean_array_get_size(v_fvars_272_);
v___x_293_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_272_, v_fvarSet_291_, v___x_292_, v___x_292_, v___x_287_);
lean_dec(v_fvarSet_291_);
v_haveInfo_294_ = lean_ctor_get(v_info_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_info_273_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; lean_object* v_unused_309_; 
v_unused_305_ = lean_ctor_get(v_info_273_, 5);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_info_273_, 4);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_info_273_, 3);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_info_273_, 2);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_info_273_, 1);
lean_dec(v_unused_309_);
v___x_296_ = v_info_273_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_haveInfo_294_);
lean_dec(v_info_273_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 5, v_a_283_);
lean_ctor_set(v___x_296_, 4, v_a_281_);
lean_ctor_set(v___x_296_, 3, v_body_270_);
lean_ctor_set(v___x_296_, 2, v___x_293_);
lean_ctor_set(v___x_296_, 1, v_bodyDeps_274_);
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_haveInfo_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_bodyDeps_274_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_body_270_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_a_281_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_a_283_);
v___x_299_ = v_reuseFailAlloc_303_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_299_);
v___x_301_ = v___x_285_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_a_281_);
lean_dec_ref(v_bodyDeps_274_);
lean_dec_ref(v_info_273_);
lean_dec(v___x_271_);
lean_dec_ref(v_body_270_);
v_a_311_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_282_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_282_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec_ref(v_bodyDeps_274_);
lean_dec_ref(v_info_273_);
lean_dec(v___x_271_);
lean_dec_ref(v_body_270_);
v_a_319_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_280_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_280_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_327_, lean_object* v___x_328_, lean_object* v_fvars_329_, lean_object* v_info_330_, lean_object* v_bodyDeps_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_327_, v___x_328_, v_fvars_329_, v_info_330_, v_bodyDeps_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec_ref(v_fvars_329_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v_ngen_341_; lean_object* v_namePrefix_342_; lean_object* v_idx_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_372_; 
v___x_340_ = lean_st_ref_get(v___y_338_);
v_ngen_341_ = lean_ctor_get(v___x_340_, 2);
lean_inc_ref(v_ngen_341_);
lean_dec(v___x_340_);
v_namePrefix_342_ = lean_ctor_get(v_ngen_341_, 0);
v_idx_343_ = lean_ctor_get(v_ngen_341_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_ngen_341_);
if (v_isSharedCheck_372_ == 0)
{
v___x_345_ = v_ngen_341_;
v_isShared_346_ = v_isSharedCheck_372_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_idx_343_);
lean_inc(v_namePrefix_342_);
lean_dec(v_ngen_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_372_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_auxDeclNGen_350_; lean_object* v_traceState_351_; lean_object* v_cache_352_; lean_object* v_messages_353_; lean_object* v_infoState_354_; lean_object* v_snapshotTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_370_; 
v___x_347_ = lean_st_ref_take(v___y_338_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_347_, 1);
v_auxDeclNGen_350_ = lean_ctor_get(v___x_347_, 3);
v_traceState_351_ = lean_ctor_get(v___x_347_, 4);
v_cache_352_ = lean_ctor_get(v___x_347_, 5);
v_messages_353_ = lean_ctor_get(v___x_347_, 6);
v_infoState_354_ = lean_ctor_get(v___x_347_, 7);
v_snapshotTasks_355_ = lean_ctor_get(v___x_347_, 8);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_347_, 2);
lean_dec(v_unused_371_);
v___x_357_ = v___x_347_;
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snapshotTasks_355_);
lean_inc(v_infoState_354_);
lean_inc(v_messages_353_);
lean_inc(v_cache_352_);
lean_inc(v_traceState_351_);
lean_inc(v_auxDeclNGen_350_);
lean_inc(v_nextMacroScope_349_);
lean_inc(v_env_348_);
lean_dec(v___x_347_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_r_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
lean_inc(v_idx_343_);
lean_inc(v_namePrefix_342_);
v_r_359_ = l_Lean_Name_num___override(v_namePrefix_342_, v_idx_343_);
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_idx_343_, v___x_360_);
lean_dec(v_idx_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_361_);
v___x_363_ = v___x_345_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_namePrefix_342_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_361_);
v___x_363_ = v_reuseFailAlloc_369_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 2, v___x_363_);
v___x_365_ = v___x_357_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_env_348_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_auxDeclNGen_350_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_traceState_351_);
lean_ctor_set(v_reuseFailAlloc_368_, 5, v_cache_352_);
lean_ctor_set(v_reuseFailAlloc_368_, 6, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 7, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_368_, 8, v_snapshotTasks_355_);
v___x_365_ = v_reuseFailAlloc_368_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_st_ref_put(v___y_338_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_r_359_);
return v___x_367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_373_);
lean_dec(v___y_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v___x_381_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_379_);
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_396_, lean_object* v_numHaves_397_, lean_object* v_info_398_, lean_object* v_lctx_399_, lean_object* v_fvars_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; 
v___x_406_ = lean_box(1);
if (lean_obj_tag(v_e_396_) == 8)
{
uint8_t v_nondep_416_; 
v_nondep_416_ = lean_ctor_get_uint8(v_e_396_, sizeof(void*)*4 + 8);
if (v_nondep_416_ == 1)
{
lean_object* v_declName_417_; lean_object* v_type_418_; lean_object* v_value_419_; lean_object* v_body_420_; lean_object* v_t_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_declName_417_ = lean_ctor_get(v_e_396_, 0);
lean_inc(v_declName_417_);
v_type_418_ = lean_ctor_get(v_e_396_, 1);
lean_inc_ref(v_type_418_);
v_value_419_ = lean_ctor_get(v_e_396_, 2);
lean_inc_ref(v_value_419_);
v_body_420_ = lean_ctor_get(v_e_396_, 3);
lean_inc_ref(v_body_420_);
lean_dec_ref_known(v_e_396_, 4);
v_t_421_ = lean_expr_instantiate_rev(v_type_418_, v_fvars_400_);
lean_inc_ref(v_t_421_);
v___x_422_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_422_, 0, v_t_421_);
lean_inc_ref(v_lctx_399_);
v___x_423_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_399_, v___x_422_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v_haveInfo_427_; lean_object* v_bodyDeps_428_; lean_object* v_bodyTypeDeps_429_; lean_object* v_body_430_; lean_object* v_bodyType_431_; lean_object* v_level_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_453_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v_haveInfo_427_ = lean_ctor_get(v_info_398_, 0);
v_bodyDeps_428_ = lean_ctor_get(v_info_398_, 1);
v_bodyTypeDeps_429_ = lean_ctor_get(v_info_398_, 2);
v_body_430_ = lean_ctor_get(v_info_398_, 3);
v_bodyType_431_ = lean_ctor_get(v_info_398_, 4);
v_level_432_ = lean_ctor_get(v_info_398_, 5);
v_isSharedCheck_453_ = !lean_is_exclusive(v_info_398_);
if (v_isSharedCheck_453_ == 0)
{
v___x_434_ = v_info_398_;
v_isShared_435_ = v_isSharedCheck_453_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_level_432_);
lean_inc(v_bodyType_431_);
lean_inc(v_body_430_);
lean_inc(v_bodyTypeDeps_429_);
lean_inc(v_bodyDeps_428_);
lean_inc(v_haveInfo_427_);
lean_dec(v_info_398_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_453_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_typeBackDeps_436_; lean_object* v_valueBackDeps_437_; lean_object* v_v_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v_typeBackDeps_436_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_397_, v_type_418_);
lean_inc_ref(v_value_419_);
v_valueBackDeps_437_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_397_, v_value_419_);
v_v_438_ = lean_expr_instantiate_rev(v_value_419_, v_fvars_400_);
lean_dec_ref(v_value_419_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = 0;
lean_inc(v_a_426_);
v___x_441_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v_a_426_);
lean_ctor_set(v___x_441_, 2, v_declName_417_);
lean_ctor_set(v___x_441_, 3, v_t_421_);
lean_ctor_set(v___x_441_, 4, v_v_438_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*5, v_nondep_416_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*5 + 1, v___x_440_);
lean_inc_ref(v___x_441_);
v___x_442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_442_, 0, v_typeBackDeps_436_);
lean_ctor_set(v___x_442_, 1, v_valueBackDeps_437_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_ctor_set(v___x_442_, 3, v_a_424_);
v___x_443_ = lean_array_push(v_haveInfo_427_, v___x_442_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_443_);
v___x_445_ = v___x_434_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_bodyDeps_428_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_bodyTypeDeps_429_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_body_430_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_bodyType_431_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_level_432_);
v___x_445_ = v_reuseFailAlloc_452_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_446_ = l_Lean_LocalContext_addDecl(v_lctx_399_, v___x_441_);
v___x_447_ = l_Lean_mkFVar(v_a_426_);
v___x_448_ = lean_array_push(v_fvars_400_, v___x_447_);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_numHaves_397_, v___x_449_);
lean_dec(v_numHaves_397_);
v_e_396_ = v_body_420_;
v_numHaves_397_ = v___x_450_;
v_info_398_ = v___x_445_;
v_lctx_399_ = v___x_446_;
v_fvars_400_ = v___x_448_;
goto _start;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_a_424_);
lean_dec_ref(v_t_421_);
lean_dec_ref(v_body_420_);
lean_dec_ref(v_value_419_);
lean_dec_ref(v_type_418_);
lean_dec(v_declName_417_);
lean_dec_ref(v_fvars_400_);
lean_dec_ref(v_lctx_399_);
lean_dec_ref(v_info_398_);
lean_dec(v_numHaves_397_);
v_a_454_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_425_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_425_);
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
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v_t_421_);
lean_dec_ref(v_body_420_);
lean_dec_ref(v_value_419_);
lean_dec_ref(v_type_418_);
lean_dec(v_declName_417_);
lean_dec_ref(v_fvars_400_);
lean_dec_ref(v_lctx_399_);
lean_dec_ref(v_info_398_);
lean_dec(v_numHaves_397_);
v_a_462_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_423_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_423_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
v___y_408_ = v_a_401_;
v___y_409_ = v_a_402_;
v___y_410_ = v_a_403_;
v___y_411_ = v_a_404_;
goto v___jp_407_;
}
}
else
{
v___y_408_ = v_a_401_;
v___y_409_ = v_a_402_;
v___y_410_ = v_a_403_;
v___y_411_ = v_a_404_;
goto v___jp_407_;
}
v___jp_407_:
{
lean_object* v_bodyDeps_412_; lean_object* v_body_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
lean_inc_ref(v_e_396_);
v_bodyDeps_412_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_397_, v_e_396_);
lean_dec(v_numHaves_397_);
v_body_413_ = lean_expr_instantiate_rev(v_e_396_, v_fvars_400_);
lean_dec_ref(v_e_396_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_414_, 0, v_body_413_);
lean_closure_set(v___f_414_, 1, v___x_406_);
lean_closure_set(v___f_414_, 2, v_fvars_400_);
lean_closure_set(v___f_414_, 3, v_info_398_);
lean_closure_set(v___f_414_, 4, v_bodyDeps_412_);
v___x_415_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_399_, v___f_414_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_470_, lean_object* v_numHaves_471_, lean_object* v_info_472_, lean_object* v_lctx_473_, lean_object* v_fvars_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_470_, v_numHaves_471_, v_info_472_, v_lctx_473_, v_fvars_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_481_, lean_object* v_m_482_, lean_object* v_a_483_, lean_object* v_b_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_482_, v_a_483_, v_b_484_);
return v___x_485_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_486_, lean_object* v_k_487_, lean_object* v_t_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_487_, v_t_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_490_, lean_object* v_k_491_, lean_object* v_t_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_490_, v_k_491_, v_t_492_);
lean_dec(v_t_492_);
lean_dec(v_k_491_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_495_, lean_object* v___x_496_, lean_object* v_n_497_, lean_object* v_j_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_495_, v___x_496_, v_n_497_, v_j_498_, v_a_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_502_, lean_object* v___x_503_, lean_object* v_n_504_, lean_object* v_j_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_502_, v___x_503_, v_n_504_, v_j_505_, v_a_506_, v_a_507_);
lean_dec(v_n_504_);
lean_dec(v___x_503_);
lean_dec_ref(v_fvars_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_520_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v_res_528_; lean_object* v_r_529_; 
v_res_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_525_, v_a_526_, v_x_527_);
lean_dec(v_x_527_);
lean_dec(v_a_526_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_530_, lean_object* v_data_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_533_, lean_object* v_i_534_, lean_object* v_source_535_, lean_object* v_target_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_534_, v_source_535_, v_target_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_lctx_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_lctx_548_ = lean_ctor_get(v_a_543_, 2);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_551_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_548_);
v___x_552_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_542_, v___x_549_, v___x_551_, v_lctx_548_, v___x_550_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
return v_x_560_;
}
else
{
lean_object* v_key_562_; lean_object* v_tail_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_key_562_ = lean_ctor_get(v_x_561_, 0);
v_tail_563_ = lean_ctor_get(v_x_561_, 2);
v___x_564_ = 1;
v___x_565_ = lean_box(v___x_564_);
v___x_566_ = lean_array_set(v_x_560_, v_key_562_, v___x_565_);
v_x_560_ = v___x_566_;
v_x_561_ = v_tail_563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_568_, v_x_569_);
lean_dec(v_x_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_571_, size_t v_i_572_, size_t v_stop_573_, lean_object* v_b_574_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_eq(v_i_572_, v_stop_573_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; 
v___x_576_ = lean_array_uget_borrowed(v_as_571_, v_i_572_);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_574_, v___x_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_572_, v___x_578_);
v_i_572_ = v___x_579_;
v_b_574_ = v___x_577_;
goto _start;
}
else
{
return v_b_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_, lean_object* v_b_584_){
_start:
{
size_t v_i_boxed_585_; size_t v_stop_boxed_586_; lean_object* v_res_587_; 
v_i_boxed_585_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_586_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_581_, v_i_boxed_585_, v_stop_boxed_586_, v_b_584_);
lean_dec_ref(v_as_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_588_, lean_object* v_s_589_){
_start:
{
lean_object* v_buckets_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_buckets_590_ = lean_ctor_get(v_s_589_, 1);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v_buckets_590_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
return v_arr_588_;
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_592_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_590_, v___x_594_, v___x_595_, v_arr_588_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_597_, lean_object* v_s_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_597_, v_s_598_);
lean_dec_ref(v_s_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_600_, lean_object* v_numHaves_601_, lean_object* v___x_602_, lean_object* v_a_603_, lean_object* v_b_604_){
_start:
{
lean_object* v_a_607_; uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_lt(v_a_603_, v_upperBound_600_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v_a_603_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_b_604_);
return v___x_612_;
}
else
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_613_ = 0;
v___x_614_ = lean_nat_sub(v_numHaves_601_, v_a_603_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_sub(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(v___x_613_);
v___x_618_ = lean_array_get(v___x_617_, v_b_604_, v___x_616_);
lean_dec(v___x_617_);
v___x_619_ = lean_unbox(v___x_618_);
lean_dec(v___x_618_);
if (v___x_619_ == 0)
{
lean_dec(v___x_616_);
v_a_607_ = v_b_604_;
goto v___jp_606_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_typeBackDeps_622_; lean_object* v_valueBackDeps_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_621_ = lean_array_get_borrowed(v___x_620_, v___x_602_, v___x_616_);
lean_dec(v___x_616_);
v_typeBackDeps_622_ = lean_ctor_get(v___x_621_, 0);
v_valueBackDeps_623_ = lean_ctor_get(v___x_621_, 1);
v___x_624_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_604_, v_typeBackDeps_622_);
v___x_625_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_624_, v_valueBackDeps_623_);
v_a_607_ = v___x_625_;
goto v___jp_606_;
}
}
v___jp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_a_603_, v___x_608_);
lean_dec(v_a_603_);
v_a_603_ = v___x_609_;
v_b_604_ = v_a_607_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_626_, lean_object* v_numHaves_627_, lean_object* v___x_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_626_, v_numHaves_627_, v___x_628_, v_a_629_, v_b_630_);
lean_dec_ref(v___x_628_);
lean_dec(v_numHaves_627_);
lean_dec(v_upperBound_626_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_633_, lean_object* v_init_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_haveInfo_640_; lean_object* v_numHaves_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v_used_644_; lean_object* v___x_645_; lean_object* v_used_646_; lean_object* v___x_647_; 
v_haveInfo_640_ = lean_ctor_get(v_info_633_, 0);
v_numHaves_641_ = lean_array_get_size(v_haveInfo_640_);
v___x_642_ = 0;
v___x_643_ = lean_box(v___x_642_);
v_used_644_ = lean_mk_array(v_numHaves_641_, v___x_643_);
v___x_645_ = lean_unsigned_to_nat(0u);
v_used_646_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_644_, v_init_634_);
v___x_647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_641_, v_numHaves_641_, v_haveInfo_640_, v___x_645_, v_used_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_648_, lean_object* v_init_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_648_, v_init_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec_ref(v_init_649_);
lean_dec_ref(v_info_648_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_656_, lean_object* v_numHaves_657_, lean_object* v___x_658_, lean_object* v_inst_659_, lean_object* v_R_660_, lean_object* v_a_661_, lean_object* v_b_662_, lean_object* v_c_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_656_, v_numHaves_657_, v___x_658_, v_a_661_, v_b_662_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_670_, lean_object* v_numHaves_671_, lean_object* v___x_672_, lean_object* v_inst_673_, lean_object* v_R_674_, lean_object* v_a_675_, lean_object* v_b_676_, lean_object* v_c_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_670_, v_numHaves_671_, v___x_672_, v_inst_673_, v_R_674_, v_a_675_, v_b_676_, v_c_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v___x_672_);
lean_dec(v_numHaves_671_);
lean_dec(v_upperBound_670_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_686_, uint8_t v_keepUnused_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_bodyDeps_693_; lean_object* v_bodyTypeDeps_694_; lean_object* v___x_695_; 
v_bodyDeps_693_ = lean_ctor_get(v_info_686_, 1);
v_bodyTypeDeps_694_ = lean_ctor_get(v_info_686_, 2);
v___x_695_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_686_, v_bodyTypeDeps_694_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_695_) == 0)
{
if (v_keepUnused_687_ == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_686_, v_bodyDeps_693_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_706_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_706_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_a_696_);
lean_ctor_set(v___x_702_, 1, v_a_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_a_696_);
v_a_707_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_697_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_697_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_724_; 
v_a_715_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_724_ == 0)
{
v___x_717_ = v___x_695_;
v_isShared_718_ = v_isSharedCheck_724_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_695_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_724_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_719_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_a_715_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_720_);
v___x_722_ = v___x_717_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_695_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_695_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_733_, lean_object* v_keepUnused_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
uint8_t v_keepUnused_boxed_740_; lean_object* v_res_741_; 
v_keepUnused_boxed_740_ = lean_unbox(v_keepUnused_734_);
v_res_741_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_733_, v_keepUnused_boxed_740_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec_ref(v_info_733_);
return v_res_741_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_747_ = l_Lean_Expr_const___override(v___x_746_, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = 0;
v___x_749_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_750_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
lean_ctor_set(v___x_750_, 3, v___x_749_);
lean_ctor_set(v___x_750_, 4, v___x_749_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*5, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_751_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_level_769_, lean_object* v_exprType_770_, lean_object* v_e_771_, uint8_t v___x_772_, lean_object* v_toPure_773_, lean_object* v_xs_774_, lean_object* v_____do__lift_775_){
_start:
{
if (lean_obj_tag(v_____do__lift_775_) == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_proof_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v_level_769_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_mkConst(v___x_776_, v___x_778_);
lean_inc_ref_n(v_e_771_, 3);
lean_inc_ref(v_exprType_770_);
v_proof_780_ = l_Lean_mkAppB(v___x_779_, v_exprType_770_, v_e_771_);
v___x_781_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_781_, 0, v_e_771_);
lean_ctor_set(v___x_781_, 1, v_exprType_770_);
lean_ctor_set(v___x_781_, 2, v_e_771_);
lean_ctor_set(v___x_781_, 3, v_e_771_);
lean_ctor_set(v___x_781_, 4, v_proof_780_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*5, v___x_772_);
v___x_782_ = lean_apply_2(v_toPure_773_, lean_box(0), v___x_781_);
return v___x_782_;
}
else
{
lean_object* v_e_783_; lean_object* v_h_784_; lean_object* v_expr_785_; lean_object* v_proof_786_; lean_object* v___x_791_; uint8_t v___x_792_; 
lean_dec(v_level_769_);
v_e_783_ = lean_ctor_get(v_____do__lift_775_, 0);
v_h_784_ = lean_ctor_get(v_____do__lift_775_, 1);
v_expr_785_ = lean_expr_abstract(v_e_783_, v_xs_774_);
v_proof_786_ = lean_expr_abstract(v_h_784_, v_xs_774_);
lean_inc_ref(v_proof_786_);
v___x_791_ = l_Lean_Expr_cleanupAnnotations(v_proof_786_);
v___x_792_ = l_Lean_Expr_isApp(v___x_791_);
if (v___x_792_ == 0)
{
lean_dec_ref(v___x_791_);
goto v___jp_787_;
}
else
{
lean_object* v_arg_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_arg_793_ = lean_ctor_get(v___x_791_, 1);
lean_inc_ref(v_arg_793_);
v___x_794_ = l_Lean_Expr_appFnCleanup___redArg(v___x_791_);
v___x_795_ = l_Lean_Expr_isApp(v___x_794_);
if (v___x_795_ == 0)
{
lean_dec_ref(v___x_794_);
lean_dec_ref(v_arg_793_);
goto v___jp_787_;
}
else
{
lean_object* v_arg_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_arg_796_ = lean_ctor_get(v___x_794_, 1);
lean_inc_ref(v_arg_796_);
v___x_797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_794_);
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_799_ = l_Lean_Expr_isConstOf(v___x_797_, v___x_798_);
lean_dec_ref(v___x_797_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_arg_796_);
lean_dec_ref(v_arg_793_);
goto v___jp_787_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_801_ = lean_unsigned_to_nat(3u);
v___x_802_ = l_Lean_Expr_isAppOfArity(v_arg_796_, v___x_800_, v___x_801_);
lean_dec_ref(v_arg_796_);
if (v___x_802_ == 0)
{
lean_dec_ref(v_arg_793_);
goto v___jp_787_;
}
else
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = l_Lean_Expr_cleanupAnnotations(v_arg_793_);
v___x_804_ = l_Lean_Expr_isApp(v___x_803_);
if (v___x_804_ == 0)
{
lean_dec_ref(v___x_803_);
goto v___jp_787_;
}
else
{
lean_object* v_arg_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_arg_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc_ref(v_arg_805_);
v___x_806_ = l_Lean_Expr_appFnCleanup___redArg(v___x_803_);
v___x_807_ = l_Lean_Expr_isApp(v___x_806_);
if (v___x_807_ == 0)
{
lean_dec_ref(v___x_806_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v_arg_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_arg_808_ = lean_ctor_get(v___x_806_, 1);
lean_inc_ref(v_arg_808_);
v___x_809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_806_);
v___x_810_ = l_Lean_Expr_isConstOf(v___x_809_, v___x_798_);
lean_dec_ref(v___x_809_);
if (v___x_810_ == 0)
{
lean_dec_ref(v_arg_808_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = l_Lean_Expr_cleanupAnnotations(v_arg_808_);
v___x_812_ = l_Lean_Expr_isApp(v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v___x_811_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v_arg_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_arg_813_ = lean_ctor_get(v___x_811_, 1);
lean_inc_ref(v_arg_813_);
v___x_814_ = l_Lean_Expr_appFnCleanup___redArg(v___x_811_);
v___x_815_ = l_Lean_Expr_isApp(v___x_814_);
if (v___x_815_ == 0)
{
lean_dec_ref(v___x_814_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v_arg_816_; uint8_t v___y_818_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_arg_816_ = lean_ctor_get(v___x_814_, 1);
lean_inc_ref(v_arg_816_);
v___x_821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_814_);
v___x_822_ = l_Lean_Expr_isApp(v___x_821_);
if (v___x_822_ == 0)
{
lean_dec_ref(v___x_821_);
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_821_);
v___x_824_ = l_Lean_Expr_isConstOf(v___x_823_, v___x_800_);
lean_dec_ref(v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Expr_getAppFn(v_arg_805_);
if (lean_obj_tag(v___x_825_) == 4)
{
lean_object* v_declName_826_; 
v_declName_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_declName_826_);
lean_dec_ref_known(v___x_825_, 2);
if (lean_obj_tag(v_declName_826_) == 1)
{
lean_object* v_pre_827_; 
v_pre_827_ = lean_ctor_get(v_declName_826_, 0);
if (lean_obj_tag(v_pre_827_) == 0)
{
lean_object* v_str_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_str_828_ = lean_ctor_get(v_declName_826_, 1);
lean_inc_ref(v_str_828_);
lean_dec_ref_known(v_declName_826_, 2);
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_830_ = lean_string_dec_eq(v_str_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_832_ = lean_string_dec_eq(v_str_828_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_834_ = lean_string_dec_eq(v_str_828_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_836_ = lean_string_dec_eq(v_str_828_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_838_ = lean_string_dec_eq(v_str_828_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_840_ = lean_string_dec_eq(v_str_828_, v___x_839_);
lean_dec_ref(v_str_828_);
if (v___x_840_ == 0)
{
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
v___y_818_ = v___x_799_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref(v_str_828_);
v___y_818_ = v___x_799_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref(v_str_828_);
v___y_818_ = v___x_799_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref(v_str_828_);
v___y_818_ = v___x_799_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref(v_str_828_);
v___y_818_ = v___x_799_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref(v_str_828_);
v___y_818_ = v___x_799_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref_known(v_declName_826_, 2);
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
}
else
{
lean_dec(v_declName_826_);
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
}
else
{
lean_dec_ref(v___x_825_);
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
}
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v_arg_805_);
goto v___jp_787_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v_proof_786_);
lean_dec_ref(v_e_771_);
v___x_819_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_819_, 0, v_arg_813_);
lean_ctor_set(v___x_819_, 1, v_exprType_770_);
lean_ctor_set(v___x_819_, 2, v_arg_816_);
lean_ctor_set(v___x_819_, 3, v_expr_785_);
lean_ctor_set(v___x_819_, 4, v_arg_805_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*5, v___x_799_);
v___x_820_ = lean_apply_2(v_toPure_773_, lean_box(0), v___x_819_);
return v___x_820_;
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
v___jp_787_:
{
uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = 1;
lean_inc_ref(v_expr_785_);
v___x_789_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_789_, 0, v_expr_785_);
lean_ctor_set(v___x_789_, 1, v_exprType_770_);
lean_ctor_set(v___x_789_, 2, v_e_771_);
lean_ctor_set(v___x_789_, 3, v_expr_785_);
lean_ctor_set(v___x_789_, 4, v_proof_786_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*5, v___x_788_);
v___x_790_ = lean_apply_2(v_toPure_773_, lean_box(0), v___x_789_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_level_841_, lean_object* v_exprType_842_, lean_object* v_e_843_, lean_object* v___x_844_, lean_object* v_toPure_845_, lean_object* v_xs_846_, lean_object* v_____do__lift_847_){
_start:
{
uint8_t v___x_7771__boxed_848_; lean_object* v_res_849_; 
v___x_7771__boxed_848_ = lean_unbox(v___x_844_);
v_res_849_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_level_841_, v_exprType_842_, v_e_843_, v___x_7771__boxed_848_, v_toPure_845_, v_xs_846_, v_____do__lift_847_);
lean_dec(v_____do__lift_847_);
lean_dec_ref(v_xs_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_850_, lean_object* v_bodyType_851_, lean_object* v_xs_852_, lean_object* v_level_853_, lean_object* v_e_854_, uint8_t v___x_855_, lean_object* v_toPure_856_, lean_object* v_body_857_, lean_object* v_toBind_858_, lean_object* v_____r_859_){
_start:
{
lean_object* v_simp_860_; lean_object* v_exprType_861_; lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_simp_860_ = lean_ctor_get(v_inst_850_, 2);
lean_inc(v_simp_860_);
lean_dec_ref(v_inst_850_);
v_exprType_861_ = lean_expr_abstract(v_bodyType_851_, v_xs_852_);
v___x_862_ = lean_box(v___x_855_);
v___f_863_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_863_, 0, v_level_853_);
lean_closure_set(v___f_863_, 1, v_exprType_861_);
lean_closure_set(v___f_863_, 2, v_e_854_);
lean_closure_set(v___f_863_, 3, v___x_862_);
lean_closure_set(v___f_863_, 4, v_toPure_856_);
lean_closure_set(v___f_863_, 5, v_xs_852_);
v___x_864_ = lean_apply_1(v_simp_860_, v_body_857_);
v___x_865_ = lean_apply_4(v_toBind_858_, lean_box(0), lean_box(0), v___x_864_, v___f_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_866_, lean_object* v_bodyType_867_, lean_object* v_xs_868_, lean_object* v_level_869_, lean_object* v_e_870_, lean_object* v___x_871_, lean_object* v_toPure_872_, lean_object* v_body_873_, lean_object* v_toBind_874_, lean_object* v_____r_875_){
_start:
{
uint8_t v___x_7924__boxed_876_; lean_object* v_res_877_; 
v___x_7924__boxed_876_ = lean_unbox(v___x_871_);
v_res_877_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_866_, v_bodyType_867_, v_xs_868_, v_level_869_, v_e_870_, v___x_7924__boxed_876_, v_toPure_872_, v_body_873_, v_toBind_874_, v_____r_875_);
lean_dec_ref(v_bodyType_867_);
return v_res_877_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_884_, lean_object* v_body_885_, lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v_toMonadRef_888_, lean_object* v___x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_options_898_; uint8_t v_hasTrace_899_; 
v_options_898_ = lean_ctor_get(v___y_892_, 2);
v_hasTrace_899_ = lean_ctor_get_uint8(v_options_898_, sizeof(void*)*1);
if (v_hasTrace_899_ == 0)
{
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___x_889_);
lean_dec_ref(v_toMonadRef_888_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v___x_886_);
lean_dec_ref(v_body_885_);
lean_dec(v_cls_884_);
goto v___jp_895_;
}
else
{
lean_object* v_inheritedTraceOptions_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_inheritedTraceOptions_900_ = lean_ctor_get(v___y_892_, 13);
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_884_);
v___x_902_ = l_Lean_Name_append(v___x_901_, v_cls_884_);
v___x_903_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_900_, v_options_898_, v___x_902_);
lean_dec(v___x_902_);
if (v___x_903_ == 0)
{
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___x_889_);
lean_dec_ref(v_toMonadRef_888_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v___x_886_);
lean_dec_ref(v_body_885_);
lean_dec(v_cls_884_);
goto v___jp_895_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_7393__overap_907_; lean_object* v___x_908_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3);
v___x_905_ = l_Lean_MessageData_ofExpr(v_body_885_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_7393__overap_907_ = l_Lean_addTrace___redArg(v___x_886_, v___x_887_, v_toMonadRef_888_, v___x_889_, v_cls_884_, v___x_906_);
v___x_908_ = lean_apply_5(v___x_7393__overap_907_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, lean_box(0));
return v___x_908_;
}
}
v___jp_895_:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_909_, lean_object* v_body_910_, lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v_toMonadRef_913_, lean_object* v___x_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_909_, v_body_910_, v___x_911_, v___x_912_, v_toMonadRef_913_, v___x_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_923_, lean_object* v_type_924_, lean_object* v___y_925_, lean_object* v_value_926_, uint8_t v___y_927_, lean_object* v___x_928_, uint8_t v___y_929_, lean_object* v_toPure_930_, lean_object* v_us_931_, uint8_t v___x_932_, lean_object* v_rb_933_){
_start:
{
lean_object* v_expr_934_; lean_object* v_exprType_935_; lean_object* v_exprInit_936_; lean_object* v_exprResult_937_; lean_object* v_proof_938_; uint8_t v_modified_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_966_; 
v_expr_934_ = lean_ctor_get(v_rb_933_, 0);
v_exprType_935_ = lean_ctor_get(v_rb_933_, 1);
v_exprInit_936_ = lean_ctor_get(v_rb_933_, 2);
v_exprResult_937_ = lean_ctor_get(v_rb_933_, 3);
v_proof_938_ = lean_ctor_get(v_rb_933_, 4);
v_modified_939_ = lean_ctor_get_uint8(v_rb_933_, sizeof(void*)*5);
v_isSharedCheck_966_ = !lean_is_exclusive(v_rb_933_);
if (v_isSharedCheck_966_ == 0)
{
v___x_941_ = v_rb_933_;
v_isShared_942_ = v_isSharedCheck_966_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_proof_938_);
lean_inc(v_exprResult_937_);
lean_inc(v_exprInit_936_);
lean_inc(v_exprType_935_);
lean_inc(v_expr_934_);
lean_dec(v_rb_933_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_966_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v_expr_945_; lean_object* v___x_946_; lean_object* v_exprType_947_; lean_object* v___x_948_; lean_object* v_exprInit_949_; lean_object* v_exprResult_950_; 
v___x_943_ = 0;
lean_inc_ref_n(v_type_924_, 4);
lean_inc_n(v_declName_923_, 4);
v___x_944_ = l_Lean_mkLambda(v_declName_923_, v___x_943_, v_type_924_, v_expr_934_);
lean_inc_ref_n(v___y_925_, 3);
lean_inc_ref(v___x_944_);
v_expr_945_ = l_Lean_Expr_app___override(v___x_944_, v___y_925_);
v___x_946_ = l_Lean_mkLambda(v_declName_923_, v___x_943_, v_type_924_, v_exprType_935_);
lean_inc_ref(v___x_946_);
v_exprType_947_ = l_Lean_Expr_app___override(v___x_946_, v___y_925_);
v___x_948_ = l_Lean_mkLambda(v_declName_923_, v___x_943_, v_type_924_, v_exprInit_936_);
lean_inc_ref(v___x_948_);
v_exprInit_949_ = l_Lean_Expr_app___override(v___x_948_, v_value_926_);
v_exprResult_950_ = l_Lean_Expr_letE___override(v_declName_923_, v_type_924_, v___y_925_, v_exprResult_937_, v___y_927_);
if (v_modified_939_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_proof_953_; lean_object* v___x_955_; 
lean_dec_ref(v___x_948_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_944_);
lean_dec_ref(v_proof_938_);
lean_dec(v_us_931_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_type_924_);
lean_dec(v_declName_923_);
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_952_ = l_Lean_mkConst(v___x_951_, v___x_928_);
lean_inc_ref(v_expr_945_);
lean_inc_ref(v_exprType_947_);
v_proof_953_ = l_Lean_mkAppB(v___x_952_, v_exprType_947_, v_expr_945_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_proof_953_);
lean_ctor_set(v___x_941_, 3, v_exprResult_950_);
lean_ctor_set(v___x_941_, 2, v_exprInit_949_);
lean_ctor_set(v___x_941_, 1, v_exprType_947_);
lean_ctor_set(v___x_941_, 0, v_expr_945_);
v___x_955_ = v___x_941_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_expr_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_exprType_947_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_exprInit_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_exprResult_950_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_proof_953_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*5, v___y_929_);
v___x_956_ = lean_apply_2(v_toPure_930_, lean_box(0), v___x_955_);
return v___x_956_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_proof_961_; lean_object* v___x_963_; 
lean_dec(v___x_928_);
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_959_ = l_Lean_mkConst(v___x_958_, v_us_931_);
lean_inc_ref(v_type_924_);
v___x_960_ = l_Lean_mkLambda(v_declName_923_, v___x_943_, v_type_924_, v_proof_938_);
v_proof_961_ = l_Lean_mkApp6(v___x_959_, v_type_924_, v___x_946_, v___y_925_, v___x_948_, v___x_944_, v___x_960_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v_proof_961_);
lean_ctor_set(v___x_941_, 3, v_exprResult_950_);
lean_ctor_set(v___x_941_, 2, v_exprInit_949_);
lean_ctor_set(v___x_941_, 1, v_exprType_947_);
lean_ctor_set(v___x_941_, 0, v_expr_945_);
v___x_963_ = v___x_941_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_expr_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_exprType_947_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_exprInit_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_exprResult_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_proof_961_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*5, v___x_932_);
v___x_964_ = lean_apply_2(v_toPure_930_, lean_box(0), v___x_963_);
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_967_, lean_object* v_type_968_, lean_object* v___y_969_, lean_object* v_value_970_, lean_object* v___y_971_, lean_object* v___x_972_, lean_object* v___y_973_, lean_object* v_toPure_974_, lean_object* v_us_975_, lean_object* v___x_976_, lean_object* v_rb_977_){
_start:
{
uint8_t v___y_8019__boxed_978_; uint8_t v___y_8021__boxed_979_; uint8_t v___x_8022__boxed_980_; lean_object* v_res_981_; 
v___y_8019__boxed_978_ = lean_unbox(v___y_971_);
v___y_8021__boxed_979_ = lean_unbox(v___y_973_);
v___x_8022__boxed_980_ = lean_unbox(v___x_976_);
v_res_981_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_967_, v_type_968_, v___y_969_, v_value_970_, v___y_8019__boxed_978_, v___x_972_, v___y_8021__boxed_979_, v_toPure_974_, v_us_975_, v___x_8022__boxed_980_, v_rb_977_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_982_, lean_object* v_____x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_apply_1(v___f_982_, v_____x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_989_, lean_object* v_declName_990_, lean_object* v_type_991_, lean_object* v_value_992_, lean_object* v_us_993_, lean_object* v___x_994_, uint8_t v___x_995_, lean_object* v_toPure_996_, lean_object* v_rb_997_){
_start:
{
lean_object* v_expr_998_; lean_object* v_exprType_999_; lean_object* v_exprInit_1000_; lean_object* v_exprResult_1001_; lean_object* v_proof_1002_; uint8_t v_modified_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1031_; 
v_expr_998_ = lean_ctor_get(v_rb_997_, 0);
v_exprType_999_ = lean_ctor_get(v_rb_997_, 1);
v_exprInit_1000_ = lean_ctor_get(v_rb_997_, 2);
v_exprResult_1001_ = lean_ctor_get(v_rb_997_, 3);
v_proof_1002_ = lean_ctor_get(v_rb_997_, 4);
v_modified_1003_ = lean_ctor_get_uint8(v_rb_997_, sizeof(void*)*5);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_rb_997_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1005_ = v_rb_997_;
v_isShared_1006_ = v_isSharedCheck_1031_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_proof_1002_);
lean_inc(v_exprResult_1001_);
lean_inc(v_exprInit_1000_);
lean_inc(v_exprType_999_);
lean_inc(v_expr_998_);
lean_dec(v_rb_997_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1031_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_expr_1007_; lean_object* v_exprType_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v_exprInit_1011_; lean_object* v_exprResult_1012_; 
v_expr_1007_ = lean_expr_lower_loose_bvars(v_expr_998_, v___x_989_, v___x_989_);
lean_dec_ref(v_expr_998_);
v_exprType_1008_ = lean_expr_lower_loose_bvars(v_exprType_999_, v___x_989_, v___x_989_);
lean_dec_ref(v_exprType_999_);
v___x_1009_ = 0;
lean_inc_ref(v_type_991_);
lean_inc(v_declName_990_);
v___x_1010_ = l_Lean_mkLambda(v_declName_990_, v___x_1009_, v_type_991_, v_exprInit_1000_);
lean_inc_ref(v_value_992_);
lean_inc_ref(v___x_1010_);
v_exprInit_1011_ = l_Lean_Expr_app___override(v___x_1010_, v_value_992_);
v_exprResult_1012_ = lean_expr_lower_loose_bvars(v_exprResult_1001_, v___x_989_, v___x_989_);
lean_dec_ref(v_exprResult_1001_);
if (v_modified_1003_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_proof_1018_; lean_object* v___x_1020_; 
lean_dec_ref(v___x_1010_);
lean_dec_ref(v_proof_1002_);
lean_dec(v_declName_990_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1014_ = l_Lean_mkConst(v___x_1013_, v_us_993_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1016_ = l_Lean_mkConst(v___x_1015_, v___x_994_);
lean_inc_ref_n(v_expr_1007_, 3);
lean_inc_ref_n(v_exprType_1008_, 2);
v___x_1017_ = l_Lean_mkAppB(v___x_1016_, v_exprType_1008_, v_expr_1007_);
v_proof_1018_ = l_Lean_mkApp6(v___x_1014_, v_type_991_, v_exprType_1008_, v_value_992_, v_expr_1007_, v_expr_1007_, v___x_1017_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v_proof_1018_);
lean_ctor_set(v___x_1005_, 3, v_exprResult_1012_);
lean_ctor_set(v___x_1005_, 2, v_exprInit_1011_);
lean_ctor_set(v___x_1005_, 1, v_exprType_1008_);
lean_ctor_set(v___x_1005_, 0, v_expr_1007_);
v___x_1020_ = v___x_1005_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_expr_1007_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_exprType_1008_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_exprInit_1011_);
lean_ctor_set(v_reuseFailAlloc_1022_, 3, v_exprResult_1012_);
lean_ctor_set(v_reuseFailAlloc_1022_, 4, v_proof_1018_);
v___x_1020_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*5, v___x_995_);
v___x_1021_ = lean_apply_2(v_toPure_996_, lean_box(0), v___x_1020_);
return v___x_1021_;
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_proof_1026_; lean_object* v___x_1028_; 
lean_dec(v___x_994_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1024_ = l_Lean_mkConst(v___x_1023_, v_us_993_);
lean_inc_ref(v_type_991_);
v___x_1025_ = l_Lean_mkLambda(v_declName_990_, v___x_1009_, v_type_991_, v_proof_1002_);
lean_inc_ref(v_expr_1007_);
lean_inc_ref(v_exprType_1008_);
v_proof_1026_ = l_Lean_mkApp6(v___x_1024_, v_type_991_, v_exprType_1008_, v_value_992_, v___x_1010_, v_expr_1007_, v___x_1025_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v_proof_1026_);
lean_ctor_set(v___x_1005_, 3, v_exprResult_1012_);
lean_ctor_set(v___x_1005_, 2, v_exprInit_1011_);
lean_ctor_set(v___x_1005_, 1, v_exprType_1008_);
lean_ctor_set(v___x_1005_, 0, v_expr_1007_);
v___x_1028_ = v___x_1005_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_expr_1007_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_exprType_1008_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_exprInit_1011_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_exprResult_1012_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_proof_1026_);
v___x_1028_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*5, v___x_995_);
v___x_1029_ = lean_apply_2(v_toPure_996_, lean_box(0), v___x_1028_);
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1032_, lean_object* v_declName_1033_, lean_object* v_type_1034_, lean_object* v_value_1035_, lean_object* v_us_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_toPure_1039_, lean_object* v_rb_1040_){
_start:
{
uint8_t v___x_8109__boxed_1041_; lean_object* v_res_1042_; 
v___x_8109__boxed_1041_ = lean_unbox(v___x_1038_);
v_res_1042_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1032_, v_declName_1033_, v_type_1034_, v_value_1035_, v_us_1036_, v___x_1037_, v___x_8109__boxed_1041_, v_toPure_1039_, v_rb_1040_);
lean_dec(v___x_1032_);
return v_res_1042_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1049_, lean_object* v_declName_1050_, lean_object* v_val_1051_, lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v_toMonadRef_1054_, lean_object* v___x_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_options_1064_; uint8_t v_hasTrace_1065_; 
v_options_1064_ = lean_ctor_get(v___y_1058_, 2);
v_hasTrace_1065_ = lean_ctor_get_uint8(v_options_1064_, sizeof(void*)*1);
if (v_hasTrace_1065_ == 0)
{
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_toMonadRef_1054_);
lean_dec_ref(v___x_1053_);
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_val_1051_);
lean_dec(v_declName_1050_);
lean_dec(v_cls_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v_inheritedTraceOptions_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_inheritedTraceOptions_1066_ = lean_ctor_get(v___y_1058_, 13);
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1049_);
v___x_1068_ = l_Lean_Name_append(v___x_1067_, v_cls_1049_);
v___x_1069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1066_, v_options_1064_, v___x_1068_);
lean_dec(v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_toMonadRef_1054_);
lean_dec_ref(v___x_1053_);
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_val_1051_);
lean_dec(v_declName_1050_);
lean_dec(v_cls_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_7737__overap_1077_; lean_object* v___x_1078_; 
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1071_ = l_Lean_MessageData_ofName(v_declName_1050_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_MessageData_ofExpr(v_val_1051_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_7737__overap_1077_ = l_Lean_addTrace___redArg(v___x_1052_, v___x_1053_, v_toMonadRef_1054_, v___x_1055_, v_cls_1049_, v___x_1076_);
v___x_1078_ = lean_apply_5(v___x_7737__overap_1077_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
return v___x_1078_;
}
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1079_, lean_object* v_declName_1080_, lean_object* v_val_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v_toMonadRef_1084_, lean_object* v___x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1079_, v_declName_1080_, v_val_1081_, v___x_1082_, v___x_1083_, v_toMonadRef_1084_, v___x_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v_res_1091_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1098_, lean_object* v_declName_1099_, lean_object* v_val_1100_, lean_object* v_val_x27_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v_toMonadRef_1104_, lean_object* v___x_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_options_1114_; uint8_t v_hasTrace_1115_; 
v_options_1114_ = lean_ctor_get(v___y_1108_, 2);
v_hasTrace_1115_ = lean_ctor_get_uint8(v_options_1114_, sizeof(void*)*1);
if (v_hasTrace_1115_ == 0)
{
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_toMonadRef_1104_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v_val_x27_1101_);
lean_dec_ref(v_val_1100_);
lean_dec(v_declName_1099_);
lean_dec(v_cls_1098_);
goto v___jp_1111_;
}
else
{
lean_object* v_inheritedTraceOptions_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_inheritedTraceOptions_1116_ = lean_ctor_get(v___y_1108_, 13);
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1098_);
v___x_1118_ = l_Lean_Name_append(v___x_1117_, v_cls_1098_);
v___x_1119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1116_, v_options_1114_, v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_toMonadRef_1104_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v_val_x27_1101_);
lean_dec_ref(v_val_1100_);
lean_dec(v_declName_1099_);
lean_dec(v_cls_1098_);
goto v___jp_1111_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_7481__overap_1131_; lean_object* v___x_1132_; 
v___x_1120_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1121_ = l_Lean_MessageData_ofName(v_declName_1099_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_ofExpr(v_val_1100_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_ofExpr(v_val_x27_1101_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_7481__overap_1131_ = l_Lean_addTrace___redArg(v___x_1102_, v___x_1103_, v_toMonadRef_1104_, v___x_1105_, v_cls_1098_, v___x_1130_);
v___x_1132_ = lean_apply_5(v___x_7481__overap_1131_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
return v___x_1132_;
}
}
v___jp_1111_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1133_, lean_object* v_declName_1134_, lean_object* v_val_1135_, lean_object* v_val_x27_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v_toMonadRef_1139_, lean_object* v___x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1133_, v_declName_1134_, v_val_1135_, v_val_x27_1136_, v___x_1137_, v___x_1138_, v_toMonadRef_1139_, v___x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_e_1147_, lean_object* v_xs_1148_, lean_object* v_h_1149_, uint8_t v___x_1150_, lean_object* v_toPure_1151_, lean_object* v_toBind_1152_, lean_object* v___f_1153_, lean_object* v_____r_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1155_ = lean_expr_abstract(v_e_1147_, v_xs_1148_);
v___x_1156_ = lean_expr_abstract(v_h_1149_, v_xs_1148_);
v___x_1157_ = lean_box(v___x_1150_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1155_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_apply_2(v_toPure_1151_, lean_box(0), v___x_1159_);
v___x_1161_ = lean_apply_4(v_toBind_1152_, lean_box(0), lean_box(0), v___x_1160_, v___f_1153_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_e_1162_, lean_object* v_xs_1163_, lean_object* v_h_1164_, lean_object* v___x_1165_, lean_object* v_toPure_1166_, lean_object* v_toBind_1167_, lean_object* v___f_1168_, lean_object* v_____r_1169_){
_start:
{
uint8_t v___x_8341__boxed_1170_; lean_object* v_res_1171_; 
v___x_8341__boxed_1170_ = lean_unbox(v___x_1165_);
v_res_1171_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_e_1162_, v_xs_1163_, v_h_1164_, v___x_8341__boxed_1170_, v_toPure_1166_, v_toBind_1167_, v___f_1168_, v_____r_1169_);
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_xs_1163_);
lean_dec_ref(v_e_1162_);
return v_res_1171_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1175_, lean_object* v_declName_1176_, lean_object* v_val_1177_, lean_object* v_e_1178_, lean_object* v___x_1179_, lean_object* v___x_1180_, lean_object* v_toMonadRef_1181_, lean_object* v___x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_options_1191_; uint8_t v_hasTrace_1192_; 
v_options_1191_ = lean_ctor_get(v___y_1185_, 2);
v_hasTrace_1192_ = lean_ctor_get_uint8(v_options_1191_, sizeof(void*)*1);
if (v_hasTrace_1192_ == 0)
{
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v___x_1182_);
lean_dec_ref(v_toMonadRef_1181_);
lean_dec_ref(v___x_1180_);
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_e_1178_);
lean_dec_ref(v_val_1177_);
lean_dec(v_declName_1176_);
lean_dec(v_cls_1175_);
goto v___jp_1188_;
}
else
{
lean_object* v_inheritedTraceOptions_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v_inheritedTraceOptions_1193_ = lean_ctor_get(v___y_1185_, 13);
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1175_);
v___x_1195_ = l_Lean_Name_append(v___x_1194_, v_cls_1175_);
v___x_1196_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1193_, v_options_1191_, v___x_1195_);
lean_dec(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v___x_1182_);
lean_dec_ref(v_toMonadRef_1181_);
lean_dec_ref(v___x_1180_);
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_e_1178_);
lean_dec_ref(v_val_1177_);
lean_dec(v_declName_1176_);
lean_dec(v_cls_1175_);
goto v___jp_1188_;
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_7631__overap_1208_; lean_object* v___x_1209_; 
v___x_1197_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1198_ = l_Lean_MessageData_ofName(v_declName_1176_);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_MessageData_ofExpr(v_val_1177_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_MessageData_ofExpr(v_e_1178_);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_7631__overap_1208_ = l_Lean_addTrace___redArg(v___x_1179_, v___x_1180_, v_toMonadRef_1181_, v___x_1182_, v_cls_1175_, v___x_1207_);
v___x_1209_ = lean_apply_5(v___x_7631__overap_1208_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, lean_box(0));
return v___x_1209_;
}
}
v___jp_1188_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1210_, lean_object* v_declName_1211_, lean_object* v_val_1212_, lean_object* v_e_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v_toMonadRef_1216_, lean_object* v___x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1210_, v_declName_1211_, v_val_1212_, v_e_1213_, v___x_1214_, v___x_1215_, v_toMonadRef_1216_, v___x_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_level_1233_, lean_object* v___x_1234_, lean_object* v_type_1235_, lean_object* v_value_1236_, uint8_t v___x_1237_, lean_object* v_toPure_1238_, lean_object* v_toBind_1239_, lean_object* v___f_1240_, lean_object* v_xs_1241_, uint8_t v___x_1242_, lean_object* v___f_1243_, lean_object* v_declName_1244_, lean_object* v_val_1245_, lean_object* v___x_1246_, lean_object* v___x_1247_, lean_object* v_toMonadRef_1248_, lean_object* v___x_1249_, lean_object* v_inst_1250_, lean_object* v_____do__lift_1251_){
_start:
{
if (lean_obj_tag(v_____do__lift_1251_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_inst_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v_toMonadRef_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v_val_1245_);
lean_dec(v_declName_1244_);
lean_dec(v___f_1243_);
lean_dec_ref(v_xs_1241_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_level_1233_);
lean_ctor_set(v___x_1253_, 1, v___x_1234_);
v___x_1254_ = l_Lean_mkConst(v___x_1252_, v___x_1253_);
lean_inc_ref(v_value_1236_);
v___x_1255_ = l_Lean_mkAppB(v___x_1254_, v_type_1235_, v_value_1236_);
v___x_1256_ = lean_box(v___x_1237_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_value_1236_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_apply_2(v_toPure_1238_, lean_box(0), v___x_1258_);
v___x_1260_ = lean_apply_4(v_toBind_1239_, lean_box(0), lean_box(0), v___x_1259_, v___f_1240_);
return v___x_1260_;
}
else
{
lean_object* v_e_1261_; lean_object* v_h_1262_; lean_object* v___x_1263_; lean_object* v___f_1264_; lean_object* v_cls_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec(v___f_1240_);
lean_dec_ref(v_value_1236_);
lean_dec_ref(v_type_1235_);
lean_dec(v___x_1234_);
lean_dec(v_level_1233_);
v_e_1261_ = lean_ctor_get(v_____do__lift_1251_, 0);
lean_inc_ref_n(v_e_1261_, 2);
v_h_1262_ = lean_ctor_get(v_____do__lift_1251_, 1);
lean_inc_ref(v_h_1262_);
lean_dec_ref_known(v_____do__lift_1251_, 2);
v___x_1263_ = lean_box(v___x_1242_);
lean_inc(v_toBind_1239_);
v___f_1264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1264_, 0, v_e_1261_);
lean_closure_set(v___f_1264_, 1, v_xs_1241_);
lean_closure_set(v___f_1264_, 2, v_h_1262_);
lean_closure_set(v___f_1264_, 3, v___x_1263_);
lean_closure_set(v___f_1264_, 4, v_toPure_1238_);
lean_closure_set(v___f_1264_, 5, v_toBind_1239_);
lean_closure_set(v___f_1264_, 6, v___f_1243_);
v_cls_1265_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1266_, 0, v_cls_1265_);
lean_closure_set(v___f_1266_, 1, v_declName_1244_);
lean_closure_set(v___f_1266_, 2, v_val_1245_);
lean_closure_set(v___f_1266_, 3, v_e_1261_);
lean_closure_set(v___f_1266_, 4, v___x_1246_);
lean_closure_set(v___f_1266_, 5, v___x_1247_);
lean_closure_set(v___f_1266_, 6, v_toMonadRef_1248_);
lean_closure_set(v___f_1266_, 7, v___x_1249_);
v___x_1267_ = lean_apply_2(v_inst_1250_, lean_box(0), v___f_1266_);
v___x_1268_ = lean_apply_4(v_toBind_1239_, lean_box(0), lean_box(0), v___x_1267_, v___f_1264_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_level_1269_ = _args[0];
lean_object* v___x_1270_ = _args[1];
lean_object* v_type_1271_ = _args[2];
lean_object* v_value_1272_ = _args[3];
lean_object* v___x_1273_ = _args[4];
lean_object* v_toPure_1274_ = _args[5];
lean_object* v_toBind_1275_ = _args[6];
lean_object* v___f_1276_ = _args[7];
lean_object* v_xs_1277_ = _args[8];
lean_object* v___x_1278_ = _args[9];
lean_object* v___f_1279_ = _args[10];
lean_object* v_declName_1280_ = _args[11];
lean_object* v_val_1281_ = _args[12];
lean_object* v___x_1282_ = _args[13];
lean_object* v___x_1283_ = _args[14];
lean_object* v_toMonadRef_1284_ = _args[15];
lean_object* v___x_1285_ = _args[16];
lean_object* v_inst_1286_ = _args[17];
lean_object* v_____do__lift_1287_ = _args[18];
_start:
{
uint8_t v___x_8481__boxed_1288_; uint8_t v___x_8483__boxed_1289_; lean_object* v_res_1290_; 
v___x_8481__boxed_1288_ = lean_unbox(v___x_1273_);
v___x_8483__boxed_1289_ = lean_unbox(v___x_1278_);
v_res_1290_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_level_1269_, v___x_1270_, v_type_1271_, v_value_1272_, v___x_8481__boxed_1288_, v_toPure_1274_, v_toBind_1275_, v___f_1276_, v_xs_1277_, v___x_8483__boxed_1289_, v___f_1279_, v_declName_1280_, v_val_1281_, v___x_1282_, v___x_1283_, v_toMonadRef_1284_, v___x_1285_, v_inst_1286_, v_____do__lift_1287_);
return v_res_1290_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1300_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1301_ = lean_unsigned_to_nat(8u);
v___x_1302_ = lean_unsigned_to_nat(287u);
v___x_1303_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1304_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1305_ = l_mkPanicMessageWithDecl(v___x_1304_, v___x_1303_, v___x_1302_, v___x_1301_, v___x_1300_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1306_, lean_object* v_type_1307_, lean_object* v_fst_1308_, lean_object* v___x_1309_, lean_object* v_value_1310_, uint8_t v___x_1311_, uint8_t v_fst_1312_, lean_object* v___x_1313_, uint8_t v___x_1314_, lean_object* v_toPure_1315_, lean_object* v_us_1316_, lean_object* v_snd_1317_, lean_object* v___x_1318_, lean_object* v_rb_1319_){
_start:
{
lean_object* v_expr_1320_; lean_object* v_exprType_1321_; lean_object* v_exprInit_1322_; lean_object* v_exprResult_1323_; lean_object* v_proof_1324_; uint8_t v_modified_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1370_; 
v_expr_1320_ = lean_ctor_get(v_rb_1319_, 0);
v_exprType_1321_ = lean_ctor_get(v_rb_1319_, 1);
v_exprInit_1322_ = lean_ctor_get(v_rb_1319_, 2);
v_exprResult_1323_ = lean_ctor_get(v_rb_1319_, 3);
v_proof_1324_ = lean_ctor_get(v_rb_1319_, 4);
v_modified_1325_ = lean_ctor_get_uint8(v_rb_1319_, sizeof(void*)*5);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_rb_1319_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1327_ = v_rb_1319_;
v_isShared_1328_ = v_isSharedCheck_1370_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_proof_1324_);
lean_inc(v_exprResult_1323_);
lean_inc(v_exprInit_1322_);
lean_inc(v_exprType_1321_);
lean_inc(v_expr_1320_);
lean_dec(v_rb_1319_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1370_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_expr_has_loose_bvar(v_exprType_1321_, v___x_1329_);
if (v___x_1330_ == 0)
{
uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v_expr_1333_; lean_object* v_exprType_1334_; lean_object* v___x_1335_; lean_object* v_exprInit_1336_; lean_object* v_exprResult_1337_; 
v___x_1331_ = 0;
lean_inc_ref_n(v_type_1307_, 3);
lean_inc_n(v_declName_1306_, 3);
v___x_1332_ = l_Lean_mkLambda(v_declName_1306_, v___x_1331_, v_type_1307_, v_expr_1320_);
lean_inc_ref_n(v_fst_1308_, 2);
lean_inc_ref(v___x_1332_);
v_expr_1333_ = l_Lean_Expr_app___override(v___x_1332_, v_fst_1308_);
v_exprType_1334_ = lean_expr_lower_loose_bvars(v_exprType_1321_, v___x_1309_, v___x_1309_);
lean_dec_ref(v_exprType_1321_);
v___x_1335_ = l_Lean_mkLambda(v_declName_1306_, v___x_1331_, v_type_1307_, v_exprInit_1322_);
lean_inc_ref(v_value_1310_);
lean_inc_ref(v___x_1335_);
v_exprInit_1336_ = l_Lean_Expr_app___override(v___x_1335_, v_value_1310_);
v_exprResult_1337_ = l_Lean_Expr_letE___override(v_declName_1306_, v_type_1307_, v_fst_1308_, v_exprResult_1323_, v___x_1311_);
if (v_fst_1312_ == 0)
{
lean_dec_ref(v_snd_1317_);
lean_dec_ref(v_fst_1308_);
if (v_modified_1325_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v_proof_1340_; lean_object* v___x_1342_; 
lean_dec_ref(v___x_1335_);
lean_dec_ref(v___x_1332_);
lean_dec_ref(v_proof_1324_);
lean_dec(v_us_1316_);
lean_dec_ref(v_value_1310_);
lean_dec_ref(v_type_1307_);
lean_dec(v_declName_1306_);
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1339_ = l_Lean_mkConst(v___x_1338_, v___x_1313_);
lean_inc_ref(v_expr_1333_);
lean_inc_ref(v_exprType_1334_);
v_proof_1340_ = l_Lean_mkAppB(v___x_1339_, v_exprType_1334_, v_expr_1333_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 4, v_proof_1340_);
lean_ctor_set(v___x_1327_, 3, v_exprResult_1337_);
lean_ctor_set(v___x_1327_, 2, v_exprInit_1336_);
lean_ctor_set(v___x_1327_, 1, v_exprType_1334_);
lean_ctor_set(v___x_1327_, 0, v_expr_1333_);
v___x_1342_ = v___x_1327_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_expr_1333_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_exprType_1334_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_exprInit_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_exprResult_1337_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_proof_1340_);
v___x_1342_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; 
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*5, v___x_1314_);
v___x_1343_ = lean_apply_2(v_toPure_1315_, lean_box(0), v___x_1342_);
return v___x_1343_;
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_proof_1348_; lean_object* v___x_1350_; 
lean_dec(v___x_1313_);
v___x_1345_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1346_ = l_Lean_mkConst(v___x_1345_, v_us_1316_);
lean_inc_ref(v_type_1307_);
v___x_1347_ = l_Lean_mkLambda(v_declName_1306_, v___x_1331_, v_type_1307_, v_proof_1324_);
lean_inc_ref(v_exprType_1334_);
v_proof_1348_ = l_Lean_mkApp6(v___x_1346_, v_type_1307_, v_exprType_1334_, v_value_1310_, v___x_1335_, v___x_1332_, v___x_1347_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 4, v_proof_1348_);
lean_ctor_set(v___x_1327_, 3, v_exprResult_1337_);
lean_ctor_set(v___x_1327_, 2, v_exprInit_1336_);
lean_ctor_set(v___x_1327_, 1, v_exprType_1334_);
lean_ctor_set(v___x_1327_, 0, v_expr_1333_);
v___x_1350_ = v___x_1327_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_expr_1333_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_exprType_1334_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_exprInit_1336_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_exprResult_1337_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_proof_1348_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; 
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*5, v___x_1311_);
v___x_1351_ = lean_apply_2(v_toPure_1315_, lean_box(0), v___x_1350_);
return v___x_1351_;
}
}
}
else
{
lean_dec(v___x_1313_);
if (v_modified_1325_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_proof_1355_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_1332_);
lean_dec_ref(v_proof_1324_);
lean_dec(v_declName_1306_);
v___x_1353_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1354_ = l_Lean_mkConst(v___x_1353_, v_us_1316_);
lean_inc_ref(v_exprType_1334_);
v_proof_1355_ = l_Lean_mkApp6(v___x_1354_, v_type_1307_, v_exprType_1334_, v_value_1310_, v_fst_1308_, v___x_1335_, v_snd_1317_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 4, v_proof_1355_);
lean_ctor_set(v___x_1327_, 3, v_exprResult_1337_);
lean_ctor_set(v___x_1327_, 2, v_exprInit_1336_);
lean_ctor_set(v___x_1327_, 1, v_exprType_1334_);
lean_ctor_set(v___x_1327_, 0, v_expr_1333_);
v___x_1357_ = v___x_1327_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_expr_1333_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_exprType_1334_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_exprInit_1336_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_exprResult_1337_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_proof_1355_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*5, v___x_1311_);
v___x_1358_ = lean_apply_2(v_toPure_1315_, lean_box(0), v___x_1357_);
return v___x_1358_;
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_proof_1363_; lean_object* v___x_1365_; 
v___x_1360_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1361_ = l_Lean_mkConst(v___x_1360_, v_us_1316_);
lean_inc_ref(v_type_1307_);
v___x_1362_ = l_Lean_mkLambda(v_declName_1306_, v___x_1331_, v_type_1307_, v_proof_1324_);
lean_inc_ref(v_exprType_1334_);
v_proof_1363_ = l_Lean_mkApp8(v___x_1361_, v_type_1307_, v_exprType_1334_, v_value_1310_, v_fst_1308_, v___x_1335_, v___x_1332_, v_snd_1317_, v___x_1362_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 4, v_proof_1363_);
lean_ctor_set(v___x_1327_, 3, v_exprResult_1337_);
lean_ctor_set(v___x_1327_, 2, v_exprInit_1336_);
lean_ctor_set(v___x_1327_, 1, v_exprType_1334_);
lean_ctor_set(v___x_1327_, 0, v_expr_1333_);
v___x_1365_ = v___x_1327_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_expr_1333_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_exprType_1334_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_exprInit_1336_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_exprResult_1337_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_proof_1363_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*5, v___x_1311_);
v___x_1366_ = lean_apply_2(v_toPure_1315_, lean_box(0), v___x_1365_);
return v___x_1366_;
}
}
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_del_object(v___x_1327_);
lean_dec_ref(v_proof_1324_);
lean_dec_ref(v_exprResult_1323_);
lean_dec_ref(v_exprInit_1322_);
lean_dec_ref(v_exprType_1321_);
lean_dec_ref(v_expr_1320_);
lean_dec_ref(v_snd_1317_);
lean_dec(v_us_1316_);
lean_dec(v_toPure_1315_);
lean_dec(v___x_1313_);
lean_dec_ref(v_value_1310_);
lean_dec_ref(v_fst_1308_);
lean_dec_ref(v_type_1307_);
lean_dec(v_declName_1306_);
v___x_1368_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1369_ = l_panic___redArg(v___x_1318_, v___x_1368_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1371_, lean_object* v_type_1372_, lean_object* v_fst_1373_, lean_object* v___x_1374_, lean_object* v_value_1375_, lean_object* v___x_1376_, lean_object* v_fst_1377_, lean_object* v___x_1378_, lean_object* v___x_1379_, lean_object* v_toPure_1380_, lean_object* v_us_1381_, lean_object* v_snd_1382_, lean_object* v___x_1383_, lean_object* v_rb_1384_){
_start:
{
uint8_t v___x_8603__boxed_1385_; uint8_t v_fst_8604__boxed_1386_; uint8_t v___x_8606__boxed_1387_; lean_object* v_res_1388_; 
v___x_8603__boxed_1385_ = lean_unbox(v___x_1376_);
v_fst_8604__boxed_1386_ = lean_unbox(v_fst_1377_);
v___x_8606__boxed_1387_ = lean_unbox(v___x_1379_);
v_res_1388_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1371_, v_type_1372_, v_fst_1373_, v___x_1374_, v_value_1375_, v___x_8603__boxed_1385_, v_fst_8604__boxed_1386_, v___x_1378_, v___x_8606__boxed_1387_, v_toPure_1380_, v_us_1381_, v_snd_1382_, v___x_1383_, v_rb_1384_);
lean_dec(v___x_1383_);
lean_dec(v___x_1374_);
return v_res_1388_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_instMonadEIO(lean_box(0));
return v___x_1392_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0);
v___x_1394_ = l_StateRefT_x27_instMonad___redArg(v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1402_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1401_, v___x_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8);
v___f_1405_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___x_1406_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1405_, v___x_1404_);
return v___x_1406_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1409_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11));
v___x_1411_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1410_, v___x_1409_, v___x_1408_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; 
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12);
v___f_1414_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___f_1415_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10));
v___x_1416_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1415_, v___f_1414_, v___x_1413_);
return v___x_1416_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14));
v___x_1419_ = lean_unsigned_to_nat(34u);
v___x_1420_ = lean_unsigned_to_nat(217u);
v___x_1421_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1423_ = l_mkPanicMessageWithDecl(v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1424_, lean_object* v_type_1425_, lean_object* v_value_1426_, uint8_t v___y_1427_, lean_object* v___x_1428_, lean_object* v_toPure_1429_, lean_object* v_us_1430_, uint8_t v___x_1431_, lean_object* v_decl_1432_, lean_object* v_x_1433_, lean_object* v_i_1434_, lean_object* v_xs_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_info_1440_, lean_object* v_fixed_1441_, lean_object* v_used_1442_, lean_object* v_body_1443_, lean_object* v_toBind_1444_, lean_object* v_withNewLemmas_1445_, lean_object* v_val_x27_1446_, lean_object* v_val_1447_, uint8_t v___x_1448_, lean_object* v_____r_1449_){
_start:
{
uint8_t v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1469_; uint8_t v___x_1471_; 
v___x_1471_ = lean_expr_eqv(v_val_1447_, v_val_x27_1446_);
if (v___x_1471_ == 0)
{
v___y_1469_ = v___y_1427_;
goto v___jp_1468_;
}
else
{
v___y_1469_ = v___x_1448_;
goto v___jp_1468_;
}
v___jp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1453_ = lean_box(v___y_1427_);
v___x_1454_ = lean_box(v___y_1451_);
v___x_1455_ = lean_box(v___x_1431_);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_1456_, 0, v_declName_1424_);
lean_closure_set(v___f_1456_, 1, v_type_1425_);
lean_closure_set(v___f_1456_, 2, v___y_1452_);
lean_closure_set(v___f_1456_, 3, v_value_1426_);
lean_closure_set(v___f_1456_, 4, v___x_1453_);
lean_closure_set(v___f_1456_, 5, v___x_1428_);
lean_closure_set(v___f_1456_, 6, v___x_1454_);
lean_closure_set(v___f_1456_, 7, v_toPure_1429_);
lean_closure_set(v___f_1456_, 8, v_us_1430_);
lean_closure_set(v___f_1456_, 9, v___x_1455_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_decl_1432_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1459_);
lean_inc_ref(v_x_1433_);
v___x_1461_ = lean_array_push(v___x_1460_, v_x_1433_);
v___x_1462_ = lean_nat_add(v_i_1434_, v___x_1459_);
v___x_1463_ = lean_array_push(v_xs_1435_, v_x_1433_);
lean_inc_ref(v_inst_1438_);
lean_inc_ref(v_inst_1436_);
v___x_1464_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1436_, v_inst_1437_, v_inst_1438_, v_inst_1439_, v_info_1440_, v_fixed_1441_, v_used_1442_, v_body_1443_, v___x_1462_, v___x_1463_);
v___x_1465_ = lean_apply_4(v_toBind_1444_, lean_box(0), lean_box(0), v___x_1464_, v___f_1456_);
v___x_1466_ = lean_apply_3(v_withNewLemmas_1445_, lean_box(0), v___x_1461_, v___x_1465_);
v___x_1467_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1438_, v_inst_1436_, v___x_1458_, v___x_1466_);
return v___x_1467_;
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
lean_inc_ref(v_value_1426_);
v___y_1451_ = v___y_1469_;
v___y_1452_ = v_value_1426_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_expr_abstract(v_val_x27_1446_, v_xs_1435_);
v___y_1451_ = v___y_1469_;
v___y_1452_ = v___x_1470_;
goto v___jp_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1472_ = _args[0];
lean_object* v_type_1473_ = _args[1];
lean_object* v_value_1474_ = _args[2];
lean_object* v___y_1475_ = _args[3];
lean_object* v___x_1476_ = _args[4];
lean_object* v_toPure_1477_ = _args[5];
lean_object* v_us_1478_ = _args[6];
lean_object* v___x_1479_ = _args[7];
lean_object* v_decl_1480_ = _args[8];
lean_object* v_x_1481_ = _args[9];
lean_object* v_i_1482_ = _args[10];
lean_object* v_xs_1483_ = _args[11];
lean_object* v_inst_1484_ = _args[12];
lean_object* v_inst_1485_ = _args[13];
lean_object* v_inst_1486_ = _args[14];
lean_object* v_inst_1487_ = _args[15];
lean_object* v_info_1488_ = _args[16];
lean_object* v_fixed_1489_ = _args[17];
lean_object* v_used_1490_ = _args[18];
lean_object* v_body_1491_ = _args[19];
lean_object* v_toBind_1492_ = _args[20];
lean_object* v_withNewLemmas_1493_ = _args[21];
lean_object* v_val_x27_1494_ = _args[22];
lean_object* v_val_1495_ = _args[23];
lean_object* v___x_1496_ = _args[24];
lean_object* v_____r_1497_ = _args[25];
_start:
{
uint8_t v___y_8864__boxed_1498_; uint8_t v___x_8866__boxed_1499_; uint8_t v___x_8872__boxed_1500_; lean_object* v_res_1501_; 
v___y_8864__boxed_1498_ = lean_unbox(v___y_1475_);
v___x_8866__boxed_1499_ = lean_unbox(v___x_1479_);
v___x_8872__boxed_1500_ = lean_unbox(v___x_1496_);
v_res_1501_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1472_, v_type_1473_, v_value_1474_, v___y_8864__boxed_1498_, v___x_1476_, v_toPure_1477_, v_us_1478_, v___x_8866__boxed_1499_, v_decl_1480_, v_x_1481_, v_i_1482_, v_xs_1483_, v_inst_1484_, v_inst_1485_, v_inst_1486_, v_inst_1487_, v_info_1488_, v_fixed_1489_, v_used_1490_, v_body_1491_, v_toBind_1492_, v_withNewLemmas_1493_, v_val_x27_1494_, v_val_1495_, v___x_8872__boxed_1500_, v_____r_1497_);
lean_dec_ref(v_val_1495_);
lean_dec_ref(v_val_x27_1494_);
lean_dec(v_i_1482_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1502_, lean_object* v_type_1503_, lean_object* v_value_1504_, uint8_t v___y_1505_, lean_object* v___x_1506_, lean_object* v_toPure_1507_, lean_object* v_us_1508_, uint8_t v___x_1509_, lean_object* v_decl_1510_, lean_object* v_x_1511_, lean_object* v_i_1512_, lean_object* v_xs_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_info_1518_, lean_object* v_fixed_1519_, lean_object* v_used_1520_, lean_object* v_body_1521_, lean_object* v_toBind_1522_, lean_object* v_withNewLemmas_1523_, lean_object* v_val_1524_, uint8_t v___x_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_toMonadRef_1528_, lean_object* v___x_1529_, lean_object* v_val_x27_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___f_1534_; lean_object* v_cls_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1531_ = lean_box(v___y_1505_);
v___x_1532_ = lean_box(v___x_1509_);
v___x_1533_ = lean_box(v___x_1525_);
lean_inc_ref(v_val_1524_);
lean_inc_ref(v_val_x27_1530_);
lean_inc(v_toBind_1522_);
lean_inc(v_inst_1515_);
lean_inc(v_declName_1502_);
v___f_1534_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 26, 25);
lean_closure_set(v___f_1534_, 0, v_declName_1502_);
lean_closure_set(v___f_1534_, 1, v_type_1503_);
lean_closure_set(v___f_1534_, 2, v_value_1504_);
lean_closure_set(v___f_1534_, 3, v___x_1531_);
lean_closure_set(v___f_1534_, 4, v___x_1506_);
lean_closure_set(v___f_1534_, 5, v_toPure_1507_);
lean_closure_set(v___f_1534_, 6, v_us_1508_);
lean_closure_set(v___f_1534_, 7, v___x_1532_);
lean_closure_set(v___f_1534_, 8, v_decl_1510_);
lean_closure_set(v___f_1534_, 9, v_x_1511_);
lean_closure_set(v___f_1534_, 10, v_i_1512_);
lean_closure_set(v___f_1534_, 11, v_xs_1513_);
lean_closure_set(v___f_1534_, 12, v_inst_1514_);
lean_closure_set(v___f_1534_, 13, v_inst_1515_);
lean_closure_set(v___f_1534_, 14, v_inst_1516_);
lean_closure_set(v___f_1534_, 15, v_inst_1517_);
lean_closure_set(v___f_1534_, 16, v_info_1518_);
lean_closure_set(v___f_1534_, 17, v_fixed_1519_);
lean_closure_set(v___f_1534_, 18, v_used_1520_);
lean_closure_set(v___f_1534_, 19, v_body_1521_);
lean_closure_set(v___f_1534_, 20, v_toBind_1522_);
lean_closure_set(v___f_1534_, 21, v_withNewLemmas_1523_);
lean_closure_set(v___f_1534_, 22, v_val_x27_1530_);
lean_closure_set(v___f_1534_, 23, v_val_1524_);
lean_closure_set(v___f_1534_, 24, v___x_1533_);
v_cls_1535_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1536_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1536_, 0, v_cls_1535_);
lean_closure_set(v___f_1536_, 1, v_declName_1502_);
lean_closure_set(v___f_1536_, 2, v_val_1524_);
lean_closure_set(v___f_1536_, 3, v_val_x27_1530_);
lean_closure_set(v___f_1536_, 4, v___x_1526_);
lean_closure_set(v___f_1536_, 5, v___x_1527_);
lean_closure_set(v___f_1536_, 6, v_toMonadRef_1528_);
lean_closure_set(v___f_1536_, 7, v___x_1529_);
v___x_1537_ = lean_apply_2(v_inst_1515_, lean_box(0), v___f_1536_);
v___x_1538_ = lean_apply_4(v_toBind_1522_, lean_box(0), lean_box(0), v___x_1537_, v___f_1534_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1539_ = _args[0];
lean_object* v_type_1540_ = _args[1];
lean_object* v_value_1541_ = _args[2];
lean_object* v___y_1542_ = _args[3];
lean_object* v___x_1543_ = _args[4];
lean_object* v_toPure_1544_ = _args[5];
lean_object* v_us_1545_ = _args[6];
lean_object* v___x_1546_ = _args[7];
lean_object* v_decl_1547_ = _args[8];
lean_object* v_x_1548_ = _args[9];
lean_object* v_i_1549_ = _args[10];
lean_object* v_xs_1550_ = _args[11];
lean_object* v_inst_1551_ = _args[12];
lean_object* v_inst_1552_ = _args[13];
lean_object* v_inst_1553_ = _args[14];
lean_object* v_inst_1554_ = _args[15];
lean_object* v_info_1555_ = _args[16];
lean_object* v_fixed_1556_ = _args[17];
lean_object* v_used_1557_ = _args[18];
lean_object* v_body_1558_ = _args[19];
lean_object* v_toBind_1559_ = _args[20];
lean_object* v_withNewLemmas_1560_ = _args[21];
lean_object* v_val_1561_ = _args[22];
lean_object* v___x_1562_ = _args[23];
lean_object* v___x_1563_ = _args[24];
lean_object* v___x_1564_ = _args[25];
lean_object* v_toMonadRef_1565_ = _args[26];
lean_object* v___x_1566_ = _args[27];
lean_object* v_val_x27_1567_ = _args[28];
_start:
{
uint8_t v___y_8811__boxed_1568_; uint8_t v___x_8813__boxed_1569_; uint8_t v___x_8819__boxed_1570_; lean_object* v_res_1571_; 
v___y_8811__boxed_1568_ = lean_unbox(v___y_1542_);
v___x_8813__boxed_1569_ = lean_unbox(v___x_1546_);
v___x_8819__boxed_1570_ = lean_unbox(v___x_1562_);
v_res_1571_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1539_, v_type_1540_, v_value_1541_, v___y_8811__boxed_1568_, v___x_1543_, v_toPure_1544_, v_us_1545_, v___x_8813__boxed_1569_, v_decl_1547_, v_x_1548_, v_i_1549_, v_xs_1550_, v_inst_1551_, v_inst_1552_, v_inst_1553_, v_inst_1554_, v_info_1555_, v_fixed_1556_, v_used_1557_, v_body_1558_, v_toBind_1559_, v_withNewLemmas_1560_, v_val_1561_, v___x_8819__boxed_1570_, v___x_1563_, v___x_1564_, v_toMonadRef_1565_, v___x_1566_, v_val_x27_1567_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1572_, lean_object* v_declName_1573_, lean_object* v_type_1574_, lean_object* v_value_1575_, uint8_t v___x_1576_, lean_object* v___x_1577_, uint8_t v___x_1578_, lean_object* v_toPure_1579_, lean_object* v_us_1580_, lean_object* v___x_1581_, lean_object* v_x_1582_, lean_object* v_i_1583_, lean_object* v_xs_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_info_1589_, lean_object* v_fixed_1590_, lean_object* v_used_1591_, lean_object* v_body_1592_, lean_object* v_toBind_1593_, lean_object* v_withNewLemmas_1594_, lean_object* v_____x_1595_){
_start:
{
lean_object* v_snd_1596_; lean_object* v_fst_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1619_; 
v_snd_1596_ = lean_ctor_get(v_____x_1595_, 1);
lean_inc(v_snd_1596_);
v_fst_1597_ = lean_ctor_get(v_____x_1595_, 0);
lean_inc(v_fst_1597_);
lean_dec_ref(v_____x_1595_);
v_fst_1598_ = lean_ctor_get(v_snd_1596_, 0);
v_snd_1599_ = lean_ctor_get(v_snd_1596_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_snd_1596_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1601_ = v_snd_1596_;
v_isShared_1602_ = v_isSharedCheck_1619_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snd_1599_);
lean_inc(v_fst_1598_);
lean_dec(v_snd_1596_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1619_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_box(0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 1);
lean_ctor_set(v___x_1601_, 1, v___x_1603_);
lean_ctor_set(v___x_1601_, 0, v_decl_1572_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_decl_1572_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_box(v___x_1576_);
v___x_1608_ = lean_box(v___x_1578_);
v___f_1609_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 14, 13);
lean_closure_set(v___f_1609_, 0, v_declName_1573_);
lean_closure_set(v___f_1609_, 1, v_type_1574_);
lean_closure_set(v___f_1609_, 2, v_fst_1597_);
lean_closure_set(v___f_1609_, 3, v___x_1606_);
lean_closure_set(v___f_1609_, 4, v_value_1575_);
lean_closure_set(v___f_1609_, 5, v___x_1607_);
lean_closure_set(v___f_1609_, 6, v_fst_1598_);
lean_closure_set(v___f_1609_, 7, v___x_1577_);
lean_closure_set(v___f_1609_, 8, v___x_1608_);
lean_closure_set(v___f_1609_, 9, v_toPure_1579_);
lean_closure_set(v___f_1609_, 10, v_us_1580_);
lean_closure_set(v___f_1609_, 11, v_snd_1599_);
lean_closure_set(v___f_1609_, 12, v___x_1581_);
v___x_1610_ = lean_mk_empty_array_with_capacity(v___x_1606_);
lean_inc_ref(v_x_1582_);
v___x_1611_ = lean_array_push(v___x_1610_, v_x_1582_);
v___x_1612_ = lean_nat_add(v_i_1583_, v___x_1606_);
v___x_1613_ = lean_array_push(v_xs_1584_, v_x_1582_);
lean_inc_ref(v_inst_1587_);
lean_inc_ref(v_inst_1585_);
v___x_1614_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1585_, v_inst_1586_, v_inst_1587_, v_inst_1588_, v_info_1589_, v_fixed_1590_, v_used_1591_, v_body_1592_, v___x_1612_, v___x_1613_);
v___x_1615_ = lean_apply_4(v_toBind_1593_, lean_box(0), lean_box(0), v___x_1614_, v___f_1609_);
v___x_1616_ = lean_apply_3(v_withNewLemmas_1594_, lean_box(0), v___x_1611_, v___x_1615_);
v___x_1617_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1587_, v_inst_1585_, v___x_1605_, v___x_1616_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1620_ = _args[0];
lean_object* v_declName_1621_ = _args[1];
lean_object* v_type_1622_ = _args[2];
lean_object* v_value_1623_ = _args[3];
lean_object* v___x_1624_ = _args[4];
lean_object* v___x_1625_ = _args[5];
lean_object* v___x_1626_ = _args[6];
lean_object* v_toPure_1627_ = _args[7];
lean_object* v_us_1628_ = _args[8];
lean_object* v___x_1629_ = _args[9];
lean_object* v_x_1630_ = _args[10];
lean_object* v_i_1631_ = _args[11];
lean_object* v_xs_1632_ = _args[12];
lean_object* v_inst_1633_ = _args[13];
lean_object* v_inst_1634_ = _args[14];
lean_object* v_inst_1635_ = _args[15];
lean_object* v_inst_1636_ = _args[16];
lean_object* v_info_1637_ = _args[17];
lean_object* v_fixed_1638_ = _args[18];
lean_object* v_used_1639_ = _args[19];
lean_object* v_body_1640_ = _args[20];
lean_object* v_toBind_1641_ = _args[21];
lean_object* v_withNewLemmas_1642_ = _args[22];
lean_object* v_____x_1643_ = _args[23];
_start:
{
uint8_t v___x_8835__boxed_1644_; uint8_t v___x_8837__boxed_1645_; lean_object* v_res_1646_; 
v___x_8835__boxed_1644_ = lean_unbox(v___x_1624_);
v___x_8837__boxed_1645_ = lean_unbox(v___x_1626_);
v_res_1646_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1620_, v_declName_1621_, v_type_1622_, v_value_1623_, v___x_8835__boxed_1644_, v___x_1625_, v___x_8837__boxed_1645_, v_toPure_1627_, v_us_1628_, v___x_1629_, v_x_1630_, v_i_1631_, v_xs_1632_, v_inst_1633_, v_inst_1634_, v_inst_1635_, v_inst_1636_, v_info_1637_, v_fixed_1638_, v_used_1639_, v_body_1640_, v_toBind_1641_, v_withNewLemmas_1642_, v_____x_1643_);
lean_dec(v_i_1631_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1647_ = _args[0];
lean_object* v_declName_1648_ = _args[1];
lean_object* v_type_1649_ = _args[2];
lean_object* v_value_1650_ = _args[3];
lean_object* v_us_1651_ = _args[4];
lean_object* v___x_1652_ = _args[5];
lean_object* v___x_1653_ = _args[6];
lean_object* v_toPure_1654_ = _args[7];
lean_object* v_i_1655_ = _args[8];
lean_object* v_xs_1656_ = _args[9];
lean_object* v_inst_1657_ = _args[10];
lean_object* v_inst_1658_ = _args[11];
lean_object* v_inst_1659_ = _args[12];
lean_object* v_inst_1660_ = _args[13];
lean_object* v_info_1661_ = _args[14];
lean_object* v_fixed_1662_ = _args[15];
lean_object* v_used_1663_ = _args[16];
lean_object* v_body_1664_ = _args[17];
lean_object* v_toBind_1665_ = _args[18];
lean_object* v_____r_1666_ = _args[19];
_start:
{
uint8_t v___x_8794__boxed_1667_; lean_object* v_res_1668_; 
v___x_8794__boxed_1667_ = lean_unbox(v___x_1653_);
v_res_1668_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1647_, v_declName_1648_, v_type_1649_, v_value_1650_, v_us_1651_, v___x_1652_, v___x_8794__boxed_1667_, v_toPure_1654_, v_i_1655_, v_xs_1656_, v_inst_1657_, v_inst_1658_, v_inst_1659_, v_inst_1660_, v_info_1661_, v_fixed_1662_, v_used_1663_, v_body_1664_, v_toBind_1665_, v_____r_1666_);
lean_dec(v_i_1655_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_info_1673_, lean_object* v_fixed_1674_, lean_object* v_used_1675_, lean_object* v_e_1676_, lean_object* v_i_1677_, lean_object* v_xs_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v_toApplicative_1680_; lean_object* v_toFunctor_1681_; lean_object* v_toSeq_1682_; lean_object* v_toSeqLeft_1683_; lean_object* v_toSeqRight_1684_; lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_toApplicative_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1797_; 
v___x_1679_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v_toApplicative_1680_ = lean_ctor_get(v___x_1679_, 0);
v_toFunctor_1681_ = lean_ctor_get(v_toApplicative_1680_, 0);
v_toSeq_1682_ = lean_ctor_get(v_toApplicative_1680_, 2);
v_toSeqLeft_1683_ = lean_ctor_get(v_toApplicative_1680_, 3);
v_toSeqRight_1684_ = lean_ctor_get(v_toApplicative_1680_, 4);
v___f_1685_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2));
v___f_1686_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1681_, 2);
v___f_1687_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1687_, 0, v_toFunctor_1681_);
v___f_1688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1688_, 0, v_toFunctor_1681_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___f_1687_);
lean_ctor_set(v___x_1689_, 1, v___f_1688_);
lean_inc(v_toSeqRight_1684_);
v___f_1690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1690_, 0, v_toSeqRight_1684_);
lean_inc(v_toSeqLeft_1683_);
v___f_1691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1691_, 0, v_toSeqLeft_1683_);
lean_inc(v_toSeq_1682_);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toSeq_1682_);
v___x_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1689_);
lean_ctor_set(v___x_1693_, 1, v___f_1685_);
lean_ctor_set(v___x_1693_, 2, v___f_1692_);
lean_ctor_set(v___x_1693_, 3, v___f_1691_);
lean_ctor_set(v___x_1693_, 4, v___f_1690_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___f_1686_);
v___x_1695_ = l_StateRefT_x27_instMonad___redArg(v___x_1694_);
v_toApplicative_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1695_, 1);
lean_dec(v_unused_1798_);
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1797_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_toApplicative_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1797_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_toFunctor_1700_; lean_object* v_toSeq_1701_; lean_object* v_toSeqLeft_1702_; lean_object* v_toSeqRight_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1795_; 
v_toFunctor_1700_ = lean_ctor_get(v_toApplicative_1696_, 0);
v_toSeq_1701_ = lean_ctor_get(v_toApplicative_1696_, 2);
v_toSeqLeft_1702_ = lean_ctor_get(v_toApplicative_1696_, 3);
v_toSeqRight_1703_ = lean_ctor_get(v_toApplicative_1696_, 4);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_toApplicative_1696_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v_toApplicative_1696_, 1);
lean_dec(v_unused_1796_);
v___x_1705_ = v_toApplicative_1696_;
v_isShared_1706_ = v_isSharedCheck_1795_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_toSeqRight_1703_);
lean_inc(v_toSeqLeft_1702_);
lean_inc(v_toSeq_1701_);
lean_inc(v_toFunctor_1700_);
lean_dec(v_toApplicative_1696_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1795_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___x_1716_; 
v___f_1707_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4));
v___f_1708_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5));
lean_inc_ref(v_toFunctor_1700_);
v___f_1709_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1709_, 0, v_toFunctor_1700_);
v___f_1710_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1710_, 0, v_toFunctor_1700_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___f_1709_);
lean_ctor_set(v___x_1711_, 1, v___f_1710_);
v___f_1712_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1712_, 0, v_toSeqRight_1703_);
v___f_1713_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1713_, 0, v_toSeqLeft_1702_);
v___f_1714_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1714_, 0, v_toSeq_1701_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 4, v___f_1712_);
lean_ctor_set(v___x_1705_, 3, v___f_1713_);
lean_ctor_set(v___x_1705_, 2, v___f_1714_);
lean_ctor_set(v___x_1705_, 1, v___f_1707_);
lean_ctor_set(v___x_1705_, 0, v___x_1711_);
v___x_1716_ = v___x_1705_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___f_1707_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v___f_1714_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v___f_1713_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v___f_1712_);
v___x_1716_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___f_1708_);
lean_ctor_set(v___x_1698_, 0, v___x_1716_);
v___x_1718_ = v___x_1698_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___f_1708_);
v___x_1718_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_toApplicative_1721_; lean_object* v_toMonadRef_1722_; lean_object* v_haveInfo_1723_; lean_object* v_body_1724_; lean_object* v_bodyType_1725_; lean_object* v_level_1726_; lean_object* v_toBind_1727_; lean_object* v_toPure_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1719_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9);
v___x_1720_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13);
v_toApplicative_1721_ = lean_ctor_get(v_inst_1669_, 0);
v_toMonadRef_1722_ = lean_ctor_get(v___x_1720_, 0);
v_haveInfo_1723_ = lean_ctor_get(v_info_1673_, 0);
v_body_1724_ = lean_ctor_get(v_info_1673_, 3);
v_bodyType_1725_ = lean_ctor_get(v_info_1673_, 4);
v_level_1726_ = lean_ctor_get(v_info_1673_, 5);
v_toBind_1727_ = lean_ctor_get(v_inst_1669_, 1);
lean_inc(v_toBind_1727_);
v_toPure_1728_ = lean_ctor_get(v_toApplicative_1721_, 1);
lean_inc(v_toPure_1728_);
v___x_1729_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1730_ = lean_array_get_size(v_haveInfo_1723_);
v___x_1731_ = lean_nat_dec_lt(v_i_1677_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___f_1733_; lean_object* v_cls_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc(v_level_1726_);
lean_inc_ref(v_bodyType_1725_);
lean_inc_ref_n(v_body_1724_, 2);
lean_dec(v_i_1677_);
lean_dec_ref(v_used_1675_);
lean_dec_ref(v_fixed_1674_);
lean_dec_ref(v_info_1673_);
lean_dec_ref(v_inst_1671_);
lean_dec_ref(v_inst_1669_);
v___x_1732_ = lean_box(v___x_1731_);
lean_inc(v_toBind_1727_);
v___f_1733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1733_, 0, v_inst_1672_);
lean_closure_set(v___f_1733_, 1, v_bodyType_1725_);
lean_closure_set(v___f_1733_, 2, v_xs_1678_);
lean_closure_set(v___f_1733_, 3, v_level_1726_);
lean_closure_set(v___f_1733_, 4, v_e_1676_);
lean_closure_set(v___f_1733_, 5, v___x_1732_);
lean_closure_set(v___f_1733_, 6, v_toPure_1728_);
lean_closure_set(v___f_1733_, 7, v_body_1724_);
lean_closure_set(v___f_1733_, 8, v_toBind_1727_);
v_cls_1734_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1722_);
v___f_1735_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1735_, 0, v_cls_1734_);
lean_closure_set(v___f_1735_, 1, v_body_1724_);
lean_closure_set(v___f_1735_, 2, v___x_1718_);
lean_closure_set(v___f_1735_, 3, v___x_1719_);
lean_closure_set(v___f_1735_, 4, v_toMonadRef_1722_);
lean_closure_set(v___f_1735_, 5, v___x_1729_);
v___x_1736_ = lean_apply_2(v_inst_1670_, lean_box(0), v___f_1735_);
v___x_1737_ = lean_apply_4(v_toBind_1727_, lean_box(0), lean_box(0), v___x_1736_, v___f_1733_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
lean_inc_ref(v_inst_1669_);
v___x_1739_ = l_instInhabitedOfMonad___redArg(v_inst_1669_, v___x_1738_);
if (lean_obj_tag(v_e_1676_) == 8)
{
uint8_t v_nondep_1743_; 
v_nondep_1743_ = lean_ctor_get_uint8(v_e_1676_, sizeof(void*)*4 + 8);
if (v_nondep_1743_ == 1)
{
lean_object* v_declName_1744_; lean_object* v_type_1745_; lean_object* v_value_1746_; lean_object* v_body_1747_; lean_object* v_hinfo_1748_; lean_object* v_decl_1749_; lean_object* v_level_1750_; lean_object* v_x_1751_; lean_object* v_val_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_us_1755_; uint8_t v___y_1757_; uint8_t v___y_1758_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_declName_1744_ = lean_ctor_get(v_e_1676_, 0);
lean_inc(v_declName_1744_);
v_type_1745_ = lean_ctor_get(v_e_1676_, 1);
lean_inc_ref(v_type_1745_);
v_value_1746_ = lean_ctor_get(v_e_1676_, 2);
lean_inc_ref(v_value_1746_);
v_body_1747_ = lean_ctor_get(v_e_1676_, 3);
lean_inc_ref(v_body_1747_);
lean_dec_ref_known(v_e_1676_, 4);
v_hinfo_1748_ = lean_array_fget_borrowed(v_haveInfo_1723_, v_i_1677_);
v_decl_1749_ = lean_ctor_get(v_hinfo_1748_, 2);
v_level_1750_ = lean_ctor_get(v_hinfo_1748_, 3);
lean_inc_ref(v_decl_1749_);
v_x_1751_ = l_Lean_LocalDecl_toExpr(v_decl_1749_);
v_val_1752_ = l_Lean_LocalDecl_value(v_decl_1749_, v___x_1731_);
v___x_1753_ = lean_box(0);
lean_inc(v_level_1726_);
v___x_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_level_1726_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_inc_ref(v___x_1754_);
lean_inc(v_level_1750_);
v_us_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1755_, 0, v_level_1750_);
lean_ctor_set(v_us_1755_, 1, v___x_1754_);
v___x_1783_ = lean_array_get_size(v_used_1675_);
v___x_1784_ = lean_nat_dec_lt(v_i_1677_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_inc_ref(v_decl_1749_);
goto v___jp_1767_;
}
else
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_array_fget_borrowed(v_used_1675_, v_i_1677_);
v___x_1786_ = lean_unbox(v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v_cls_1789_; lean_object* v___f_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec_ref(v_x_1751_);
lean_dec(v___x_1739_);
v___x_1787_ = lean_box(v___x_1731_);
lean_inc(v_toBind_1727_);
lean_inc(v_inst_1670_);
lean_inc(v_declName_1744_);
v___f_1788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1788_, 0, v___x_1753_);
lean_closure_set(v___f_1788_, 1, v_declName_1744_);
lean_closure_set(v___f_1788_, 2, v_type_1745_);
lean_closure_set(v___f_1788_, 3, v_value_1746_);
lean_closure_set(v___f_1788_, 4, v_us_1755_);
lean_closure_set(v___f_1788_, 5, v___x_1754_);
lean_closure_set(v___f_1788_, 6, v___x_1787_);
lean_closure_set(v___f_1788_, 7, v_toPure_1728_);
lean_closure_set(v___f_1788_, 8, v_i_1677_);
lean_closure_set(v___f_1788_, 9, v_xs_1678_);
lean_closure_set(v___f_1788_, 10, v_inst_1669_);
lean_closure_set(v___f_1788_, 11, v_inst_1670_);
lean_closure_set(v___f_1788_, 12, v_inst_1671_);
lean_closure_set(v___f_1788_, 13, v_inst_1672_);
lean_closure_set(v___f_1788_, 14, v_info_1673_);
lean_closure_set(v___f_1788_, 15, v_fixed_1674_);
lean_closure_set(v___f_1788_, 16, v_used_1675_);
lean_closure_set(v___f_1788_, 17, v_body_1747_);
lean_closure_set(v___f_1788_, 18, v_toBind_1727_);
v_cls_1789_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1722_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1790_, 0, v_cls_1789_);
lean_closure_set(v___f_1790_, 1, v_declName_1744_);
lean_closure_set(v___f_1790_, 2, v_val_1752_);
lean_closure_set(v___f_1790_, 3, v___x_1718_);
lean_closure_set(v___f_1790_, 4, v___x_1719_);
lean_closure_set(v___f_1790_, 5, v_toMonadRef_1722_);
lean_closure_set(v___f_1790_, 6, v___x_1729_);
v___x_1791_ = lean_apply_2(v_inst_1670_, lean_box(0), v___f_1790_);
v___x_1792_ = lean_apply_4(v_toBind_1727_, lean_box(0), lean_box(0), v___x_1791_, v___f_1788_);
return v___x_1792_;
}
else
{
lean_inc_ref(v_decl_1749_);
goto v___jp_1767_;
}
}
v___jp_1756_:
{
lean_object* v_withNewLemmas_1759_; lean_object* v_dsimp_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_withNewLemmas_1759_ = lean_ctor_get(v_inst_1672_, 0);
lean_inc(v_withNewLemmas_1759_);
v_dsimp_1760_ = lean_ctor_get(v_inst_1672_, 1);
lean_inc(v_dsimp_1760_);
v___x_1761_ = lean_box(v___y_1758_);
v___x_1762_ = lean_box(v___x_1731_);
v___x_1763_ = lean_box(v___y_1757_);
lean_inc_ref(v_toMonadRef_1722_);
lean_inc_ref(v_val_1752_);
lean_inc(v_toBind_1727_);
v___f_1764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 29, 28);
lean_closure_set(v___f_1764_, 0, v_declName_1744_);
lean_closure_set(v___f_1764_, 1, v_type_1745_);
lean_closure_set(v___f_1764_, 2, v_value_1746_);
lean_closure_set(v___f_1764_, 3, v___x_1761_);
lean_closure_set(v___f_1764_, 4, v___x_1754_);
lean_closure_set(v___f_1764_, 5, v_toPure_1728_);
lean_closure_set(v___f_1764_, 6, v_us_1755_);
lean_closure_set(v___f_1764_, 7, v___x_1762_);
lean_closure_set(v___f_1764_, 8, v_decl_1749_);
lean_closure_set(v___f_1764_, 9, v_x_1751_);
lean_closure_set(v___f_1764_, 10, v_i_1677_);
lean_closure_set(v___f_1764_, 11, v_xs_1678_);
lean_closure_set(v___f_1764_, 12, v_inst_1669_);
lean_closure_set(v___f_1764_, 13, v_inst_1670_);
lean_closure_set(v___f_1764_, 14, v_inst_1671_);
lean_closure_set(v___f_1764_, 15, v_inst_1672_);
lean_closure_set(v___f_1764_, 16, v_info_1673_);
lean_closure_set(v___f_1764_, 17, v_fixed_1674_);
lean_closure_set(v___f_1764_, 18, v_used_1675_);
lean_closure_set(v___f_1764_, 19, v_body_1747_);
lean_closure_set(v___f_1764_, 20, v_toBind_1727_);
lean_closure_set(v___f_1764_, 21, v_withNewLemmas_1759_);
lean_closure_set(v___f_1764_, 22, v_val_1752_);
lean_closure_set(v___f_1764_, 23, v___x_1763_);
lean_closure_set(v___f_1764_, 24, v___x_1718_);
lean_closure_set(v___f_1764_, 25, v___x_1719_);
lean_closure_set(v___f_1764_, 26, v_toMonadRef_1722_);
lean_closure_set(v___f_1764_, 27, v___x_1729_);
v___x_1765_ = lean_apply_1(v_dsimp_1760_, v_val_1752_);
v___x_1766_ = lean_apply_4(v_toBind_1727_, lean_box(0), lean_box(0), v___x_1765_, v___f_1764_);
return v___x_1766_;
}
v___jp_1767_:
{
uint8_t v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = 0;
v___x_1769_ = lean_array_get_size(v_fixed_1674_);
v___x_1770_ = lean_nat_dec_lt(v_i_1677_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec(v___x_1739_);
v___y_1757_ = v___x_1768_;
v___y_1758_ = v___x_1731_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_fget_borrowed(v_fixed_1674_, v_i_1677_);
v___x_1772_ = lean_unbox(v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v_withNewLemmas_1773_; lean_object* v_simp_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___f_1777_; lean_object* v___x_1778_; lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_inc_n(v___x_1771_, 2);
lean_inc(v_level_1750_);
v_withNewLemmas_1773_ = lean_ctor_get(v_inst_1672_, 0);
lean_inc(v_withNewLemmas_1773_);
v_simp_1774_ = lean_ctor_get(v_inst_1672_, 2);
lean_inc(v_simp_1774_);
v___x_1775_ = lean_box(v___x_1731_);
lean_inc_n(v_toBind_1727_, 2);
lean_inc(v_inst_1670_);
lean_inc_ref(v_xs_1678_);
lean_inc(v_toPure_1728_);
lean_inc_ref(v_value_1746_);
lean_inc_ref(v_type_1745_);
lean_inc(v_declName_1744_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 24, 23);
lean_closure_set(v___f_1776_, 0, v_decl_1749_);
lean_closure_set(v___f_1776_, 1, v_declName_1744_);
lean_closure_set(v___f_1776_, 2, v_type_1745_);
lean_closure_set(v___f_1776_, 3, v_value_1746_);
lean_closure_set(v___f_1776_, 4, v___x_1775_);
lean_closure_set(v___f_1776_, 5, v___x_1754_);
lean_closure_set(v___f_1776_, 6, v___x_1771_);
lean_closure_set(v___f_1776_, 7, v_toPure_1728_);
lean_closure_set(v___f_1776_, 8, v_us_1755_);
lean_closure_set(v___f_1776_, 9, v___x_1739_);
lean_closure_set(v___f_1776_, 10, v_x_1751_);
lean_closure_set(v___f_1776_, 11, v_i_1677_);
lean_closure_set(v___f_1776_, 12, v_xs_1678_);
lean_closure_set(v___f_1776_, 13, v_inst_1669_);
lean_closure_set(v___f_1776_, 14, v_inst_1670_);
lean_closure_set(v___f_1776_, 15, v_inst_1671_);
lean_closure_set(v___f_1776_, 16, v_inst_1672_);
lean_closure_set(v___f_1776_, 17, v_info_1673_);
lean_closure_set(v___f_1776_, 18, v_fixed_1674_);
lean_closure_set(v___f_1776_, 19, v_used_1675_);
lean_closure_set(v___f_1776_, 20, v_body_1747_);
lean_closure_set(v___f_1776_, 21, v_toBind_1727_);
lean_closure_set(v___f_1776_, 22, v_withNewLemmas_1773_);
v___f_1777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1777_, 0, v___f_1776_);
v___x_1778_ = lean_box(v___x_1731_);
lean_inc_ref(v_toMonadRef_1722_);
lean_inc_ref(v_val_1752_);
lean_inc_ref(v___f_1777_);
v___f_1779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_1779_, 0, v_level_1750_);
lean_closure_set(v___f_1779_, 1, v___x_1753_);
lean_closure_set(v___f_1779_, 2, v_type_1745_);
lean_closure_set(v___f_1779_, 3, v_value_1746_);
lean_closure_set(v___f_1779_, 4, v___x_1771_);
lean_closure_set(v___f_1779_, 5, v_toPure_1728_);
lean_closure_set(v___f_1779_, 6, v_toBind_1727_);
lean_closure_set(v___f_1779_, 7, v___f_1777_);
lean_closure_set(v___f_1779_, 8, v_xs_1678_);
lean_closure_set(v___f_1779_, 9, v___x_1778_);
lean_closure_set(v___f_1779_, 10, v___f_1777_);
lean_closure_set(v___f_1779_, 11, v_declName_1744_);
lean_closure_set(v___f_1779_, 12, v_val_1752_);
lean_closure_set(v___f_1779_, 13, v___x_1718_);
lean_closure_set(v___f_1779_, 14, v___x_1719_);
lean_closure_set(v___f_1779_, 15, v_toMonadRef_1722_);
lean_closure_set(v___f_1779_, 16, v___x_1729_);
lean_closure_set(v___f_1779_, 17, v_inst_1670_);
v___x_1780_ = lean_apply_1(v_simp_1774_, v_val_1752_);
v___x_1781_ = lean_apply_4(v_toBind_1727_, lean_box(0), lean_box(0), v___x_1780_, v___f_1779_);
return v___x_1781_;
}
else
{
uint8_t v___x_1782_; 
lean_dec(v___x_1739_);
v___x_1782_ = lean_unbox(v___x_1771_);
v___y_1757_ = v___x_1768_;
v___y_1758_ = v___x_1782_;
goto v___jp_1756_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1676_, 4);
lean_dec(v_toPure_1728_);
lean_dec(v_toBind_1727_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v_xs_1678_);
lean_dec(v_i_1677_);
lean_dec_ref(v_used_1675_);
lean_dec_ref(v_fixed_1674_);
lean_dec_ref(v_info_1673_);
lean_dec_ref(v_inst_1672_);
lean_dec_ref(v_inst_1671_);
lean_dec(v_inst_1670_);
lean_dec_ref(v_inst_1669_);
goto v___jp_1740_;
}
}
else
{
lean_dec(v_toPure_1728_);
lean_dec(v_toBind_1727_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v_xs_1678_);
lean_dec(v_i_1677_);
lean_dec_ref(v_e_1676_);
lean_dec_ref(v_used_1675_);
lean_dec_ref(v_fixed_1674_);
lean_dec_ref(v_info_1673_);
lean_dec_ref(v_inst_1672_);
lean_dec_ref(v_inst_1671_);
lean_dec(v_inst_1670_);
lean_dec_ref(v_inst_1669_);
goto v___jp_1740_;
}
v___jp_1740_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15);
v___x_1742_ = l_panic___redArg(v___x_1739_, v___x_1741_);
lean_dec(v___x_1739_);
return v___x_1742_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1799_, lean_object* v_declName_1800_, lean_object* v_type_1801_, lean_object* v_value_1802_, lean_object* v_us_1803_, lean_object* v___x_1804_, uint8_t v___x_1805_, lean_object* v_toPure_1806_, lean_object* v_i_1807_, lean_object* v_xs_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_info_1813_, lean_object* v_fixed_1814_, lean_object* v_used_1815_, lean_object* v_body_1816_, lean_object* v_toBind_1817_, lean_object* v_____r_1818_){
_start:
{
lean_object* v___x_1819_; lean_object* v_x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___f_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1820_ = l_Lean_mkConst(v___x_1819_, v___x_1799_);
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_box(v___x_1805_);
v___f_1823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1823_, 0, v___x_1821_);
lean_closure_set(v___f_1823_, 1, v_declName_1800_);
lean_closure_set(v___f_1823_, 2, v_type_1801_);
lean_closure_set(v___f_1823_, 3, v_value_1802_);
lean_closure_set(v___f_1823_, 4, v_us_1803_);
lean_closure_set(v___f_1823_, 5, v___x_1804_);
lean_closure_set(v___f_1823_, 6, v___x_1822_);
lean_closure_set(v___f_1823_, 7, v_toPure_1806_);
v___x_1824_ = lean_nat_add(v_i_1807_, v___x_1821_);
v___x_1825_ = lean_array_push(v_xs_1808_, v_x_1820_);
v___x_1826_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1809_, v_inst_1810_, v_inst_1811_, v_inst_1812_, v_info_1813_, v_fixed_1814_, v_used_1815_, v_body_1816_, v___x_1824_, v___x_1825_);
v___x_1827_ = lean_apply_4(v_toBind_1817_, lean_box(0), lean_box(0), v___x_1826_, v___f_1823_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_info_1833_, lean_object* v_fixed_1834_, lean_object* v_used_1835_, lean_object* v_e_1836_, lean_object* v_i_1837_, lean_object* v_xs_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v_info_1833_, v_fixed_1834_, v_used_1835_, v_e_1836_, v_i_1837_, v_xs_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_1840_){
_start:
{
switch(v_x_1840_)
{
case 0:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_unsigned_to_nat(0u);
return v___x_1841_;
}
case 1:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_unsigned_to_nat(1u);
return v___x_1842_;
}
default: 
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_unsigned_to_nat(2u);
return v___x_1843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_1844_){
_start:
{
uint8_t v_x_boxed_1845_; lean_object* v_res_1846_; 
v_x_boxed_1845_ = lean_unbox(v_x_1844_);
v_res_1846_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_1845_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_1847_){
_start:
{
lean_inc(v_k_1847_);
return v_k_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_1848_);
lean_dec(v_k_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_1850_, lean_object* v_ctorIdx_1851_, uint8_t v_t_1852_, lean_object* v_h_1853_, lean_object* v_k_1854_){
_start:
{
lean_inc(v_k_1854_);
return v_k_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_1855_, lean_object* v_ctorIdx_1856_, lean_object* v_t_1857_, lean_object* v_h_1858_, lean_object* v_k_1859_){
_start:
{
uint8_t v_t_boxed_1860_; lean_object* v_res_1861_; 
v_t_boxed_1860_ = lean_unbox(v_t_1857_);
v_res_1861_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_1855_, v_ctorIdx_1856_, v_t_boxed_1860_, v_h_1858_, v_k_1859_);
lean_dec(v_k_1859_);
lean_dec(v_ctorIdx_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_1862_){
_start:
{
lean_inc(v_no_1862_);
return v_no_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_1863_);
lean_dec(v_no_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_1865_, uint8_t v_t_1866_, lean_object* v_h_1867_, lean_object* v_no_1868_){
_start:
{
lean_inc(v_no_1868_);
return v_no_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_1869_, lean_object* v_t_1870_, lean_object* v_h_1871_, lean_object* v_no_1872_){
_start:
{
uint8_t v_t_boxed_1873_; lean_object* v_res_1874_; 
v_t_boxed_1873_ = lean_unbox(v_t_1870_);
v_res_1874_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_1869_, v_t_boxed_1873_, v_h_1871_, v_no_1872_);
lean_dec(v_no_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_1875_){
_start:
{
lean_inc(v_singlePass_1875_);
return v_singlePass_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_1876_);
lean_dec(v_singlePass_1876_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_1878_, uint8_t v_t_1879_, lean_object* v_h_1880_, lean_object* v_singlePass_1881_){
_start:
{
lean_inc(v_singlePass_1881_);
return v_singlePass_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_1882_, lean_object* v_t_1883_, lean_object* v_h_1884_, lean_object* v_singlePass_1885_){
_start:
{
uint8_t v_t_boxed_1886_; lean_object* v_res_1887_; 
v_t_boxed_1886_ = lean_unbox(v_t_1883_);
v_res_1887_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_1882_, v_t_boxed_1886_, v_h_1884_, v_singlePass_1885_);
lean_dec(v_singlePass_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_1888_){
_start:
{
lean_inc(v_twoPasses_1888_);
return v_twoPasses_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_1889_);
lean_dec(v_twoPasses_1889_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_1891_, uint8_t v_t_1892_, lean_object* v_h_1893_, lean_object* v_twoPasses_1894_){
_start:
{
lean_inc(v_twoPasses_1894_);
return v_twoPasses_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_1895_, lean_object* v_t_1896_, lean_object* v_h_1897_, lean_object* v_twoPasses_1898_){
_start:
{
uint8_t v_t_boxed_1899_; lean_object* v_res_1900_; 
v_t_boxed_1899_ = lean_unbox(v_t_1896_);
v_res_1900_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_1895_, v_t_boxed_1899_, v_h_1897_, v_twoPasses_1898_);
lean_dec(v_twoPasses_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_1901_, lean_object* v_b_1902_, lean_object* v_c_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; 
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
v___x_1909_ = lean_apply_7(v_k_1901_, v_b_1902_, v_c_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, lean_box(0));
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_1910_, lean_object* v_b_1911_, lean_object* v_c_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_1910_, v_b_1911_, v_c_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_1919_, lean_object* v_k_1920_, uint8_t v_cleanupAnnotations_1921_, uint8_t v_preserveNondepLet_1922_, uint8_t v_nondepLetOnly_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___f_1929_; uint8_t v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1929_, 0, v_k_1920_);
v___x_1930_ = 0;
v___x_1931_ = 1;
v___x_1932_ = lean_box(0);
v___x_1933_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1919_, v___x_1930_, v___x_1931_, v_preserveNondepLet_1922_, v_nondepLetOnly_1923_, v___x_1932_, v___f_1929_, v_cleanupAnnotations_1921_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_1950_, lean_object* v_k_1951_, lean_object* v_cleanupAnnotations_1952_, lean_object* v_preserveNondepLet_1953_, lean_object* v_nondepLetOnly_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1960_; uint8_t v_preserveNondepLet_boxed_1961_; uint8_t v_nondepLetOnly_boxed_1962_; lean_object* v_res_1963_; 
v_cleanupAnnotations_boxed_1960_ = lean_unbox(v_cleanupAnnotations_1952_);
v_preserveNondepLet_boxed_1961_ = lean_unbox(v_preserveNondepLet_1953_);
v_nondepLetOnly_boxed_1962_ = lean_unbox(v_nondepLetOnly_1954_);
v_res_1963_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1950_, v_k_1951_, v_cleanupAnnotations_boxed_1960_, v_preserveNondepLet_boxed_1961_, v_nondepLetOnly_boxed_1962_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_1964_, lean_object* v_e_1965_, lean_object* v_k_1966_, uint8_t v_cleanupAnnotations_1967_, uint8_t v_preserveNondepLet_1968_, uint8_t v_nondepLetOnly_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1965_, v_k_1966_, v_cleanupAnnotations_1967_, v_preserveNondepLet_1968_, v_nondepLetOnly_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_1976_, lean_object* v_e_1977_, lean_object* v_k_1978_, lean_object* v_cleanupAnnotations_1979_, lean_object* v_preserveNondepLet_1980_, lean_object* v_nondepLetOnly_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1987_; uint8_t v_preserveNondepLet_boxed_1988_; uint8_t v_nondepLetOnly_boxed_1989_; lean_object* v_res_1990_; 
v_cleanupAnnotations_boxed_1987_ = lean_unbox(v_cleanupAnnotations_1979_);
v_preserveNondepLet_boxed_1988_ = lean_unbox(v_preserveNondepLet_1980_);
v_nondepLetOnly_boxed_1989_ = lean_unbox(v_nondepLetOnly_1981_);
v_res_1990_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_1976_, v_e_1977_, v_k_1978_, v_cleanupAnnotations_boxed_1987_, v_preserveNondepLet_boxed_1988_, v_nondepLetOnly_boxed_1989_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_1991_, lean_object* v_a_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_snd_1997_; lean_object* v_fst_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2053_; 
v_snd_1997_ = lean_ctor_get(v_a_1992_, 1);
v_fst_1998_ = lean_ctor_get(v_a_1992_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2000_ = v_a_1992_;
v_isShared_2001_ = v_isSharedCheck_2053_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_snd_1997_);
lean_inc(v_fst_1998_);
lean_dec(v_a_1992_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2053_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2052_; 
v_fst_2002_ = lean_ctor_get(v_snd_1997_, 0);
v_snd_2003_ = lean_ctor_get(v_snd_1997_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_snd_1997_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2005_ = v_snd_1997_;
v_isShared_2006_ = v_isSharedCheck_2052_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_snd_1997_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2052_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_nat_dec_lt(v___x_2007_, v_snd_2003_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2010_; 
if (v_isShared_2006_ == 0)
{
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_fst_2002_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_snd_2003_);
v___x_2010_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2010_);
v___x_2012_ = v___x_2000_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_fst_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
}
else
{
lean_object* v_fvarSet_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_fvarSet_2016_ = lean_ctor_get(v_fst_1998_, 1);
v___x_2017_ = l_Lean_instInhabitedExpr;
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_sub(v_snd_2003_, v___x_2018_);
lean_dec(v_snd_2003_);
v___x_2020_ = lean_array_get_borrowed(v___x_2017_, v_xs_1991_, v___x_2019_);
v___x_2021_ = l_Lean_Expr_fvarId_x21(v___x_2020_);
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2021_, v_fvarSet_2016_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2024_; 
lean_dec(v___x_2021_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2019_);
v___x_2024_ = v___x_2005_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_fst_2002_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2019_);
v___x_2024_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2024_);
v___x_2026_ = v___x_2000_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_fst_1998_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
v_a_1992_ = v___x_2026_;
goto _start;
}
}
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_FVarId_getDecl___redArg(v___x_2021_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = l_Lean_LocalDecl_type(v_a_2031_);
v___x_2033_ = l_Lean_collectFVars(v_fst_1998_, v___x_2032_);
v___x_2034_ = l_Lean_LocalDecl_value(v_a_2031_, v___x_2008_);
lean_dec(v_a_2031_);
v___x_2035_ = l_Lean_collectFVars(v___x_2033_, v___x_2034_);
lean_inc(v___x_2020_);
v___x_2036_ = lean_array_push(v_fst_2002_, v___x_2020_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2019_);
lean_ctor_set(v___x_2005_, 0, v___x_2036_);
v___x_2038_ = v___x_2005_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2019_);
v___x_2038_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2038_);
lean_ctor_set(v___x_2000_, 0, v___x_2035_);
v___x_2040_ = v___x_2000_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v_a_1992_ = v___x_2040_;
goto _start;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v___x_2019_);
lean_del_object(v___x_2005_);
lean_dec(v_fst_2002_);
lean_del_object(v___x_2000_);
lean_dec(v_fst_1998_);
v_a_2044_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2030_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2030_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2054_, lean_object* v_a_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2054_, v_a_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v_xs_2054_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2061_, lean_object* v_e_2062_, lean_object* v_xs_2063_, lean_object* v_body_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_s_2073_; lean_object* v_i_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2070_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2061_);
lean_ctor_set(v___x_2072_, 2, v___x_2071_);
lean_inc_ref(v_body_2064_);
v_s_2073_ = l_Lean_collectFVars(v___x_2072_, v_body_2064_);
v_i_2074_ = lean_array_get_size(v_xs_2063_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2071_);
lean_ctor_set(v___x_2075_, 1, v_i_2074_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_s_2073_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2063_, v___x_2076_, v___y_2065_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2093_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2093_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2093_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_snd_2082_; lean_object* v_fst_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_snd_2082_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_snd_2082_);
lean_dec(v_a_2078_);
v_fst_2083_ = lean_ctor_get(v_snd_2082_, 0);
lean_inc(v_fst_2083_);
lean_dec(v_snd_2082_);
v___x_2084_ = lean_array_get_size(v_fst_2083_);
v___x_2085_ = lean_nat_dec_eq(v___x_2084_, v_i_2074_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; 
lean_del_object(v___x_2080_);
lean_dec_ref(v_e_2062_);
v___x_2086_ = 1;
v___x_2087_ = l_Array_reverse___redArg(v_fst_2083_);
v___x_2088_ = 1;
v___x_2089_ = l_Lean_Meta_mkLetFVars(v___x_2087_, v_body_2064_, v___x_2086_, v___x_2085_, v___x_2088_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v___x_2087_);
return v___x_2089_;
}
else
{
lean_object* v___x_2091_; 
lean_dec(v_fst_2083_);
lean_dec_ref(v_body_2064_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v_e_2062_);
v___x_2091_ = v___x_2080_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_e_2062_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref(v_body_2064_);
lean_dec_ref(v_e_2062_);
v_a_2094_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2077_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2077_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2102_, lean_object* v_e_2103_, lean_object* v_xs_2104_, lean_object* v_body_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2102_, v_e_2103_, v_xs_2104_, v_body_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v_xs_2104_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___f_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; 
v___x_2118_ = lean_box(1);
lean_inc_ref(v_e_2112_);
v___f_2119_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2119_, 0, v___x_2118_);
lean_closure_set(v___f_2119_, 1, v_e_2112_);
v___x_2120_ = 0;
v___x_2121_ = 1;
v___x_2122_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2112_, v___f_2119_, v___x_2120_, v___x_2121_, v___x_2120_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_zetaUnused(v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2130_, lean_object* v_inst_2131_, lean_object* v_a_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2130_, v_a_2132_, v___y_2133_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2139_, lean_object* v_inst_2140_, lean_object* v_a_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2139_, v_inst_2140_, v_a_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec_ref(v_xs_2139_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2152_, lean_object* v_source_2153_, lean_object* v_result_2154_, uint8_t v_keepUnused_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
uint8_t v_modified_2161_; 
v_modified_2161_ = lean_ctor_get_uint8(v_result_2154_, sizeof(void*)*5);
if (v_modified_2161_ == 0)
{
if (v_keepUnused_2155_ == 0)
{
lean_object* v_exprType_2162_; lean_object* v___x_2163_; 
v_exprType_2162_ = lean_ctor_get(v_result_2154_, 1);
lean_inc_ref(v_exprType_2162_);
lean_dec_ref(v_result_2154_);
lean_inc_ref(v_source_2153_);
v___x_2163_ = l_Lean_Meta_zetaUnused(v_source_2153_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2182_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2182_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2182_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_expr_eqv(v_a_2164_, v_source_2153_);
lean_dec_ref(v_source_2153_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_u_2152_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = l_Lean_mkConst(v___x_2169_, v___x_2171_);
lean_inc(v_a_2164_);
v___x_2173_ = l_Lean_mkAppB(v___x_2172_, v_exprType_2162_, v_a_2164_);
v___x_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_a_2164_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2174_);
v___x_2176_ = v___x_2166_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec(v_a_2164_);
lean_dec_ref(v_exprType_2162_);
lean_dec(v_u_2152_);
v___x_2178_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2178_);
v___x_2180_ = v___x_2166_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v_exprType_2162_);
lean_dec_ref(v_source_2153_);
lean_dec(v_u_2152_);
v_a_2183_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2163_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2163_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v_result_2154_);
lean_dec_ref(v_source_2153_);
lean_dec(v_u_2152_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
else
{
lean_object* v_expr_2193_; lean_object* v_exprType_2194_; lean_object* v_exprInit_2195_; lean_object* v_exprResult_2196_; lean_object* v_proof_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v_proof_2205_; 
v_expr_2193_ = lean_ctor_get(v_result_2154_, 0);
lean_inc_ref(v_expr_2193_);
v_exprType_2194_ = lean_ctor_get(v_result_2154_, 1);
lean_inc_ref_n(v_exprType_2194_, 3);
v_exprInit_2195_ = lean_ctor_get(v_result_2154_, 2);
lean_inc_ref(v_exprInit_2195_);
v_exprResult_2196_ = lean_ctor_get(v_result_2154_, 3);
lean_inc_ref_n(v_exprResult_2196_, 2);
v_proof_2197_ = lean_ctor_get(v_result_2154_, 4);
lean_inc_ref(v_proof_2197_);
lean_dec_ref(v_result_2154_);
v___x_2198_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_u_2152_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
lean_inc_ref(v___x_2200_);
v___x_2201_ = l_Lean_mkConst(v___x_2198_, v___x_2200_);
lean_inc_ref(v___x_2201_);
v___x_2202_ = l_Lean_mkApp3(v___x_2201_, v_exprType_2194_, v_exprInit_2195_, v_expr_2193_);
v___x_2203_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2197_, v___x_2202_);
lean_inc_ref(v_source_2153_);
v___x_2204_ = l_Lean_mkApp3(v___x_2201_, v_exprType_2194_, v_source_2153_, v_exprResult_2196_);
v_proof_2205_ = l_Lean_Meta_mkExpectedPropHint(v___x_2203_, v___x_2204_);
if (v_keepUnused_2155_ == 0)
{
lean_object* v___x_2206_; 
lean_inc_ref(v_exprResult_2196_);
v___x_2206_ = l_Lean_Meta_zetaUnused(v_exprResult_2196_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2226_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2226_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2226_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
uint8_t v___x_2211_; 
v___x_2211_ = lean_expr_eqv(v_a_2207_, v_exprResult_2196_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2200_);
v___x_2213_ = l_Lean_mkConst(v___x_2212_, v___x_2200_);
v___x_2214_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2215_ = l_Lean_mkConst(v___x_2214_, v___x_2200_);
lean_inc_n(v_a_2207_, 2);
lean_inc_ref(v_exprType_2194_);
v___x_2216_ = l_Lean_mkAppB(v___x_2215_, v_exprType_2194_, v_a_2207_);
v___x_2217_ = l_Lean_mkApp6(v___x_2213_, v_exprType_2194_, v_source_2153_, v_exprResult_2196_, v_a_2207_, v_proof_2205_, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_a_2207_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2218_);
v___x_2220_ = v___x_2209_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_dec(v_a_2207_);
lean_dec_ref_known(v___x_2200_, 2);
lean_dec_ref(v_exprType_2194_);
lean_dec_ref(v_source_2153_);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_exprResult_2196_);
lean_ctor_set(v___x_2222_, 1, v_proof_2205_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2222_);
v___x_2224_ = v___x_2209_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v_proof_2205_);
lean_dec_ref_known(v___x_2200_, 2);
lean_dec_ref(v_exprResult_2196_);
lean_dec_ref(v_exprType_2194_);
lean_dec_ref(v_source_2153_);
v_a_2227_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2206_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2206_);
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
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2200_, 2);
lean_dec_ref(v_exprType_2194_);
lean_dec_ref(v_source_2153_);
v___x_2235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_exprResult_2196_);
lean_ctor_set(v___x_2235_, 1, v_proof_2205_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2237_, lean_object* v_source_2238_, lean_object* v_result_2239_, lean_object* v_keepUnused_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v_keepUnused_boxed_2246_; lean_object* v_res_2247_; 
v_keepUnused_boxed_2246_ = lean_unbox(v_keepUnused_2240_);
v_res_2247_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2237_, v_source_2238_, v_result_2239_, v_keepUnused_boxed_2246_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2248_, lean_object* v_e_2249_, lean_object* v_inst_2250_, uint8_t v_zetaUnusedMode_2251_, uint8_t v___x_2252_, uint8_t v___x_2253_, lean_object* v_r_2254_){
_start:
{
uint8_t v___y_2256_; 
switch(v_zetaUnusedMode_2251_)
{
case 0:
{
v___y_2256_ = v___x_2252_;
goto v___jp_2255_;
}
case 1:
{
v___y_2256_ = v___x_2252_;
goto v___jp_2255_;
}
default: 
{
v___y_2256_ = v___x_2253_;
goto v___jp_2255_;
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_box(v___y_2256_);
v___x_2258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2258_, 0, v_level_2248_);
lean_closure_set(v___x_2258_, 1, v_e_2249_);
lean_closure_set(v___x_2258_, 2, v_r_2254_);
lean_closure_set(v___x_2258_, 3, v___x_2257_);
v___x_2259_ = lean_apply_2(v_inst_2250_, lean_box(0), v___x_2258_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2260_, lean_object* v_e_2261_, lean_object* v_inst_2262_, lean_object* v_zetaUnusedMode_2263_, lean_object* v___x_2264_, lean_object* v___x_2265_, lean_object* v_r_2266_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2267_; uint8_t v___x_286__boxed_2268_; uint8_t v___x_287__boxed_2269_; lean_object* v_res_2270_; 
v_zetaUnusedMode_boxed_2267_ = lean_unbox(v_zetaUnusedMode_2263_);
v___x_286__boxed_2268_ = lean_unbox(v___x_2264_);
v___x_287__boxed_2269_ = lean_unbox(v___x_2265_);
v_res_2270_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2260_, v_e_2261_, v_inst_2262_, v_zetaUnusedMode_boxed_2267_, v___x_286__boxed_2268_, v___x_287__boxed_2269_, v_r_2266_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2271_, lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_info_2276_, lean_object* v_e_2277_, lean_object* v___x_2278_, lean_object* v_toBind_2279_, lean_object* v___f_2280_, lean_object* v_____x_2281_){
_start:
{
lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_fst_2282_ = lean_ctor_get(v_____x_2281_, 0);
lean_inc(v_fst_2282_);
v_snd_2283_ = lean_ctor_get(v_____x_2281_, 1);
lean_inc(v_snd_2283_);
lean_dec_ref(v_____x_2281_);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2271_);
v___x_2285_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2272_, v_inst_2273_, v_inst_2274_, v_inst_2275_, v_info_2276_, v_fst_2282_, v_snd_2283_, v_e_2277_, v___x_2278_, v___x_2284_);
v___x_2286_ = lean_apply_4(v_toBind_2279_, lean_box(0), lean_box(0), v___x_2285_, v___f_2280_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_info_2292_, lean_object* v_e_2293_, lean_object* v___x_2294_, lean_object* v_toBind_2295_, lean_object* v___f_2296_, lean_object* v_____x_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2287_, v_inst_2288_, v_inst_2289_, v_inst_2290_, v_inst_2291_, v_info_2292_, v_e_2293_, v___x_2294_, v_toBind_2295_, v___f_2296_, v_____x_2297_);
lean_dec(v___x_2287_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2302_ = lean_unsigned_to_nat(2u);
v___x_2303_ = lean_unsigned_to_nat(456u);
v___x_2304_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2305_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2306_ = l_mkPanicMessageWithDecl(v___x_2305_, v___x_2304_, v___x_2303_, v___x_2302_, v___x_2301_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2307_, lean_object* v_inst_2308_, uint8_t v_zetaUnusedMode_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_toBind_2313_, lean_object* v___x_2314_, lean_object* v_info_2315_){
_start:
{
lean_object* v_haveInfo_2316_; lean_object* v_level_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_haveInfo_2316_ = lean_ctor_get(v_info_2315_, 0);
v_level_2317_ = lean_ctor_get(v_info_2315_, 5);
v___x_2318_ = lean_array_get_size(v_haveInfo_2316_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_nat_dec_eq(v___x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___f_2325_; lean_object* v___f_2326_; uint8_t v___y_2328_; 
v___x_2321_ = 1;
v___x_2322_ = lean_box(v_zetaUnusedMode_2309_);
v___x_2323_ = lean_box(v___x_2321_);
v___x_2324_ = lean_box(v___x_2320_);
lean_inc_n(v_inst_2308_, 2);
lean_inc_ref(v_e_2307_);
lean_inc(v_level_2317_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2325_, 0, v_level_2317_);
lean_closure_set(v___f_2325_, 1, v_e_2307_);
lean_closure_set(v___f_2325_, 2, v_inst_2308_);
lean_closure_set(v___f_2325_, 3, v___x_2322_);
lean_closure_set(v___f_2325_, 4, v___x_2323_);
lean_closure_set(v___f_2325_, 5, v___x_2324_);
lean_inc(v_toBind_2313_);
lean_inc_ref(v_info_2315_);
v___f_2326_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2326_, 0, v___x_2318_);
lean_closure_set(v___f_2326_, 1, v_inst_2310_);
lean_closure_set(v___f_2326_, 2, v_inst_2308_);
lean_closure_set(v___f_2326_, 3, v_inst_2311_);
lean_closure_set(v___f_2326_, 4, v_inst_2312_);
lean_closure_set(v___f_2326_, 5, v_info_2315_);
lean_closure_set(v___f_2326_, 6, v_e_2307_);
lean_closure_set(v___f_2326_, 7, v___x_2319_);
lean_closure_set(v___f_2326_, 8, v_toBind_2313_);
lean_closure_set(v___f_2326_, 9, v___f_2325_);
switch(v_zetaUnusedMode_2309_)
{
case 0:
{
v___y_2328_ = v___x_2321_;
goto v___jp_2327_;
}
case 2:
{
v___y_2328_ = v___x_2321_;
goto v___jp_2327_;
}
default: 
{
v___y_2328_ = v___x_2320_;
goto v___jp_2327_;
}
}
v___jp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_box(v___y_2328_);
v___x_2330_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2330_, 0, v_info_2315_);
lean_closure_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_apply_2(v_inst_2308_, lean_box(0), v___x_2330_);
v___x_2332_ = lean_apply_4(v_toBind_2313_, lean_box(0), lean_box(0), v___x_2331_, v___f_2326_);
return v___x_2332_;
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v_info_2315_);
lean_dec(v_toBind_2313_);
lean_dec_ref(v_inst_2312_);
lean_dec_ref(v_inst_2311_);
lean_dec_ref(v_inst_2310_);
lean_dec(v_inst_2308_);
lean_dec_ref(v_e_2307_);
v___x_2333_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2334_ = l_panic___redArg(v___x_2314_, v___x_2333_);
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2335_, lean_object* v_inst_2336_, lean_object* v_zetaUnusedMode_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_toBind_2341_, lean_object* v___x_2342_, lean_object* v_info_2343_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2344_; lean_object* v_res_2345_; 
v_zetaUnusedMode_boxed_2344_ = lean_unbox(v_zetaUnusedMode_2337_);
v_res_2345_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2335_, v_inst_2336_, v_zetaUnusedMode_boxed_2344_, v_inst_2338_, v_inst_2339_, v_inst_2340_, v_toBind_2341_, v___x_2342_, v_info_2343_);
lean_dec(v___x_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_e_2350_, uint8_t v_zetaUnusedMode_2351_){
_start:
{
lean_object* v_toBind_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; lean_object* v___x_2359_; 
v_toBind_2352_ = lean_ctor_get(v_inst_2346_, 1);
lean_inc_n(v_toBind_2352_, 2);
v___x_2353_ = lean_box(0);
lean_inc_ref(v_e_2350_);
v___x_2354_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2354_, 0, v_e_2350_);
lean_inc(v_inst_2347_);
v___x_2355_ = lean_apply_2(v_inst_2347_, lean_box(0), v___x_2354_);
lean_inc_ref(v_inst_2346_);
v___x_2356_ = l_instInhabitedOfMonad___redArg(v_inst_2346_, v___x_2353_);
v___x_2357_ = lean_box(v_zetaUnusedMode_2351_);
v___f_2358_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2358_, 0, v_e_2350_);
lean_closure_set(v___f_2358_, 1, v_inst_2347_);
lean_closure_set(v___f_2358_, 2, v___x_2357_);
lean_closure_set(v___f_2358_, 3, v_inst_2346_);
lean_closure_set(v___f_2358_, 4, v_inst_2348_);
lean_closure_set(v___f_2358_, 5, v_inst_2349_);
lean_closure_set(v___f_2358_, 6, v_toBind_2352_);
lean_closure_set(v___f_2358_, 7, v___x_2356_);
v___x_2359_ = lean_apply_4(v_toBind_2352_, lean_box(0), lean_box(0), v___x_2355_, v___f_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_e_2364_, lean_object* v_zetaUnusedMode_2365_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2366_; lean_object* v_res_2367_; 
v_zetaUnusedMode_boxed_2366_ = lean_unbox(v_zetaUnusedMode_2365_);
v_res_2367_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2360_, v_inst_2361_, v_inst_2362_, v_inst_2363_, v_e_2364_, v_zetaUnusedMode_boxed_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_e_2373_, uint8_t v_zetaUnusedMode_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2369_, v_inst_2370_, v_inst_2371_, v_inst_2372_, v_e_2373_, v_zetaUnusedMode_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_e_2381_, lean_object* v_zetaUnusedMode_2382_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2383_; lean_object* v_res_2384_; 
v_zetaUnusedMode_boxed_2383_ = lean_unbox(v_zetaUnusedMode_2382_);
v_res_2384_ = l_Lean_Meta_simpHaveTelescope(v_m_2376_, v_inst_2377_, v_inst_2378_, v_inst_2379_, v_inst_2380_, v_e_2381_, v_zetaUnusedMode_boxed_2383_);
return v_res_2384_;
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
