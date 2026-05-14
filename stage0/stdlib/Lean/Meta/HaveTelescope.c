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
lean_object* l_Lean_Meta_withExistingLocalDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_keyedConfig_37_; uint8_t v_trackZetaDelta_38_; lean_object* v_zetaDeltaSet_39_; lean_object* v_localInstances_40_; lean_object* v_defEqCtx_x3f_41_; lean_object* v_synthPendingDepth_42_; lean_object* v_canUnfold_x3f_43_; uint8_t v_univApprox_44_; uint8_t v_inTypeClassResolution_45_; uint8_t v_cacheInferType_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_keyedConfig_37_ = lean_ctor_get(v___y_32_, 0);
v_trackZetaDelta_38_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7);
v_zetaDeltaSet_39_ = lean_ctor_get(v___y_32_, 1);
v_localInstances_40_ = lean_ctor_get(v___y_32_, 3);
v_defEqCtx_x3f_41_ = lean_ctor_get(v___y_32_, 4);
v_synthPendingDepth_42_ = lean_ctor_get(v___y_32_, 5);
v_canUnfold_x3f_43_ = lean_ctor_get(v___y_32_, 6);
v_univApprox_44_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_45_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7 + 2);
v_cacheInferType_46_ = lean_ctor_get_uint8(v___y_32_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_43_);
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
lean_ctor_set(v___x_47_, 6, v_canUnfold_x3f_43_);
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
uint8_t v___x_219_; 
v___x_219_ = lean_nat_dec_le(v___x_217_, v___x_217_);
if (v___x_219_ == 0)
{
if (v___x_218_ == 0)
{
lean_dec_ref(v_buckets_216_);
return v___x_214_;
}
else
{
size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((size_t)0ULL);
v___x_221_ = lean_usize_of_nat(v___x_217_);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_211_, v_buckets_216_, v___x_220_, v___x_221_, v___x_214_);
lean_dec_ref(v_buckets_216_);
return v___x_222_;
}
}
else
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_217_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_211_, v_buckets_216_, v___x_223_, v___x_224_, v___x_214_);
lean_dec_ref(v_buckets_216_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_226_, v_a_227_);
lean_dec(v_numHaves_226_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_229_, lean_object* v_t_230_){
_start:
{
if (lean_obj_tag(v_t_230_) == 0)
{
lean_object* v_k_231_; lean_object* v_l_232_; lean_object* v_r_233_; uint8_t v___x_234_; 
v_k_231_ = lean_ctor_get(v_t_230_, 1);
v_l_232_ = lean_ctor_get(v_t_230_, 3);
v_r_233_ = lean_ctor_get(v_t_230_, 4);
v___x_234_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_229_, v_k_231_);
switch(v___x_234_)
{
case 0:
{
v_t_230_ = v_l_232_;
goto _start;
}
case 1:
{
uint8_t v___x_236_; 
v___x_236_ = 1;
return v___x_236_;
}
default: 
{
v_t_230_ = v_r_233_;
goto _start;
}
}
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_239_, lean_object* v_t_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_239_, v_t_240_);
lean_dec(v_t_240_);
lean_dec(v_k_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_243_, lean_object* v___x_244_, lean_object* v_n_245_, lean_object* v_j_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_zero_248_; uint8_t v_isZero_249_; 
v_zero_248_ = lean_unsigned_to_nat(0u);
v_isZero_249_ = lean_nat_dec_eq(v_j_246_, v_zero_248_);
if (v_isZero_249_ == 1)
{
lean_dec(v_j_246_);
return v_a_247_;
}
else
{
lean_object* v_one_250_; lean_object* v_n_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_one_250_ = lean_unsigned_to_nat(1u);
v_n_251_ = lean_nat_sub(v_j_246_, v_one_250_);
v___x_252_ = lean_nat_sub(v_n_245_, v_j_246_);
lean_dec(v_j_246_);
v___x_253_ = lean_array_fget_borrowed(v_fvars_243_, v___x_252_);
v___x_254_ = l_Lean_Expr_fvarId_x21(v___x_253_);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_254_, v___x_244_);
lean_dec(v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v___x_252_);
v_j_246_ = v_n_251_;
goto _start;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(0);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_247_, v___x_252_, v___x_257_);
v_j_246_ = v_n_251_;
v_a_247_ = v___x_258_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_260_, lean_object* v___x_261_, lean_object* v_n_262_, lean_object* v_j_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_260_, v___x_261_, v_n_262_, v_j_263_, v_a_264_);
lean_dec(v_n_262_);
lean_dec(v___x_261_);
lean_dec_ref(v_fvars_260_);
return v_res_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_unsigned_to_nat(16u);
v___x_268_ = lean_mk_array(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_274_, lean_object* v___x_275_, lean_object* v_fvars_276_, lean_object* v_info_277_, lean_object* v_bodyDeps_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc_ref(v_body_274_);
v___x_284_ = lean_infer_type(v_body_274_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc_n(v_a_285_, 2);
lean_dec_ref(v___x_284_);
v___x_286_ = l_Lean_Meta_getLevel(v_a_285_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_314_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_314_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_314_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_314_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_fvarSet_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_haveInfo_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
v___x_291_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_275_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
lean_inc(v_a_285_);
v___x_294_ = l_Lean_collectFVars(v___x_293_, v_a_285_);
v_fvarSet_295_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_fvarSet_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = lean_array_get_size(v_fvars_276_);
v___x_297_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_276_, v_fvarSet_295_, v___x_296_, v___x_296_, v___x_291_);
lean_dec(v_fvarSet_295_);
v_haveInfo_298_ = lean_ctor_get(v_info_277_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_info_277_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_309_ = lean_ctor_get(v_info_277_, 5);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_info_277_, 4);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_info_277_, 3);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_info_277_, 2);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_info_277_, 1);
lean_dec(v_unused_313_);
v___x_300_ = v_info_277_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_haveInfo_298_);
lean_dec(v_info_277_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 5, v_a_287_);
lean_ctor_set(v___x_300_, 4, v_a_285_);
lean_ctor_set(v___x_300_, 3, v_body_274_);
lean_ctor_set(v___x_300_, 2, v___x_297_);
lean_ctor_set(v___x_300_, 1, v_bodyDeps_278_);
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_haveInfo_298_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_bodyDeps_278_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_body_274_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_a_285_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_a_287_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_303_);
v___x_305_ = v___x_289_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_a_285_);
lean_dec_ref(v_bodyDeps_278_);
lean_dec_ref(v_info_277_);
lean_dec(v___x_275_);
lean_dec_ref(v_body_274_);
v_a_315_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_286_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_286_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_bodyDeps_278_);
lean_dec_ref(v_info_277_);
lean_dec(v___x_275_);
lean_dec_ref(v_body_274_);
v_a_323_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_284_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_284_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_331_, lean_object* v___x_332_, lean_object* v_fvars_333_, lean_object* v_info_334_, lean_object* v_bodyDeps_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_331_, v___x_332_, v_fvars_333_, v_info_334_, v_bodyDeps_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec_ref(v_fvars_333_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; lean_object* v_ngen_345_; lean_object* v_namePrefix_346_; lean_object* v_idx_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_377_; 
v___x_344_ = lean_st_ref_get(v___y_342_);
v_ngen_345_ = lean_ctor_get(v___x_344_, 2);
lean_inc_ref(v_ngen_345_);
lean_dec(v___x_344_);
v_namePrefix_346_ = lean_ctor_get(v_ngen_345_, 0);
v_idx_347_ = lean_ctor_get(v_ngen_345_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_ngen_345_);
if (v_isSharedCheck_377_ == 0)
{
v___x_349_ = v_ngen_345_;
v_isShared_350_ = v_isSharedCheck_377_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_idx_347_);
lean_inc(v_namePrefix_346_);
lean_dec(v_ngen_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_377_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v_nextMacroScope_353_; lean_object* v_auxDeclNGen_354_; lean_object* v_traceState_355_; lean_object* v_cache_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v_newDecls_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_375_; 
v___x_351_ = lean_st_ref_take(v___y_342_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
v_nextMacroScope_353_ = lean_ctor_get(v___x_351_, 1);
v_auxDeclNGen_354_ = lean_ctor_get(v___x_351_, 3);
v_traceState_355_ = lean_ctor_get(v___x_351_, 4);
v_cache_356_ = lean_ctor_get(v___x_351_, 5);
v_messages_357_ = lean_ctor_get(v___x_351_, 6);
v_infoState_358_ = lean_ctor_get(v___x_351_, 7);
v_snapshotTasks_359_ = lean_ctor_get(v___x_351_, 8);
v_newDecls_360_ = lean_ctor_get(v___x_351_, 9);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_351_, 2);
lean_dec(v_unused_376_);
v___x_362_ = v___x_351_;
v_isShared_363_ = v_isSharedCheck_375_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_newDecls_360_);
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_cache_356_);
lean_inc(v_traceState_355_);
lean_inc(v_auxDeclNGen_354_);
lean_inc(v_nextMacroScope_353_);
lean_inc(v_env_352_);
lean_dec(v___x_351_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_375_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_r_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
lean_inc(v_idx_347_);
lean_inc(v_namePrefix_346_);
v_r_364_ = l_Lean_Name_num___override(v_namePrefix_346_, v_idx_347_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_add(v_idx_347_, v___x_365_);
lean_dec(v_idx_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_366_);
v___x_368_ = v___x_349_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_namePrefix_346_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_374_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 2, v___x_368_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_env_352_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_354_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_traceState_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_cache_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_snapshotTasks_359_);
lean_ctor_set(v_reuseFailAlloc_373_, 9, v_newDecls_360_);
v___x_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_st_ref_set(v___y_342_, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_r_364_);
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_378_);
lean_dec(v___y_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v___x_386_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_384_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_401_, lean_object* v_numHaves_402_, lean_object* v_info_403_, lean_object* v_lctx_404_, lean_object* v_fvars_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; 
v___x_411_ = lean_box(1);
if (lean_obj_tag(v_e_401_) == 8)
{
uint8_t v_nondep_421_; 
v_nondep_421_ = lean_ctor_get_uint8(v_e_401_, sizeof(void*)*4 + 8);
if (v_nondep_421_ == 1)
{
lean_object* v_declName_422_; lean_object* v_type_423_; lean_object* v_value_424_; lean_object* v_body_425_; lean_object* v_t_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_declName_422_ = lean_ctor_get(v_e_401_, 0);
lean_inc(v_declName_422_);
v_type_423_ = lean_ctor_get(v_e_401_, 1);
lean_inc_ref(v_type_423_);
v_value_424_ = lean_ctor_get(v_e_401_, 2);
lean_inc_ref(v_value_424_);
v_body_425_ = lean_ctor_get(v_e_401_, 3);
lean_inc_ref(v_body_425_);
lean_dec_ref(v_e_401_);
v_t_426_ = lean_expr_instantiate_rev(v_type_423_, v_fvars_405_);
lean_inc_ref(v_t_426_);
v___x_427_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_427_, 0, v_t_426_);
lean_inc_ref(v_lctx_404_);
v___x_428_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_404_, v___x_427_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
v___x_430_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_haveInfo_432_; lean_object* v_bodyDeps_433_; lean_object* v_bodyTypeDeps_434_; lean_object* v_body_435_; lean_object* v_bodyType_436_; lean_object* v_level_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_458_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___x_430_);
v_haveInfo_432_ = lean_ctor_get(v_info_403_, 0);
v_bodyDeps_433_ = lean_ctor_get(v_info_403_, 1);
v_bodyTypeDeps_434_ = lean_ctor_get(v_info_403_, 2);
v_body_435_ = lean_ctor_get(v_info_403_, 3);
v_bodyType_436_ = lean_ctor_get(v_info_403_, 4);
v_level_437_ = lean_ctor_get(v_info_403_, 5);
v_isSharedCheck_458_ = !lean_is_exclusive(v_info_403_);
if (v_isSharedCheck_458_ == 0)
{
v___x_439_ = v_info_403_;
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_level_437_);
lean_inc(v_bodyType_436_);
lean_inc(v_body_435_);
lean_inc(v_bodyTypeDeps_434_);
lean_inc(v_bodyDeps_433_);
lean_inc(v_haveInfo_432_);
lean_dec(v_info_403_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_typeBackDeps_441_; lean_object* v_valueBackDeps_442_; lean_object* v_v_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v_typeBackDeps_441_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_402_, v_type_423_);
lean_inc_ref(v_value_424_);
v_valueBackDeps_442_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_402_, v_value_424_);
v_v_443_ = lean_expr_instantiate_rev(v_value_424_, v_fvars_405_);
lean_dec_ref(v_value_424_);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = 0;
lean_inc(v_a_431_);
v___x_446_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v_a_431_);
lean_ctor_set(v___x_446_, 2, v_declName_422_);
lean_ctor_set(v___x_446_, 3, v_t_426_);
lean_ctor_set(v___x_446_, 4, v_v_443_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*5, v_nondep_421_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*5 + 1, v___x_445_);
lean_inc_ref(v___x_446_);
v___x_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_447_, 0, v_typeBackDeps_441_);
lean_ctor_set(v___x_447_, 1, v_valueBackDeps_442_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
lean_ctor_set(v___x_447_, 3, v_a_429_);
v___x_448_ = lean_array_push(v_haveInfo_432_, v___x_447_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_448_);
v___x_450_ = v___x_439_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_bodyDeps_433_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_bodyTypeDeps_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_body_435_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_bodyType_436_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_level_437_);
v___x_450_ = v_reuseFailAlloc_457_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = l_Lean_LocalContext_addDecl(v_lctx_404_, v___x_446_);
v___x_452_ = l_Lean_mkFVar(v_a_431_);
v___x_453_ = lean_array_push(v_fvars_405_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_numHaves_402_, v___x_454_);
lean_dec(v_numHaves_402_);
v_e_401_ = v_body_425_;
v_numHaves_402_ = v___x_455_;
v_info_403_ = v___x_450_;
v_lctx_404_ = v___x_451_;
v_fvars_405_ = v___x_453_;
goto _start;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_429_);
lean_dec_ref(v_t_426_);
lean_dec_ref(v_body_425_);
lean_dec_ref(v_value_424_);
lean_dec_ref(v_type_423_);
lean_dec(v_declName_422_);
lean_dec_ref(v_fvars_405_);
lean_dec_ref(v_lctx_404_);
lean_dec_ref(v_info_403_);
lean_dec(v_numHaves_402_);
v_a_459_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_430_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_430_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_t_426_);
lean_dec_ref(v_body_425_);
lean_dec_ref(v_value_424_);
lean_dec_ref(v_type_423_);
lean_dec(v_declName_422_);
lean_dec_ref(v_fvars_405_);
lean_dec_ref(v_lctx_404_);
lean_dec_ref(v_info_403_);
lean_dec(v_numHaves_402_);
v_a_467_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_428_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_428_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
v___y_413_ = v_a_406_;
v___y_414_ = v_a_407_;
v___y_415_ = v_a_408_;
v___y_416_ = v_a_409_;
goto v___jp_412_;
}
}
else
{
v___y_413_ = v_a_406_;
v___y_414_ = v_a_407_;
v___y_415_ = v_a_408_;
v___y_416_ = v_a_409_;
goto v___jp_412_;
}
v___jp_412_:
{
lean_object* v_bodyDeps_417_; lean_object* v_body_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
lean_inc_ref(v_e_401_);
v_bodyDeps_417_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_402_, v_e_401_);
lean_dec(v_numHaves_402_);
v_body_418_ = lean_expr_instantiate_rev(v_e_401_, v_fvars_405_);
lean_dec_ref(v_e_401_);
v___f_419_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_419_, 0, v_body_418_);
lean_closure_set(v___f_419_, 1, v___x_411_);
lean_closure_set(v___f_419_, 2, v_fvars_405_);
lean_closure_set(v___f_419_, 3, v_info_403_);
lean_closure_set(v___f_419_, 4, v_bodyDeps_417_);
v___x_420_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_404_, v___f_419_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_475_, lean_object* v_numHaves_476_, lean_object* v_info_477_, lean_object* v_lctx_478_, lean_object* v_fvars_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_475_, v_numHaves_476_, v_info_477_, v_lctx_478_, v_fvars_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_486_, lean_object* v_m_487_, lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_487_, v_a_488_, v_b_489_);
return v___x_490_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_491_, lean_object* v_k_492_, lean_object* v_t_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_492_, v_t_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_495_, lean_object* v_k_496_, lean_object* v_t_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_495_, v_k_496_, v_t_497_);
lean_dec(v_t_497_);
lean_dec(v_k_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_500_, lean_object* v___x_501_, lean_object* v_n_502_, lean_object* v_j_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_500_, v___x_501_, v_n_502_, v_j_503_, v_a_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_507_, lean_object* v___x_508_, lean_object* v_n_509_, lean_object* v_j_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_507_, v___x_508_, v_n_509_, v_j_510_, v_a_511_, v_a_512_);
lean_dec(v_n_509_);
lean_dec(v___x_508_);
lean_dec_ref(v_fvars_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_530_, lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_530_, v_a_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_a_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_535_, lean_object* v_data_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_538_, lean_object* v_i_539_, lean_object* v_source_540_, lean_object* v_target_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_539_, v_source_540_, v_target_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_lctx_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_lctx_553_ = lean_ctor_get(v_a_548_, 2);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_556_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_553_);
v___x_557_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_547_, v___x_554_, v___x_556_, v_lctx_553_, v___x_555_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
return v_x_565_;
}
else
{
lean_object* v_key_567_; lean_object* v_tail_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_key_567_ = lean_ctor_get(v_x_566_, 0);
v_tail_568_ = lean_ctor_get(v_x_566_, 2);
v___x_569_ = 1;
v___x_570_ = lean_box(v___x_569_);
v___x_571_ = lean_array_set(v_x_565_, v_key_567_, v___x_570_);
v_x_565_ = v___x_571_;
v_x_566_ = v_tail_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_573_, v_x_574_);
lean_dec(v_x_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_576_, size_t v_i_577_, size_t v_stop_578_, lean_object* v_b_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_eq(v_i_577_, v_stop_578_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; size_t v___x_583_; size_t v___x_584_; 
v___x_581_ = lean_array_uget_borrowed(v_as_576_, v_i_577_);
v___x_582_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_579_, v___x_581_);
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_577_, v___x_583_);
v_i_577_ = v___x_584_;
v_b_579_ = v___x_582_;
goto _start;
}
else
{
return v_b_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_586_, lean_object* v_i_587_, lean_object* v_stop_588_, lean_object* v_b_589_){
_start:
{
size_t v_i_boxed_590_; size_t v_stop_boxed_591_; lean_object* v_res_592_; 
v_i_boxed_590_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_stop_boxed_591_ = lean_unbox_usize(v_stop_588_);
lean_dec(v_stop_588_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_586_, v_i_boxed_590_, v_stop_boxed_591_, v_b_589_);
lean_dec_ref(v_as_586_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_593_, lean_object* v_s_594_){
_start:
{
lean_object* v_buckets_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_buckets_595_ = lean_ctor_get(v_s_594_, 1);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_array_get_size(v_buckets_595_);
v___x_598_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
return v_arr_593_;
}
else
{
uint8_t v___x_599_; 
v___x_599_ = lean_nat_dec_le(v___x_597_, v___x_597_);
if (v___x_599_ == 0)
{
if (v___x_598_ == 0)
{
return v_arr_593_;
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((size_t)0ULL);
v___x_601_ = lean_usize_of_nat(v___x_597_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_595_, v___x_600_, v___x_601_, v_arr_593_);
return v___x_602_;
}
}
else
{
size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_597_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_595_, v___x_603_, v___x_604_, v_arr_593_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_606_, lean_object* v_s_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_606_, v_s_607_);
lean_dec_ref(v_s_607_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_609_, lean_object* v_numHaves_610_, lean_object* v___x_611_, lean_object* v_a_612_, lean_object* v_b_613_){
_start:
{
lean_object* v_a_616_; uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_lt(v_a_612_, v_upperBound_609_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_a_612_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_b_613_);
return v___x_621_;
}
else
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_622_ = 0;
v___x_623_ = lean_nat_sub(v_numHaves_610_, v_a_612_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_sub(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(v___x_622_);
v___x_627_ = lean_array_get(v___x_626_, v_b_613_, v___x_625_);
lean_dec(v___x_626_);
v___x_628_ = lean_unbox(v___x_627_);
lean_dec(v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v___x_625_);
v_a_616_ = v_b_613_;
goto v___jp_615_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_typeBackDeps_631_; lean_object* v_valueBackDeps_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_630_ = lean_array_get_borrowed(v___x_629_, v___x_611_, v___x_625_);
lean_dec(v___x_625_);
v_typeBackDeps_631_ = lean_ctor_get(v___x_630_, 0);
v_valueBackDeps_632_ = lean_ctor_get(v___x_630_, 1);
v___x_633_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_613_, v_typeBackDeps_631_);
v___x_634_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_633_, v_valueBackDeps_632_);
v_a_616_ = v___x_634_;
goto v___jp_615_;
}
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_a_612_, v___x_617_);
lean_dec(v_a_612_);
v_a_612_ = v___x_618_;
v_b_613_ = v_a_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_635_, lean_object* v_numHaves_636_, lean_object* v___x_637_, lean_object* v_a_638_, lean_object* v_b_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_635_, v_numHaves_636_, v___x_637_, v_a_638_, v_b_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_numHaves_636_);
lean_dec(v_upperBound_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_642_, lean_object* v_init_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_haveInfo_649_; lean_object* v_numHaves_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v_used_653_; lean_object* v___x_654_; lean_object* v_used_655_; lean_object* v___x_656_; 
v_haveInfo_649_ = lean_ctor_get(v_info_642_, 0);
v_numHaves_650_ = lean_array_get_size(v_haveInfo_649_);
v___x_651_ = 0;
v___x_652_ = lean_box(v___x_651_);
v_used_653_ = lean_mk_array(v_numHaves_650_, v___x_652_);
v___x_654_ = lean_unsigned_to_nat(0u);
v_used_655_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_653_, v_init_643_);
v___x_656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_650_, v_numHaves_650_, v_haveInfo_649_, v___x_654_, v_used_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_657_, lean_object* v_init_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_657_, v_init_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec_ref(v_init_658_);
lean_dec_ref(v_info_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_665_, lean_object* v_numHaves_666_, lean_object* v___x_667_, lean_object* v_inst_668_, lean_object* v_R_669_, lean_object* v_a_670_, lean_object* v_b_671_, lean_object* v_c_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_665_, v_numHaves_666_, v___x_667_, v_a_670_, v_b_671_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_679_, lean_object* v_numHaves_680_, lean_object* v___x_681_, lean_object* v_inst_682_, lean_object* v_R_683_, lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_c_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_679_, v_numHaves_680_, v___x_681_, v_inst_682_, v_R_683_, v_a_684_, v_b_685_, v_c_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___x_681_);
lean_dec(v_numHaves_680_);
lean_dec(v_upperBound_679_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_695_, uint8_t v_keepUnused_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_bodyDeps_702_; lean_object* v_bodyTypeDeps_703_; lean_object* v___x_704_; 
v_bodyDeps_702_ = lean_ctor_get(v_info_695_, 1);
v_bodyTypeDeps_703_ = lean_ctor_get(v_info_695_, 2);
v___x_704_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_695_, v_bodyTypeDeps_703_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_704_) == 0)
{
if (v_keepUnused_696_ == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
v___x_706_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_695_, v_bodyDeps_702_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_a_705_);
lean_ctor_set(v___x_711_, 1, v_a_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_a_705_);
v_a_716_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_706_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_706_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_733_; 
v_a_724_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_733_ == 0)
{
v___x_726_ = v___x_704_;
v_isShared_727_ = v_isSharedCheck_733_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_704_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_733_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_728_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_a_724_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_729_);
v___x_731_ = v___x_726_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_a_734_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_704_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_704_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_742_, lean_object* v_keepUnused_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
uint8_t v_keepUnused_boxed_749_; lean_object* v_res_750_; 
v_keepUnused_boxed_749_ = lean_unbox(v_keepUnused_743_);
v_res_750_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_742_, v_keepUnused_boxed_749_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec_ref(v_info_742_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_box(0);
v___x_755_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_756_ = l_Lean_Expr_const___override(v___x_755_, v___x_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = 0;
v___x_758_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_759_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_ctor_set(v___x_759_, 3, v___x_758_);
lean_ctor_set(v___x_759_, 4, v___x_758_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*5, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_760_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_toApplicative_778_, lean_object* v_level_779_, lean_object* v_exprType_780_, lean_object* v_e_781_, uint8_t v___x_782_, lean_object* v_xs_783_, lean_object* v_____do__lift_784_){
_start:
{
if (lean_obj_tag(v_____do__lift_784_) == 0)
{
lean_object* v_toPure_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_proof_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_toPure_785_ = lean_ctor_get(v_toApplicative_778_, 1);
lean_inc(v_toPure_785_);
lean_dec_ref(v_toApplicative_778_);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_787_ = lean_box(0);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v_level_779_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_mkConst(v___x_786_, v___x_788_);
lean_inc_ref_n(v_e_781_, 3);
lean_inc_ref(v_exprType_780_);
v_proof_790_ = l_Lean_mkAppB(v___x_789_, v_exprType_780_, v_e_781_);
v___x_791_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_791_, 0, v_e_781_);
lean_ctor_set(v___x_791_, 1, v_exprType_780_);
lean_ctor_set(v___x_791_, 2, v_e_781_);
lean_ctor_set(v___x_791_, 3, v_e_781_);
lean_ctor_set(v___x_791_, 4, v_proof_790_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*5, v___x_782_);
v___x_792_ = lean_apply_2(v_toPure_785_, lean_box(0), v___x_791_);
return v___x_792_;
}
else
{
lean_object* v_e_793_; lean_object* v_h_794_; lean_object* v_expr_795_; lean_object* v_proof_796_; lean_object* v___x_802_; uint8_t v___x_803_; 
lean_dec(v_level_779_);
v_e_793_ = lean_ctor_get(v_____do__lift_784_, 0);
v_h_794_ = lean_ctor_get(v_____do__lift_784_, 1);
v_expr_795_ = lean_expr_abstract(v_e_793_, v_xs_783_);
v_proof_796_ = lean_expr_abstract(v_h_794_, v_xs_783_);
lean_inc_ref(v_proof_796_);
v___x_802_ = l_Lean_Expr_cleanupAnnotations(v_proof_796_);
v___x_803_ = l_Lean_Expr_isApp(v___x_802_);
if (v___x_803_ == 0)
{
lean_dec_ref(v___x_802_);
goto v___jp_797_;
}
else
{
lean_object* v_arg_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_arg_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc_ref(v_arg_804_);
v___x_805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_802_);
v___x_806_ = l_Lean_Expr_isApp(v___x_805_);
if (v___x_806_ == 0)
{
lean_dec_ref(v___x_805_);
lean_dec_ref(v_arg_804_);
goto v___jp_797_;
}
else
{
lean_object* v_arg_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_arg_807_ = lean_ctor_get(v___x_805_, 1);
lean_inc_ref(v_arg_807_);
v___x_808_ = l_Lean_Expr_appFnCleanup___redArg(v___x_805_);
v___x_809_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_810_ = l_Lean_Expr_isConstOf(v___x_808_, v___x_809_);
lean_dec_ref(v___x_808_);
if (v___x_810_ == 0)
{
lean_dec_ref(v_arg_807_);
lean_dec_ref(v_arg_804_);
goto v___jp_797_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_812_ = lean_unsigned_to_nat(3u);
v___x_813_ = l_Lean_Expr_isAppOfArity(v_arg_807_, v___x_811_, v___x_812_);
lean_dec_ref(v_arg_807_);
if (v___x_813_ == 0)
{
lean_dec_ref(v_arg_804_);
goto v___jp_797_;
}
else
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = l_Lean_Expr_cleanupAnnotations(v_arg_804_);
v___x_815_ = l_Lean_Expr_isApp(v___x_814_);
if (v___x_815_ == 0)
{
lean_dec_ref(v___x_814_);
goto v___jp_797_;
}
else
{
lean_object* v_arg_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_arg_816_ = lean_ctor_get(v___x_814_, 1);
lean_inc_ref(v_arg_816_);
v___x_817_ = l_Lean_Expr_appFnCleanup___redArg(v___x_814_);
v___x_818_ = l_Lean_Expr_isApp(v___x_817_);
if (v___x_818_ == 0)
{
lean_dec_ref(v___x_817_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v_arg_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_arg_819_ = lean_ctor_get(v___x_817_, 1);
lean_inc_ref(v_arg_819_);
v___x_820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_817_);
v___x_821_ = l_Lean_Expr_isConstOf(v___x_820_, v___x_809_);
lean_dec_ref(v___x_820_);
if (v___x_821_ == 0)
{
lean_dec_ref(v_arg_819_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = l_Lean_Expr_cleanupAnnotations(v_arg_819_);
v___x_823_ = l_Lean_Expr_isApp(v___x_822_);
if (v___x_823_ == 0)
{
lean_dec_ref(v___x_822_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v_arg_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_arg_824_ = lean_ctor_get(v___x_822_, 1);
lean_inc_ref(v_arg_824_);
v___x_825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_822_);
v___x_826_ = l_Lean_Expr_isApp(v___x_825_);
if (v___x_826_ == 0)
{
lean_dec_ref(v___x_825_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v_arg_827_; uint8_t v___y_829_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_arg_827_ = lean_ctor_get(v___x_825_, 1);
lean_inc_ref(v_arg_827_);
v___x_833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_825_);
v___x_834_ = l_Lean_Expr_isApp(v___x_833_);
if (v___x_834_ == 0)
{
lean_dec_ref(v___x_833_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = l_Lean_Expr_appFnCleanup___redArg(v___x_833_);
v___x_836_ = l_Lean_Expr_isConstOf(v___x_835_, v___x_811_);
lean_dec_ref(v___x_835_);
if (v___x_836_ == 0)
{
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Expr_getAppFn(v_arg_816_);
if (lean_obj_tag(v___x_837_) == 4)
{
lean_object* v_declName_838_; 
v_declName_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_declName_838_);
lean_dec_ref(v___x_837_);
if (lean_obj_tag(v_declName_838_) == 1)
{
lean_object* v_pre_839_; 
v_pre_839_ = lean_ctor_get(v_declName_838_, 0);
if (lean_obj_tag(v_pre_839_) == 0)
{
lean_object* v_str_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_str_840_ = lean_ctor_get(v_declName_838_, 1);
lean_inc_ref(v_str_840_);
lean_dec_ref(v_declName_838_);
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_842_ = lean_string_dec_eq(v_str_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_844_ = lean_string_dec_eq(v_str_840_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_846_ = lean_string_dec_eq(v_str_840_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_848_ = lean_string_dec_eq(v_str_840_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_850_ = lean_string_dec_eq(v_str_840_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_852_ = lean_string_dec_eq(v_str_840_, v___x_851_);
lean_dec_ref(v_str_840_);
if (v___x_852_ == 0)
{
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
v___y_829_ = v___x_810_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_str_840_);
v___y_829_ = v___x_810_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_str_840_);
v___y_829_ = v___x_810_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_str_840_);
v___y_829_ = v___x_810_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_str_840_);
v___y_829_ = v___x_810_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_str_840_);
v___y_829_ = v___x_810_;
goto v___jp_828_;
}
}
else
{
lean_dec_ref(v_declName_838_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
}
else
{
lean_dec(v_declName_838_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
}
else
{
lean_dec_ref(v___x_837_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
}
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_816_);
goto v___jp_797_;
}
else
{
lean_object* v_toPure_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v_proof_796_);
lean_dec_ref(v_e_781_);
v_toPure_830_ = lean_ctor_get(v_toApplicative_778_, 1);
lean_inc(v_toPure_830_);
lean_dec_ref(v_toApplicative_778_);
v___x_831_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_831_, 0, v_arg_824_);
lean_ctor_set(v___x_831_, 1, v_exprType_780_);
lean_ctor_set(v___x_831_, 2, v_arg_827_);
lean_ctor_set(v___x_831_, 3, v_expr_795_);
lean_ctor_set(v___x_831_, 4, v_arg_816_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*5, v___x_810_);
v___x_832_ = lean_apply_2(v_toPure_830_, lean_box(0), v___x_831_);
return v___x_832_;
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
v___jp_797_:
{
lean_object* v_toPure_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_toPure_798_ = lean_ctor_get(v_toApplicative_778_, 1);
lean_inc(v_toPure_798_);
lean_dec_ref(v_toApplicative_778_);
v___x_799_ = 1;
lean_inc_ref(v_expr_795_);
v___x_800_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_800_, 0, v_expr_795_);
lean_ctor_set(v___x_800_, 1, v_exprType_780_);
lean_ctor_set(v___x_800_, 2, v_e_781_);
lean_ctor_set(v___x_800_, 3, v_expr_795_);
lean_ctor_set(v___x_800_, 4, v_proof_796_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*5, v___x_799_);
v___x_801_ = lean_apply_2(v_toPure_798_, lean_box(0), v___x_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_toApplicative_853_, lean_object* v_level_854_, lean_object* v_exprType_855_, lean_object* v_e_856_, lean_object* v___x_857_, lean_object* v_xs_858_, lean_object* v_____do__lift_859_){
_start:
{
uint8_t v___x_12301__boxed_860_; lean_object* v_res_861_; 
v___x_12301__boxed_860_ = lean_unbox(v___x_857_);
v_res_861_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_853_, v_level_854_, v_exprType_855_, v_e_856_, v___x_12301__boxed_860_, v_xs_858_, v_____do__lift_859_);
lean_dec(v_____do__lift_859_);
lean_dec_ref(v_xs_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_862_, lean_object* v_bodyType_863_, lean_object* v_xs_864_, lean_object* v_toApplicative_865_, lean_object* v_level_866_, lean_object* v_e_867_, uint8_t v___x_868_, lean_object* v_body_869_, lean_object* v_toBind_870_, lean_object* v_____r_871_){
_start:
{
lean_object* v_simp_872_; lean_object* v_exprType_873_; lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_simp_872_ = lean_ctor_get(v_inst_862_, 2);
lean_inc(v_simp_872_);
lean_dec_ref(v_inst_862_);
v_exprType_873_ = lean_expr_abstract(v_bodyType_863_, v_xs_864_);
v___x_874_ = lean_box(v___x_868_);
v___f_875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_875_, 0, v_toApplicative_865_);
lean_closure_set(v___f_875_, 1, v_level_866_);
lean_closure_set(v___f_875_, 2, v_exprType_873_);
lean_closure_set(v___f_875_, 3, v_e_867_);
lean_closure_set(v___f_875_, 4, v___x_874_);
lean_closure_set(v___f_875_, 5, v_xs_864_);
v___x_876_ = lean_apply_1(v_simp_872_, v_body_869_);
v___x_877_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v___x_876_, v___f_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_878_, lean_object* v_bodyType_879_, lean_object* v_xs_880_, lean_object* v_toApplicative_881_, lean_object* v_level_882_, lean_object* v_e_883_, lean_object* v___x_884_, lean_object* v_body_885_, lean_object* v_toBind_886_, lean_object* v_____r_887_){
_start:
{
uint8_t v___x_12454__boxed_888_; lean_object* v_res_889_; 
v___x_12454__boxed_888_ = lean_unbox(v___x_884_);
v_res_889_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_878_, v_bodyType_879_, v_xs_880_, v_toApplicative_881_, v_level_882_, v_e_883_, v___x_12454__boxed_888_, v_body_885_, v_toBind_886_, v_____r_887_);
lean_dec_ref(v_bodyType_879_);
return v_res_889_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_898_, lean_object* v___x_899_, lean_object* v___f_900_, lean_object* v_body_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_options_912_; uint8_t v_hasTrace_913_; 
v_options_912_ = lean_ctor_get(v___y_906_, 2);
v_hasTrace_913_ = lean_ctor_get_uint8(v_options_912_, sizeof(void*)*1);
if (v_hasTrace_913_ == 0)
{
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v_body_901_);
lean_dec(v___f_900_);
lean_dec(v___x_899_);
lean_dec(v_cls_898_);
goto v___jp_909_;
}
else
{
lean_object* v_inheritedTraceOptions_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_inheritedTraceOptions_914_ = lean_ctor_get(v___y_906_, 13);
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_898_);
v___x_916_ = l_Lean_Name_append(v___x_915_, v_cls_898_);
v___x_917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_914_, v_options_912_, v___x_916_);
lean_dec(v___x_916_);
if (v___x_917_ == 0)
{
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v_body_901_);
lean_dec(v___f_900_);
lean_dec(v___x_899_);
lean_dec(v_cls_898_);
goto v___jp_909_;
}
else
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_toMonadRef_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_11856__overap_928_; lean_object* v___x_929_; 
v___f_918_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_919_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_920_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_921_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_919_, v___x_899_, v___x_920_);
v___x_922_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_918_, v___f_900_, v___x_921_);
v_toMonadRef_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_toMonadRef_923_);
lean_dec_ref(v___x_922_);
v___x_924_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5);
v___x_926_ = l_Lean_MessageData_ofExpr(v_body_901_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_11856__overap_928_ = l_Lean_addTrace___redArg(v___x_902_, v___x_903_, v_toMonadRef_923_, v___x_924_, v_cls_898_, v___x_927_);
v___x_929_ = lean_apply_5(v___x_11856__overap_928_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
return v___x_929_;
}
}
v___jp_909_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_930_, lean_object* v___x_931_, lean_object* v___f_932_, lean_object* v_body_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_930_, v___x_931_, v___f_932_, v_body_933_, v___x_934_, v___x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_944_, lean_object* v_type_945_, lean_object* v___y_946_, lean_object* v_value_947_, uint8_t v_nondep_948_, lean_object* v_toApplicative_949_, lean_object* v___x_950_, uint8_t v___y_951_, lean_object* v_us_952_, lean_object* v_rb_953_){
_start:
{
lean_object* v_expr_954_; lean_object* v_exprType_955_; lean_object* v_exprInit_956_; lean_object* v_exprResult_957_; lean_object* v_proof_958_; uint8_t v_modified_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_988_; 
v_expr_954_ = lean_ctor_get(v_rb_953_, 0);
v_exprType_955_ = lean_ctor_get(v_rb_953_, 1);
v_exprInit_956_ = lean_ctor_get(v_rb_953_, 2);
v_exprResult_957_ = lean_ctor_get(v_rb_953_, 3);
v_proof_958_ = lean_ctor_get(v_rb_953_, 4);
v_modified_959_ = lean_ctor_get_uint8(v_rb_953_, sizeof(void*)*5);
v_isSharedCheck_988_ = !lean_is_exclusive(v_rb_953_);
if (v_isSharedCheck_988_ == 0)
{
v___x_961_ = v_rb_953_;
v_isShared_962_ = v_isSharedCheck_988_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_proof_958_);
lean_inc(v_exprResult_957_);
lean_inc(v_exprInit_956_);
lean_inc(v_exprType_955_);
lean_inc(v_expr_954_);
lean_dec(v_rb_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_988_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v_expr_965_; lean_object* v___x_966_; lean_object* v_exprType_967_; lean_object* v___x_968_; lean_object* v_exprInit_969_; lean_object* v_exprResult_970_; 
v___x_963_ = 0;
lean_inc_ref_n(v_type_945_, 4);
lean_inc_n(v_declName_944_, 4);
v___x_964_ = l_Lean_mkLambda(v_declName_944_, v___x_963_, v_type_945_, v_expr_954_);
lean_inc_ref_n(v___y_946_, 3);
lean_inc_ref(v___x_964_);
v_expr_965_ = l_Lean_Expr_app___override(v___x_964_, v___y_946_);
v___x_966_ = l_Lean_mkLambda(v_declName_944_, v___x_963_, v_type_945_, v_exprType_955_);
lean_inc_ref(v___x_966_);
v_exprType_967_ = l_Lean_Expr_app___override(v___x_966_, v___y_946_);
v___x_968_ = l_Lean_mkLambda(v_declName_944_, v___x_963_, v_type_945_, v_exprInit_956_);
lean_inc_ref(v___x_968_);
v_exprInit_969_ = l_Lean_Expr_app___override(v___x_968_, v_value_947_);
v_exprResult_970_ = l_Lean_Expr_letE___override(v_declName_944_, v_type_945_, v___y_946_, v_exprResult_957_, v_nondep_948_);
if (v_modified_959_ == 0)
{
lean_object* v_toPure_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_proof_974_; lean_object* v___x_976_; 
lean_dec_ref(v___x_968_);
lean_dec_ref(v___x_966_);
lean_dec_ref(v___x_964_);
lean_dec_ref(v_proof_958_);
lean_dec(v_us_952_);
lean_dec_ref(v___y_946_);
lean_dec_ref(v_type_945_);
lean_dec(v_declName_944_);
v_toPure_971_ = lean_ctor_get(v_toApplicative_949_, 1);
lean_inc(v_toPure_971_);
lean_dec_ref(v_toApplicative_949_);
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_973_ = l_Lean_mkConst(v___x_972_, v___x_950_);
lean_inc_ref(v_expr_965_);
lean_inc_ref(v_exprType_967_);
v_proof_974_ = l_Lean_mkAppB(v___x_973_, v_exprType_967_, v_expr_965_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 4, v_proof_974_);
lean_ctor_set(v___x_961_, 3, v_exprResult_970_);
lean_ctor_set(v___x_961_, 2, v_exprInit_969_);
lean_ctor_set(v___x_961_, 1, v_exprType_967_);
lean_ctor_set(v___x_961_, 0, v_expr_965_);
v___x_976_ = v___x_961_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_expr_965_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_exprType_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_exprInit_969_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_exprResult_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_proof_974_);
v___x_976_ = v_reuseFailAlloc_978_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; 
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*5, v___y_951_);
v___x_977_ = lean_apply_2(v_toPure_971_, lean_box(0), v___x_976_);
return v___x_977_;
}
}
else
{
lean_object* v_toPure_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_proof_983_; lean_object* v___x_985_; 
lean_dec(v___x_950_);
v_toPure_979_ = lean_ctor_get(v_toApplicative_949_, 1);
lean_inc(v_toPure_979_);
lean_dec_ref(v_toApplicative_949_);
lean_inc_ref(v_type_945_);
v___x_980_ = l_Lean_mkLambda(v_declName_944_, v___x_963_, v_type_945_, v_proof_958_);
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_982_ = l_Lean_mkConst(v___x_981_, v_us_952_);
v_proof_983_ = l_Lean_mkApp6(v___x_982_, v_type_945_, v___x_966_, v___y_946_, v___x_968_, v___x_964_, v___x_980_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 4, v_proof_983_);
lean_ctor_set(v___x_961_, 3, v_exprResult_970_);
lean_ctor_set(v___x_961_, 2, v_exprInit_969_);
lean_ctor_set(v___x_961_, 1, v_exprType_967_);
lean_ctor_set(v___x_961_, 0, v_expr_965_);
v___x_985_ = v___x_961_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_expr_965_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_exprType_967_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_exprInit_969_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_exprResult_970_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_proof_983_);
v___x_985_ = v_reuseFailAlloc_987_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; 
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*5, v_nondep_948_);
v___x_986_ = lean_apply_2(v_toPure_979_, lean_box(0), v___x_985_);
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_989_, lean_object* v_type_990_, lean_object* v___y_991_, lean_object* v_value_992_, lean_object* v_nondep_993_, lean_object* v_toApplicative_994_, lean_object* v___x_995_, lean_object* v___y_996_, lean_object* v_us_997_, lean_object* v_rb_998_){
_start:
{
uint8_t v_nondep_12570__boxed_999_; uint8_t v___y_12572__boxed_1000_; lean_object* v_res_1001_; 
v_nondep_12570__boxed_999_ = lean_unbox(v_nondep_993_);
v___y_12572__boxed_1000_ = lean_unbox(v___y_996_);
v_res_1001_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_989_, v_type_990_, v___y_991_, v_value_992_, v_nondep_12570__boxed_999_, v_toApplicative_994_, v___x_995_, v___y_12572__boxed_1000_, v_us_997_, v_rb_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1002_, lean_object* v_____x_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_apply_1(v___f_1002_, v_____x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1009_, lean_object* v_declName_1010_, lean_object* v_type_1011_, lean_object* v_value_1012_, lean_object* v_us_1013_, lean_object* v___x_1014_, lean_object* v_toApplicative_1015_, uint8_t v_nondep_1016_, lean_object* v_rb_1017_){
_start:
{
lean_object* v_expr_1018_; lean_object* v_exprType_1019_; lean_object* v_exprInit_1020_; lean_object* v_exprResult_1021_; lean_object* v_proof_1022_; uint8_t v_modified_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1053_; 
v_expr_1018_ = lean_ctor_get(v_rb_1017_, 0);
v_exprType_1019_ = lean_ctor_get(v_rb_1017_, 1);
v_exprInit_1020_ = lean_ctor_get(v_rb_1017_, 2);
v_exprResult_1021_ = lean_ctor_get(v_rb_1017_, 3);
v_proof_1022_ = lean_ctor_get(v_rb_1017_, 4);
v_modified_1023_ = lean_ctor_get_uint8(v_rb_1017_, sizeof(void*)*5);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_rb_1017_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1025_ = v_rb_1017_;
v_isShared_1026_ = v_isSharedCheck_1053_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_proof_1022_);
lean_inc(v_exprResult_1021_);
lean_inc(v_exprInit_1020_);
lean_inc(v_exprType_1019_);
lean_inc(v_expr_1018_);
lean_dec(v_rb_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1053_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_expr_1027_; lean_object* v_exprType_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v_exprInit_1031_; lean_object* v_exprResult_1032_; 
v_expr_1027_ = lean_expr_lower_loose_bvars(v_expr_1018_, v___x_1009_, v___x_1009_);
lean_dec_ref(v_expr_1018_);
v_exprType_1028_ = lean_expr_lower_loose_bvars(v_exprType_1019_, v___x_1009_, v___x_1009_);
lean_dec_ref(v_exprType_1019_);
v___x_1029_ = 0;
lean_inc_ref(v_type_1011_);
lean_inc(v_declName_1010_);
v___x_1030_ = l_Lean_mkLambda(v_declName_1010_, v___x_1029_, v_type_1011_, v_exprInit_1020_);
lean_inc_ref(v_value_1012_);
lean_inc_ref(v___x_1030_);
v_exprInit_1031_ = l_Lean_Expr_app___override(v___x_1030_, v_value_1012_);
v_exprResult_1032_ = lean_expr_lower_loose_bvars(v_exprResult_1021_, v___x_1009_, v___x_1009_);
lean_dec_ref(v_exprResult_1021_);
if (v_modified_1023_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_proof_1038_; lean_object* v_toPure_1039_; lean_object* v___x_1041_; 
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_proof_1022_);
lean_dec(v_declName_1010_);
v___x_1033_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1034_ = l_Lean_mkConst(v___x_1033_, v_us_1013_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1036_ = l_Lean_mkConst(v___x_1035_, v___x_1014_);
lean_inc_ref_n(v_expr_1027_, 3);
lean_inc_ref_n(v_exprType_1028_, 2);
v___x_1037_ = l_Lean_mkAppB(v___x_1036_, v_exprType_1028_, v_expr_1027_);
v_proof_1038_ = l_Lean_mkApp6(v___x_1034_, v_type_1011_, v_exprType_1028_, v_value_1012_, v_expr_1027_, v_expr_1027_, v___x_1037_);
v_toPure_1039_ = lean_ctor_get(v_toApplicative_1015_, 1);
lean_inc(v_toPure_1039_);
lean_dec_ref(v_toApplicative_1015_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v_proof_1038_);
lean_ctor_set(v___x_1025_, 3, v_exprResult_1032_);
lean_ctor_set(v___x_1025_, 2, v_exprInit_1031_);
lean_ctor_set(v___x_1025_, 1, v_exprType_1028_);
lean_ctor_set(v___x_1025_, 0, v_expr_1027_);
v___x_1041_ = v___x_1025_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_expr_1027_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_exprType_1028_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_exprInit_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_exprResult_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_proof_1038_);
v___x_1041_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*5, v_nondep_1016_);
v___x_1042_ = lean_apply_2(v_toPure_1039_, lean_box(0), v___x_1041_);
return v___x_1042_;
}
}
else
{
lean_object* v_toPure_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_proof_1048_; lean_object* v___x_1050_; 
lean_dec(v___x_1014_);
v_toPure_1044_ = lean_ctor_get(v_toApplicative_1015_, 1);
lean_inc(v_toPure_1044_);
lean_dec_ref(v_toApplicative_1015_);
lean_inc_ref(v_type_1011_);
v___x_1045_ = l_Lean_mkLambda(v_declName_1010_, v___x_1029_, v_type_1011_, v_proof_1022_);
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1047_ = l_Lean_mkConst(v___x_1046_, v_us_1013_);
lean_inc_ref(v_expr_1027_);
lean_inc_ref(v_exprType_1028_);
v_proof_1048_ = l_Lean_mkApp6(v___x_1047_, v_type_1011_, v_exprType_1028_, v_value_1012_, v___x_1030_, v_expr_1027_, v___x_1045_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v_proof_1048_);
lean_ctor_set(v___x_1025_, 3, v_exprResult_1032_);
lean_ctor_set(v___x_1025_, 2, v_exprInit_1031_);
lean_ctor_set(v___x_1025_, 1, v_exprType_1028_);
lean_ctor_set(v___x_1025_, 0, v_expr_1027_);
v___x_1050_ = v___x_1025_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_expr_1027_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_exprType_1028_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_exprInit_1031_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_exprResult_1032_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_proof_1048_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*5, v_nondep_1016_);
v___x_1051_ = lean_apply_2(v_toPure_1044_, lean_box(0), v___x_1050_);
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1054_, lean_object* v_declName_1055_, lean_object* v_type_1056_, lean_object* v_value_1057_, lean_object* v_us_1058_, lean_object* v___x_1059_, lean_object* v_toApplicative_1060_, lean_object* v_nondep_1061_, lean_object* v_rb_1062_){
_start:
{
uint8_t v_nondep_12657__boxed_1063_; lean_object* v_res_1064_; 
v_nondep_12657__boxed_1063_ = lean_unbox(v_nondep_1061_);
v_res_1064_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1054_, v_declName_1055_, v_type_1056_, v_value_1057_, v_us_1058_, v___x_1059_, v_toApplicative_1060_, v_nondep_12657__boxed_1063_, v_rb_1062_);
lean_dec(v___x_1054_);
return v_res_1064_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1071_, lean_object* v___x_1072_, lean_object* v___f_1073_, lean_object* v_declName_1074_, lean_object* v_val_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_options_1086_; uint8_t v_hasTrace_1087_; 
v_options_1086_ = lean_ctor_get(v___y_1080_, 2);
v_hasTrace_1087_ = lean_ctor_get_uint8(v_options_1086_, sizeof(void*)*1);
if (v_hasTrace_1087_ == 0)
{
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_val_1075_);
lean_dec(v_declName_1074_);
lean_dec(v___f_1073_);
lean_dec(v___x_1072_);
lean_dec(v_cls_1071_);
goto v___jp_1083_;
}
else
{
lean_object* v_inheritedTraceOptions_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_inheritedTraceOptions_1088_ = lean_ctor_get(v___y_1080_, 13);
v___x_1089_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1071_);
v___x_1090_ = l_Lean_Name_append(v___x_1089_, v_cls_1071_);
v___x_1091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1088_, v_options_1086_, v___x_1090_);
lean_dec(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_val_1075_);
lean_dec(v_declName_1074_);
lean_dec(v___f_1073_);
lean_dec(v___x_1072_);
lean_dec(v_cls_1071_);
goto v___jp_1083_;
}
else
{
lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_toMonadRef_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_12267__overap_1106_; lean_object* v___x_1107_; 
v___f_1092_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1093_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1094_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1095_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1093_, v___x_1072_, v___x_1094_);
v___x_1096_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1092_, v___f_1073_, v___x_1095_);
v_toMonadRef_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_toMonadRef_1097_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1100_ = l_Lean_MessageData_ofName(v_declName_1074_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_MessageData_ofExpr(v_val_1075_);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_12267__overap_1106_ = l_Lean_addTrace___redArg(v___x_1076_, v___x_1077_, v_toMonadRef_1097_, v___x_1098_, v_cls_1071_, v___x_1105_);
v___x_1107_ = lean_apply_5(v___x_12267__overap_1106_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, lean_box(0));
return v___x_1107_;
}
}
v___jp_1083_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1108_, lean_object* v___x_1109_, lean_object* v___f_1110_, lean_object* v_declName_1111_, lean_object* v_val_1112_, lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1108_, v___x_1109_, v___f_1110_, v_declName_1111_, v_val_1112_, v___x_1113_, v___x_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v_res_1120_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1127_, lean_object* v___x_1128_, lean_object* v___f_1129_, lean_object* v_declName_1130_, lean_object* v_val_1131_, lean_object* v_val_x27_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_options_1143_; uint8_t v_hasTrace_1144_; 
v_options_1143_ = lean_ctor_get(v___y_1137_, 2);
v_hasTrace_1144_ = lean_ctor_get_uint8(v_options_1143_, sizeof(void*)*1);
if (v_hasTrace_1144_ == 0)
{
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_val_x27_1132_);
lean_dec_ref(v_val_1131_);
lean_dec(v_declName_1130_);
lean_dec(v___f_1129_);
lean_dec(v___x_1128_);
lean_dec(v_cls_1127_);
goto v___jp_1140_;
}
else
{
lean_object* v_inheritedTraceOptions_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_inheritedTraceOptions_1145_ = lean_ctor_get(v___y_1137_, 13);
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1127_);
v___x_1147_ = l_Lean_Name_append(v___x_1146_, v_cls_1127_);
v___x_1148_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1145_, v_options_1143_, v___x_1147_);
lean_dec(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_val_x27_1132_);
lean_dec_ref(v_val_1131_);
lean_dec(v_declName_1130_);
lean_dec(v___f_1129_);
lean_dec(v___x_1128_);
lean_dec(v_cls_1127_);
goto v___jp_1140_;
}
else
{
lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_toMonadRef_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_11949__overap_1167_; lean_object* v___x_1168_; 
v___f_1149_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1151_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1152_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1150_, v___x_1128_, v___x_1151_);
v___x_1153_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1149_, v___f_1129_, v___x_1152_);
v_toMonadRef_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_toMonadRef_1154_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1156_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1157_ = l_Lean_MessageData_ofName(v_declName_1130_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_MessageData_ofExpr(v_val_1131_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_MessageData_ofExpr(v_val_x27_1132_);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_11949__overap_1167_ = l_Lean_addTrace___redArg(v___x_1133_, v___x_1134_, v_toMonadRef_1154_, v___x_1155_, v_cls_1127_, v___x_1166_);
v___x_1168_ = lean_apply_5(v___x_11949__overap_1167_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1168_;
}
}
v___jp_1140_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1169_, lean_object* v___x_1170_, lean_object* v___f_1171_, lean_object* v_declName_1172_, lean_object* v_val_1173_, lean_object* v_val_x27_1174_, lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1169_, v___x_1170_, v___f_1171_, v_declName_1172_, v_val_1173_, v_val_x27_1174_, v___x_1175_, v___x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_toApplicative_1183_, lean_object* v_e_1184_, lean_object* v_xs_1185_, lean_object* v_h_1186_, uint8_t v_nondep_1187_, lean_object* v_toBind_1188_, lean_object* v___f_1189_, lean_object* v_____r_1190_){
_start:
{
lean_object* v_toPure_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_toPure_1191_ = lean_ctor_get(v_toApplicative_1183_, 1);
lean_inc(v_toPure_1191_);
lean_dec_ref(v_toApplicative_1183_);
v___x_1192_ = lean_expr_abstract(v_e_1184_, v_xs_1185_);
v___x_1193_ = lean_expr_abstract(v_h_1186_, v_xs_1185_);
v___x_1194_ = lean_box(v_nondep_1187_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1192_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_apply_2(v_toPure_1191_, lean_box(0), v___x_1196_);
v___x_1198_ = lean_apply_4(v_toBind_1188_, lean_box(0), lean_box(0), v___x_1197_, v___f_1189_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_toApplicative_1199_, lean_object* v_e_1200_, lean_object* v_xs_1201_, lean_object* v_h_1202_, lean_object* v_nondep_1203_, lean_object* v_toBind_1204_, lean_object* v___f_1205_, lean_object* v_____r_1206_){
_start:
{
uint8_t v_nondep_12923__boxed_1207_; lean_object* v_res_1208_; 
v_nondep_12923__boxed_1207_ = lean_unbox(v_nondep_1203_);
v_res_1208_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1199_, v_e_1200_, v_xs_1201_, v_h_1202_, v_nondep_12923__boxed_1207_, v_toBind_1204_, v___f_1205_, v_____r_1206_);
lean_dec_ref(v_h_1202_);
lean_dec_ref(v_xs_1201_);
lean_dec_ref(v_e_1200_);
return v_res_1208_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1212_, lean_object* v___x_1213_, lean_object* v___f_1214_, lean_object* v_declName_1215_, lean_object* v_val_1216_, lean_object* v_e_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_options_1228_; uint8_t v_hasTrace_1229_; 
v_options_1228_ = lean_ctor_get(v___y_1222_, 2);
v_hasTrace_1229_ = lean_ctor_get_uint8(v_options_1228_, sizeof(void*)*1);
if (v_hasTrace_1229_ == 0)
{
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___x_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v_e_1217_);
lean_dec_ref(v_val_1216_);
lean_dec(v_declName_1215_);
lean_dec(v___f_1214_);
lean_dec(v___x_1213_);
lean_dec(v_cls_1212_);
goto v___jp_1225_;
}
else
{
lean_object* v_inheritedTraceOptions_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_inheritedTraceOptions_1230_ = lean_ctor_get(v___y_1222_, 13);
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1212_);
v___x_1232_ = l_Lean_Name_append(v___x_1231_, v_cls_1212_);
v___x_1233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1230_, v_options_1228_, v___x_1232_);
lean_dec(v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___x_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v_e_1217_);
lean_dec_ref(v_val_1216_);
lean_dec(v_declName_1215_);
lean_dec(v___f_1214_);
lean_dec(v___x_1213_);
lean_dec(v_cls_1212_);
goto v___jp_1225_;
}
else
{
lean_object* v___f_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_toMonadRef_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_12129__overap_1252_; lean_object* v___x_1253_; 
v___f_1234_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1236_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1237_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1235_, v___x_1213_, v___x_1236_);
v___x_1238_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1234_, v___f_1214_, v___x_1237_);
v_toMonadRef_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_toMonadRef_1239_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1241_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1242_ = l_Lean_MessageData_ofName(v_declName_1215_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_MessageData_ofExpr(v_val_1216_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_MessageData_ofExpr(v_e_1217_);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_12129__overap_1252_ = l_Lean_addTrace___redArg(v___x_1218_, v___x_1219_, v_toMonadRef_1239_, v___x_1240_, v_cls_1212_, v___x_1251_);
v___x_1253_ = lean_apply_5(v___x_12129__overap_1252_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
return v___x_1253_;
}
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1254_, lean_object* v___x_1255_, lean_object* v___f_1256_, lean_object* v_declName_1257_, lean_object* v_val_1258_, lean_object* v_e_1259_, lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1254_, v___x_1255_, v___f_1256_, v_declName_1257_, v_val_1258_, v_e_1259_, v___x_1260_, v___x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v_res_1267_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_instMonadEIO(lean_box(0));
return v___x_1268_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
v___x_1270_ = l_StateRefT_x27_instMonad___redArg(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1288_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1287_, v___x_1286_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
v___f_1290_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1291_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1290_, v___x_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_toApplicative_1292_, lean_object* v_level_1293_, lean_object* v___x_1294_, lean_object* v_type_1295_, lean_object* v_value_1296_, uint8_t v___x_1297_, lean_object* v_toBind_1298_, lean_object* v___f_1299_, lean_object* v_xs_1300_, uint8_t v_nondep_1301_, lean_object* v___f_1302_, lean_object* v_declName_1303_, lean_object* v_val_1304_, lean_object* v_inst_1305_, lean_object* v_____do__lift_1306_){
_start:
{
if (lean_obj_tag(v_____do__lift_1306_) == 0)
{
lean_object* v_toPure_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_inst_1305_);
lean_dec_ref(v_val_1304_);
lean_dec(v_declName_1303_);
lean_dec(v___f_1302_);
lean_dec_ref(v_xs_1300_);
v_toPure_1307_ = lean_ctor_get(v_toApplicative_1292_, 1);
lean_inc(v_toPure_1307_);
lean_dec_ref(v_toApplicative_1292_);
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_level_1293_);
lean_ctor_set(v___x_1309_, 1, v___x_1294_);
v___x_1310_ = l_Lean_mkConst(v___x_1308_, v___x_1309_);
lean_inc_ref(v_value_1296_);
v___x_1311_ = l_Lean_mkAppB(v___x_1310_, v_type_1295_, v_value_1296_);
v___x_1312_ = lean_box(v___x_1297_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v_value_1296_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_apply_2(v_toPure_1307_, lean_box(0), v___x_1314_);
v___x_1316_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v___x_1315_, v___f_1299_);
return v___x_1316_;
}
else
{
lean_object* v_e_1317_; lean_object* v_h_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v___f_1299_);
lean_dec_ref(v_value_1296_);
lean_dec_ref(v_type_1295_);
lean_dec(v___x_1294_);
lean_dec(v_level_1293_);
v_e_1317_ = lean_ctor_get(v_____do__lift_1306_, 0);
v_h_1318_ = lean_ctor_get(v_____do__lift_1306_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_____do__lift_1306_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1320_ = v_____do__lift_1306_;
v_isShared_1321_ = v_isSharedCheck_1379_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_h_1318_);
lean_inc(v_e_1317_);
lean_dec(v_____do__lift_1306_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1379_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v_toApplicative_1323_; lean_object* v_toFunctor_1324_; lean_object* v_toSeq_1325_; lean_object* v_toSeqLeft_1326_; lean_object* v_toSeqRight_1327_; lean_object* v___f_1328_; lean_object* v___f_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___x_1333_; 
v___x_1322_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1323_ = lean_ctor_get(v___x_1322_, 0);
v_toFunctor_1324_ = lean_ctor_get(v_toApplicative_1323_, 0);
v_toSeq_1325_ = lean_ctor_get(v_toApplicative_1323_, 2);
v_toSeqLeft_1326_ = lean_ctor_get(v_toApplicative_1323_, 3);
v_toSeqRight_1327_ = lean_ctor_get(v_toApplicative_1323_, 4);
v___f_1328_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1329_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1324_, 2);
v___f_1330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1330_, 0, v_toFunctor_1324_);
v___f_1331_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1331_, 0, v_toFunctor_1324_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 0);
lean_ctor_set(v___x_1320_, 1, v___f_1331_);
lean_ctor_set(v___x_1320_, 0, v___f_1330_);
v___x_1333_ = v___x_1320_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___f_1330_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___f_1331_);
v___x_1333_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___f_1334_; lean_object* v___f_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v_toApplicative_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1376_; 
lean_inc(v_toSeqRight_1327_);
v___f_1334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1334_, 0, v_toSeqRight_1327_);
lean_inc(v_toSeqLeft_1326_);
v___f_1335_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1335_, 0, v_toSeqLeft_1326_);
lean_inc(v_toSeq_1325_);
v___f_1336_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1336_, 0, v_toSeq_1325_);
v___x_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1333_);
lean_ctor_set(v___x_1337_, 1, v___f_1328_);
lean_ctor_set(v___x_1337_, 2, v___f_1336_);
lean_ctor_set(v___x_1337_, 3, v___f_1335_);
lean_ctor_set(v___x_1337_, 4, v___f_1334_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___f_1329_);
v___x_1339_ = l_StateRefT_x27_instMonad___redArg(v___x_1338_);
v_toApplicative_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1339_, 1);
lean_dec(v_unused_1377_);
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1376_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_toApplicative_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1376_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_toFunctor_1344_; lean_object* v_toSeq_1345_; lean_object* v_toSeqLeft_1346_; lean_object* v_toSeqRight_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1374_; 
v_toFunctor_1344_ = lean_ctor_get(v_toApplicative_1340_, 0);
v_toSeq_1345_ = lean_ctor_get(v_toApplicative_1340_, 2);
v_toSeqLeft_1346_ = lean_ctor_get(v_toApplicative_1340_, 3);
v_toSeqRight_1347_ = lean_ctor_get(v_toApplicative_1340_, 4);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_toApplicative_1340_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_toApplicative_1340_, 1);
lean_dec(v_unused_1375_);
v___x_1349_ = v_toApplicative_1340_;
v_isShared_1350_ = v_isSharedCheck_1374_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_toSeqRight_1347_);
lean_inc(v_toSeqLeft_1346_);
lean_inc(v_toSeq_1345_);
lean_inc(v_toFunctor_1344_);
lean_dec(v_toApplicative_1340_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1374_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___f_1352_; lean_object* v_cls_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___f_1361_; lean_object* v___x_1363_; 
v___x_1351_ = lean_box(v_nondep_1301_);
lean_inc(v_toBind_1298_);
lean_inc_ref(v_e_1317_);
v___f_1352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1352_, 0, v_toApplicative_1292_);
lean_closure_set(v___f_1352_, 1, v_e_1317_);
lean_closure_set(v___f_1352_, 2, v_xs_1300_);
lean_closure_set(v___f_1352_, 3, v_h_1318_);
lean_closure_set(v___f_1352_, 4, v___x_1351_);
lean_closure_set(v___f_1352_, 5, v_toBind_1298_);
lean_closure_set(v___f_1352_, 6, v___f_1302_);
v_cls_1353_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1354_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1355_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1344_);
v___f_1356_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1356_, 0, v_toFunctor_1344_);
v___f_1357_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1357_, 0, v_toFunctor_1344_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___f_1356_);
lean_ctor_set(v___x_1358_, 1, v___f_1357_);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1359_, 0, v_toSeqRight_1347_);
v___f_1360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1360_, 0, v_toSeqLeft_1346_);
v___f_1361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1361_, 0, v_toSeq_1345_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v___f_1359_);
lean_ctor_set(v___x_1349_, 3, v___f_1360_);
lean_ctor_set(v___x_1349_, 2, v___f_1361_);
lean_ctor_set(v___x_1349_, 1, v___f_1354_);
lean_ctor_set(v___x_1349_, 0, v___x_1358_);
v___x_1363_ = v___x_1349_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___f_1354_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v___f_1361_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v___f_1360_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v___f_1359_);
v___x_1363_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v___f_1355_);
lean_ctor_set(v___x_1342_, 0, v___x_1363_);
v___x_1365_ = v___x_1342_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___f_1355_);
v___x_1365_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___f_1366_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1368_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1369_, 0, v_cls_1353_);
lean_closure_set(v___f_1369_, 1, v___x_1367_);
lean_closure_set(v___f_1369_, 2, v___f_1366_);
lean_closure_set(v___f_1369_, 3, v_declName_1303_);
lean_closure_set(v___f_1369_, 4, v_val_1304_);
lean_closure_set(v___f_1369_, 5, v_e_1317_);
lean_closure_set(v___f_1369_, 6, v___x_1365_);
lean_closure_set(v___f_1369_, 7, v___x_1368_);
v___x_1370_ = lean_apply_2(v_inst_1305_, lean_box(0), v___f_1369_);
v___x_1371_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v___x_1370_, v___f_1352_);
return v___x_1371_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object* v_toApplicative_1380_, lean_object* v_level_1381_, lean_object* v___x_1382_, lean_object* v_type_1383_, lean_object* v_value_1384_, lean_object* v___x_1385_, lean_object* v_toBind_1386_, lean_object* v___f_1387_, lean_object* v_xs_1388_, lean_object* v_nondep_1389_, lean_object* v___f_1390_, lean_object* v_declName_1391_, lean_object* v_val_1392_, lean_object* v_inst_1393_, lean_object* v_____do__lift_1394_){
_start:
{
uint8_t v___x_13110__boxed_1395_; uint8_t v_nondep_13112__boxed_1396_; lean_object* v_res_1397_; 
v___x_13110__boxed_1395_ = lean_unbox(v___x_1385_);
v_nondep_13112__boxed_1396_ = lean_unbox(v_nondep_1389_);
v_res_1397_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1380_, v_level_1381_, v___x_1382_, v_type_1383_, v_value_1384_, v___x_13110__boxed_1395_, v_toBind_1386_, v___f_1387_, v_xs_1388_, v_nondep_13112__boxed_1396_, v___f_1390_, v_declName_1391_, v_val_1392_, v_inst_1393_, v_____do__lift_1394_);
return v_res_1397_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1408_ = lean_unsigned_to_nat(8u);
v___x_1409_ = lean_unsigned_to_nat(287u);
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1412_ = l_mkPanicMessageWithDecl(v___x_1411_, v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1413_, lean_object* v_type_1414_, lean_object* v_fst_1415_, lean_object* v___x_1416_, lean_object* v_value_1417_, uint8_t v_nondep_1418_, uint8_t v_fst_1419_, lean_object* v_toApplicative_1420_, lean_object* v___x_1421_, lean_object* v_us_1422_, lean_object* v_snd_1423_, lean_object* v_inst_1424_, lean_object* v_rb_1425_){
_start:
{
lean_object* v_expr_1426_; lean_object* v_exprType_1427_; lean_object* v_exprInit_1428_; lean_object* v_exprResult_1429_; lean_object* v_proof_1430_; uint8_t v_modified_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1482_; 
v_expr_1426_ = lean_ctor_get(v_rb_1425_, 0);
v_exprType_1427_ = lean_ctor_get(v_rb_1425_, 1);
v_exprInit_1428_ = lean_ctor_get(v_rb_1425_, 2);
v_exprResult_1429_ = lean_ctor_get(v_rb_1425_, 3);
v_proof_1430_ = lean_ctor_get(v_rb_1425_, 4);
v_modified_1431_ = lean_ctor_get_uint8(v_rb_1425_, sizeof(void*)*5);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_rb_1425_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1433_ = v_rb_1425_;
v_isShared_1434_ = v_isSharedCheck_1482_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_proof_1430_);
lean_inc(v_exprResult_1429_);
lean_inc(v_exprInit_1428_);
lean_inc(v_exprType_1427_);
lean_inc(v_expr_1426_);
lean_dec(v_rb_1425_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1482_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_expr_has_loose_bvar(v_exprType_1427_, v___x_1435_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v_expr_1439_; lean_object* v_exprType_1440_; lean_object* v___x_1441_; lean_object* v_exprInit_1442_; lean_object* v_exprResult_1443_; 
lean_dec_ref(v_inst_1424_);
v___x_1437_ = 0;
lean_inc_ref_n(v_type_1414_, 3);
lean_inc_n(v_declName_1413_, 3);
v___x_1438_ = l_Lean_mkLambda(v_declName_1413_, v___x_1437_, v_type_1414_, v_expr_1426_);
lean_inc_ref_n(v_fst_1415_, 2);
lean_inc_ref(v___x_1438_);
v_expr_1439_ = l_Lean_Expr_app___override(v___x_1438_, v_fst_1415_);
v_exprType_1440_ = lean_expr_lower_loose_bvars(v_exprType_1427_, v___x_1416_, v___x_1416_);
lean_dec_ref(v_exprType_1427_);
v___x_1441_ = l_Lean_mkLambda(v_declName_1413_, v___x_1437_, v_type_1414_, v_exprInit_1428_);
lean_inc_ref(v_value_1417_);
lean_inc_ref(v___x_1441_);
v_exprInit_1442_ = l_Lean_Expr_app___override(v___x_1441_, v_value_1417_);
v_exprResult_1443_ = l_Lean_Expr_letE___override(v_declName_1413_, v_type_1414_, v_fst_1415_, v_exprResult_1429_, v_nondep_1418_);
if (v_fst_1419_ == 0)
{
lean_dec_ref(v_snd_1423_);
lean_dec_ref(v_fst_1415_);
if (v_modified_1431_ == 0)
{
lean_object* v_toPure_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_proof_1447_; lean_object* v___x_1449_; 
lean_dec_ref(v___x_1441_);
lean_dec_ref(v___x_1438_);
lean_dec_ref(v_proof_1430_);
lean_dec(v_us_1422_);
lean_dec_ref(v_value_1417_);
lean_dec_ref(v_type_1414_);
lean_dec(v_declName_1413_);
v_toPure_1444_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1444_);
lean_dec_ref(v_toApplicative_1420_);
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1446_ = l_Lean_mkConst(v___x_1445_, v___x_1421_);
lean_inc_ref(v_expr_1439_);
lean_inc_ref(v_exprType_1440_);
v_proof_1447_ = l_Lean_mkAppB(v___x_1446_, v_exprType_1440_, v_expr_1439_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v_proof_1447_);
lean_ctor_set(v___x_1433_, 3, v_exprResult_1443_);
lean_ctor_set(v___x_1433_, 2, v_exprInit_1442_);
lean_ctor_set(v___x_1433_, 1, v_exprType_1440_);
lean_ctor_set(v___x_1433_, 0, v_expr_1439_);
v___x_1449_ = v___x_1433_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_expr_1439_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_exprType_1440_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_exprInit_1442_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_exprResult_1443_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_proof_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1451_, sizeof(void*)*5, v_modified_1431_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_apply_2(v_toPure_1444_, lean_box(0), v___x_1449_);
return v___x_1450_;
}
}
else
{
lean_object* v_toPure_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_proof_1456_; lean_object* v___x_1458_; 
lean_dec(v___x_1421_);
v_toPure_1452_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1452_);
lean_dec_ref(v_toApplicative_1420_);
lean_inc_ref(v_type_1414_);
v___x_1453_ = l_Lean_mkLambda(v_declName_1413_, v___x_1437_, v_type_1414_, v_proof_1430_);
v___x_1454_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1455_ = l_Lean_mkConst(v___x_1454_, v_us_1422_);
lean_inc_ref(v_exprType_1440_);
v_proof_1456_ = l_Lean_mkApp6(v___x_1455_, v_type_1414_, v_exprType_1440_, v_value_1417_, v___x_1441_, v___x_1438_, v___x_1453_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v_proof_1456_);
lean_ctor_set(v___x_1433_, 3, v_exprResult_1443_);
lean_ctor_set(v___x_1433_, 2, v_exprInit_1442_);
lean_ctor_set(v___x_1433_, 1, v_exprType_1440_);
lean_ctor_set(v___x_1433_, 0, v_expr_1439_);
v___x_1458_ = v___x_1433_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_expr_1439_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_exprType_1440_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_exprInit_1442_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_exprResult_1443_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_proof_1456_);
v___x_1458_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; 
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*5, v_nondep_1418_);
v___x_1459_ = lean_apply_2(v_toPure_1452_, lean_box(0), v___x_1458_);
return v___x_1459_;
}
}
}
else
{
lean_dec(v___x_1421_);
if (v_modified_1431_ == 0)
{
lean_object* v_toPure_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_proof_1464_; lean_object* v___x_1466_; 
lean_dec_ref(v___x_1438_);
lean_dec_ref(v_proof_1430_);
lean_dec(v_declName_1413_);
v_toPure_1461_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1461_);
lean_dec_ref(v_toApplicative_1420_);
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1463_ = l_Lean_mkConst(v___x_1462_, v_us_1422_);
lean_inc_ref(v_exprType_1440_);
v_proof_1464_ = l_Lean_mkApp6(v___x_1463_, v_type_1414_, v_exprType_1440_, v_value_1417_, v_fst_1415_, v___x_1441_, v_snd_1423_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v_proof_1464_);
lean_ctor_set(v___x_1433_, 3, v_exprResult_1443_);
lean_ctor_set(v___x_1433_, 2, v_exprInit_1442_);
lean_ctor_set(v___x_1433_, 1, v_exprType_1440_);
lean_ctor_set(v___x_1433_, 0, v_expr_1439_);
v___x_1466_ = v___x_1433_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_expr_1439_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_exprType_1440_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_exprInit_1442_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_exprResult_1443_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_proof_1464_);
v___x_1466_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
lean_ctor_set_uint8(v___x_1466_, sizeof(void*)*5, v_nondep_1418_);
v___x_1467_ = lean_apply_2(v_toPure_1461_, lean_box(0), v___x_1466_);
return v___x_1467_;
}
}
else
{
lean_object* v_toPure_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v_proof_1473_; lean_object* v___x_1475_; 
v_toPure_1469_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1469_);
lean_dec_ref(v_toApplicative_1420_);
lean_inc_ref(v_type_1414_);
v___x_1470_ = l_Lean_mkLambda(v_declName_1413_, v___x_1437_, v_type_1414_, v_proof_1430_);
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1472_ = l_Lean_mkConst(v___x_1471_, v_us_1422_);
lean_inc_ref(v_exprType_1440_);
v_proof_1473_ = l_Lean_mkApp8(v___x_1472_, v_type_1414_, v_exprType_1440_, v_value_1417_, v_fst_1415_, v___x_1441_, v___x_1438_, v_snd_1423_, v___x_1470_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v_proof_1473_);
lean_ctor_set(v___x_1433_, 3, v_exprResult_1443_);
lean_ctor_set(v___x_1433_, 2, v_exprInit_1442_);
lean_ctor_set(v___x_1433_, 1, v_exprType_1440_);
lean_ctor_set(v___x_1433_, 0, v_expr_1439_);
v___x_1475_ = v___x_1433_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_expr_1439_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_exprType_1440_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_exprInit_1442_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_exprResult_1443_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_proof_1473_);
v___x_1475_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; 
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*5, v_nondep_1418_);
v___x_1476_ = lean_apply_2(v_toPure_1469_, lean_box(0), v___x_1475_);
return v___x_1476_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_del_object(v___x_1433_);
lean_dec_ref(v_proof_1430_);
lean_dec_ref(v_exprResult_1429_);
lean_dec_ref(v_exprInit_1428_);
lean_dec_ref(v_exprType_1427_);
lean_dec_ref(v_expr_1426_);
lean_dec_ref(v_snd_1423_);
lean_dec(v_us_1422_);
lean_dec(v___x_1421_);
lean_dec_ref(v_toApplicative_1420_);
lean_dec_ref(v_value_1417_);
lean_dec_ref(v_fst_1415_);
lean_dec_ref(v_type_1414_);
lean_dec(v_declName_1413_);
v___x_1478_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1479_ = l_instInhabitedOfMonad___redArg(v_inst_1424_, v___x_1478_);
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1481_ = l_panic___redArg(v___x_1479_, v___x_1480_);
lean_dec(v___x_1479_);
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1483_, lean_object* v_type_1484_, lean_object* v_fst_1485_, lean_object* v___x_1486_, lean_object* v_value_1487_, lean_object* v_nondep_1488_, lean_object* v_fst_1489_, lean_object* v_toApplicative_1490_, lean_object* v___x_1491_, lean_object* v_us_1492_, lean_object* v_snd_1493_, lean_object* v_inst_1494_, lean_object* v_rb_1495_){
_start:
{
uint8_t v_nondep_13328__boxed_1496_; uint8_t v_fst_13329__boxed_1497_; lean_object* v_res_1498_; 
v_nondep_13328__boxed_1496_ = lean_unbox(v_nondep_1488_);
v_fst_13329__boxed_1497_ = lean_unbox(v_fst_1489_);
v_res_1498_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1483_, v_type_1484_, v_fst_1485_, v___x_1486_, v_value_1487_, v_nondep_13328__boxed_1496_, v_fst_13329__boxed_1497_, v_toApplicative_1490_, v___x_1491_, v_us_1492_, v_snd_1493_, v_inst_1494_, v_rb_1495_);
lean_dec(v___x_1486_);
return v_res_1498_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0));
v___x_1504_ = lean_unsigned_to_nat(34u);
v___x_1505_ = lean_unsigned_to_nat(217u);
v___x_1506_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1507_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1508_ = l_mkPanicMessageWithDecl(v___x_1507_, v___x_1506_, v___x_1505_, v___x_1504_, v___x_1503_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1509_, lean_object* v_type_1510_, lean_object* v_value_1511_, uint8_t v_nondep_1512_, lean_object* v_toApplicative_1513_, lean_object* v___x_1514_, lean_object* v_us_1515_, lean_object* v_decl_1516_, lean_object* v_x_1517_, lean_object* v_i_1518_, lean_object* v_xs_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_info_1524_, lean_object* v_fixed_1525_, lean_object* v_used_1526_, lean_object* v_body_1527_, lean_object* v_toBind_1528_, lean_object* v_withNewLemmas_1529_, lean_object* v_val_x27_1530_, lean_object* v_val_1531_, uint8_t v___x_1532_, lean_object* v_____r_1533_){
_start:
{
uint8_t v___y_1535_; lean_object* v___y_1536_; uint8_t v___y_1552_; uint8_t v___x_1554_; 
v___x_1554_ = lean_expr_eqv(v_val_1531_, v_val_x27_1530_);
if (v___x_1554_ == 0)
{
v___y_1552_ = v_nondep_1512_;
goto v___jp_1551_;
}
else
{
v___y_1552_ = v___x_1532_;
goto v___jp_1551_;
}
v___jp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1537_ = lean_box(v_nondep_1512_);
v___x_1538_ = lean_box(v___y_1535_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1539_, 0, v_declName_1509_);
lean_closure_set(v___f_1539_, 1, v_type_1510_);
lean_closure_set(v___f_1539_, 2, v___y_1536_);
lean_closure_set(v___f_1539_, 3, v_value_1511_);
lean_closure_set(v___f_1539_, 4, v___x_1537_);
lean_closure_set(v___f_1539_, 5, v_toApplicative_1513_);
lean_closure_set(v___f_1539_, 6, v___x_1514_);
lean_closure_set(v___f_1539_, 7, v___x_1538_);
lean_closure_set(v___f_1539_, 8, v_us_1515_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_decl_1516_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_mk_empty_array_with_capacity(v___x_1542_);
lean_inc_ref(v_x_1517_);
v___x_1544_ = lean_array_push(v___x_1543_, v_x_1517_);
v___x_1545_ = lean_nat_add(v_i_1518_, v___x_1542_);
v___x_1546_ = lean_array_push(v_xs_1519_, v_x_1517_);
lean_inc_ref(v_inst_1522_);
lean_inc_ref(v_inst_1520_);
v___x_1547_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_info_1524_, v_fixed_1525_, v_used_1526_, v_body_1527_, v___x_1545_, v___x_1546_);
v___x_1548_ = lean_apply_4(v_toBind_1528_, lean_box(0), lean_box(0), v___x_1547_, v___f_1539_);
v___x_1549_ = lean_apply_3(v_withNewLemmas_1529_, lean_box(0), v___x_1544_, v___x_1548_);
v___x_1550_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1522_, v_inst_1520_, v___x_1541_, v___x_1549_);
return v___x_1550_;
}
v___jp_1551_:
{
if (v___y_1552_ == 0)
{
lean_inc_ref(v_value_1511_);
v___y_1535_ = v___y_1552_;
v___y_1536_ = v_value_1511_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_expr_abstract(v_val_x27_1530_, v_xs_1519_);
v___y_1535_ = v___y_1552_;
v___y_1536_ = v___x_1553_;
goto v___jp_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1555_ = _args[0];
lean_object* v_type_1556_ = _args[1];
lean_object* v_value_1557_ = _args[2];
lean_object* v_nondep_1558_ = _args[3];
lean_object* v_toApplicative_1559_ = _args[4];
lean_object* v___x_1560_ = _args[5];
lean_object* v_us_1561_ = _args[6];
lean_object* v_decl_1562_ = _args[7];
lean_object* v_x_1563_ = _args[8];
lean_object* v_i_1564_ = _args[9];
lean_object* v_xs_1565_ = _args[10];
lean_object* v_inst_1566_ = _args[11];
lean_object* v_inst_1567_ = _args[12];
lean_object* v_inst_1568_ = _args[13];
lean_object* v_inst_1569_ = _args[14];
lean_object* v_info_1570_ = _args[15];
lean_object* v_fixed_1571_ = _args[16];
lean_object* v_used_1572_ = _args[17];
lean_object* v_body_1573_ = _args[18];
lean_object* v_toBind_1574_ = _args[19];
lean_object* v_withNewLemmas_1575_ = _args[20];
lean_object* v_val_x27_1576_ = _args[21];
lean_object* v_val_1577_ = _args[22];
lean_object* v___x_1578_ = _args[23];
lean_object* v_____r_1579_ = _args[24];
_start:
{
uint8_t v_nondep_13584__boxed_1580_; uint8_t v___x_13591__boxed_1581_; lean_object* v_res_1582_; 
v_nondep_13584__boxed_1580_ = lean_unbox(v_nondep_1558_);
v___x_13591__boxed_1581_ = lean_unbox(v___x_1578_);
v_res_1582_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1555_, v_type_1556_, v_value_1557_, v_nondep_13584__boxed_1580_, v_toApplicative_1559_, v___x_1560_, v_us_1561_, v_decl_1562_, v_x_1563_, v_i_1564_, v_xs_1565_, v_inst_1566_, v_inst_1567_, v_inst_1568_, v_inst_1569_, v_info_1570_, v_fixed_1571_, v_used_1572_, v_body_1573_, v_toBind_1574_, v_withNewLemmas_1575_, v_val_x27_1576_, v_val_1577_, v___x_13591__boxed_1581_, v_____r_1579_);
lean_dec_ref(v_val_1577_);
lean_dec_ref(v_val_x27_1576_);
lean_dec(v_i_1564_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1583_, lean_object* v_type_1584_, lean_object* v_value_1585_, uint8_t v_nondep_1586_, lean_object* v_toApplicative_1587_, lean_object* v___x_1588_, lean_object* v_us_1589_, lean_object* v_decl_1590_, lean_object* v_x_1591_, lean_object* v_i_1592_, lean_object* v_xs_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_info_1598_, lean_object* v_fixed_1599_, lean_object* v_used_1600_, lean_object* v_body_1601_, lean_object* v_toBind_1602_, lean_object* v_withNewLemmas_1603_, lean_object* v_val_1604_, uint8_t v___x_1605_, lean_object* v_val_x27_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v_toApplicative_1608_; lean_object* v_toFunctor_1609_; lean_object* v_toSeq_1610_; lean_object* v_toSeqLeft_1611_; lean_object* v_toSeqRight_1612_; lean_object* v___f_1613_; lean_object* v___f_1614_; lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_toApplicative_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1661_; 
v___x_1607_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1608_ = lean_ctor_get(v___x_1607_, 0);
v_toFunctor_1609_ = lean_ctor_get(v_toApplicative_1608_, 0);
v_toSeq_1610_ = lean_ctor_get(v_toApplicative_1608_, 2);
v_toSeqLeft_1611_ = lean_ctor_get(v_toApplicative_1608_, 3);
v_toSeqRight_1612_ = lean_ctor_get(v_toApplicative_1608_, 4);
v___f_1613_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1614_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1609_, 2);
v___f_1615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1615_, 0, v_toFunctor_1609_);
v___f_1616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1616_, 0, v_toFunctor_1609_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___f_1615_);
lean_ctor_set(v___x_1617_, 1, v___f_1616_);
lean_inc(v_toSeqRight_1612_);
v___f_1618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1618_, 0, v_toSeqRight_1612_);
lean_inc(v_toSeqLeft_1611_);
v___f_1619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1619_, 0, v_toSeqLeft_1611_);
lean_inc(v_toSeq_1610_);
v___f_1620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1620_, 0, v_toSeq_1610_);
v___x_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1617_);
lean_ctor_set(v___x_1621_, 1, v___f_1613_);
lean_ctor_set(v___x_1621_, 2, v___f_1620_);
lean_ctor_set(v___x_1621_, 3, v___f_1619_);
lean_ctor_set(v___x_1621_, 4, v___f_1618_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v___f_1614_);
v___x_1623_ = l_StateRefT_x27_instMonad___redArg(v___x_1622_);
v_toApplicative_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1623_, 1);
lean_dec(v_unused_1662_);
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1661_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_toApplicative_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1661_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v_toFunctor_1628_; lean_object* v_toSeq_1629_; lean_object* v_toSeqLeft_1630_; lean_object* v_toSeqRight_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1659_; 
v_toFunctor_1628_ = lean_ctor_get(v_toApplicative_1624_, 0);
v_toSeq_1629_ = lean_ctor_get(v_toApplicative_1624_, 2);
v_toSeqLeft_1630_ = lean_ctor_get(v_toApplicative_1624_, 3);
v_toSeqRight_1631_ = lean_ctor_get(v_toApplicative_1624_, 4);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_toApplicative_1624_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_toApplicative_1624_, 1);
lean_dec(v_unused_1660_);
v___x_1633_ = v_toApplicative_1624_;
v_isShared_1634_ = v_isSharedCheck_1659_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_toSeqRight_1631_);
lean_inc(v_toSeqLeft_1630_);
lean_inc(v_toSeq_1629_);
lean_inc(v_toFunctor_1628_);
lean_dec(v_toApplicative_1624_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1659_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___f_1637_; lean_object* v_cls_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___x_1648_; 
v___x_1635_ = lean_box(v_nondep_1586_);
v___x_1636_ = lean_box(v___x_1605_);
lean_inc_ref(v_val_1604_);
lean_inc_ref(v_val_x27_1606_);
lean_inc(v_toBind_1602_);
lean_inc(v_inst_1595_);
lean_inc(v_declName_1583_);
v___f_1637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 25, 24);
lean_closure_set(v___f_1637_, 0, v_declName_1583_);
lean_closure_set(v___f_1637_, 1, v_type_1584_);
lean_closure_set(v___f_1637_, 2, v_value_1585_);
lean_closure_set(v___f_1637_, 3, v___x_1635_);
lean_closure_set(v___f_1637_, 4, v_toApplicative_1587_);
lean_closure_set(v___f_1637_, 5, v___x_1588_);
lean_closure_set(v___f_1637_, 6, v_us_1589_);
lean_closure_set(v___f_1637_, 7, v_decl_1590_);
lean_closure_set(v___f_1637_, 8, v_x_1591_);
lean_closure_set(v___f_1637_, 9, v_i_1592_);
lean_closure_set(v___f_1637_, 10, v_xs_1593_);
lean_closure_set(v___f_1637_, 11, v_inst_1594_);
lean_closure_set(v___f_1637_, 12, v_inst_1595_);
lean_closure_set(v___f_1637_, 13, v_inst_1596_);
lean_closure_set(v___f_1637_, 14, v_inst_1597_);
lean_closure_set(v___f_1637_, 15, v_info_1598_);
lean_closure_set(v___f_1637_, 16, v_fixed_1599_);
lean_closure_set(v___f_1637_, 17, v_used_1600_);
lean_closure_set(v___f_1637_, 18, v_body_1601_);
lean_closure_set(v___f_1637_, 19, v_toBind_1602_);
lean_closure_set(v___f_1637_, 20, v_withNewLemmas_1603_);
lean_closure_set(v___f_1637_, 21, v_val_x27_1606_);
lean_closure_set(v___f_1637_, 22, v_val_1604_);
lean_closure_set(v___f_1637_, 23, v___x_1636_);
v_cls_1638_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1639_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1640_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1628_);
v___f_1641_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1641_, 0, v_toFunctor_1628_);
v___f_1642_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1642_, 0, v_toFunctor_1628_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___f_1641_);
lean_ctor_set(v___x_1643_, 1, v___f_1642_);
v___f_1644_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1644_, 0, v_toSeqRight_1631_);
v___f_1645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1645_, 0, v_toSeqLeft_1630_);
v___f_1646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1646_, 0, v_toSeq_1629_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 4, v___f_1644_);
lean_ctor_set(v___x_1633_, 3, v___f_1645_);
lean_ctor_set(v___x_1633_, 2, v___f_1646_);
lean_ctor_set(v___x_1633_, 1, v___f_1639_);
lean_ctor_set(v___x_1633_, 0, v___x_1643_);
v___x_1648_ = v___x_1633_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___f_1639_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v___f_1646_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v___f_1645_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v___f_1644_);
v___x_1648_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___f_1640_);
lean_ctor_set(v___x_1626_, 0, v___x_1648_);
v___x_1650_ = v___x_1626_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___f_1640_);
v___x_1650_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___f_1651_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1652_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1654_, 0, v_cls_1638_);
lean_closure_set(v___f_1654_, 1, v___x_1652_);
lean_closure_set(v___f_1654_, 2, v___f_1651_);
lean_closure_set(v___f_1654_, 3, v_declName_1583_);
lean_closure_set(v___f_1654_, 4, v_val_1604_);
lean_closure_set(v___f_1654_, 5, v_val_x27_1606_);
lean_closure_set(v___f_1654_, 6, v___x_1650_);
lean_closure_set(v___f_1654_, 7, v___x_1653_);
v___x_1655_ = lean_apply_2(v_inst_1595_, lean_box(0), v___f_1654_);
v___x_1656_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1655_, v___f_1637_);
return v___x_1656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1663_ = _args[0];
lean_object* v_type_1664_ = _args[1];
lean_object* v_value_1665_ = _args[2];
lean_object* v_nondep_1666_ = _args[3];
lean_object* v_toApplicative_1667_ = _args[4];
lean_object* v___x_1668_ = _args[5];
lean_object* v_us_1669_ = _args[6];
lean_object* v_decl_1670_ = _args[7];
lean_object* v_x_1671_ = _args[8];
lean_object* v_i_1672_ = _args[9];
lean_object* v_xs_1673_ = _args[10];
lean_object* v_inst_1674_ = _args[11];
lean_object* v_inst_1675_ = _args[12];
lean_object* v_inst_1676_ = _args[13];
lean_object* v_inst_1677_ = _args[14];
lean_object* v_info_1678_ = _args[15];
lean_object* v_fixed_1679_ = _args[16];
lean_object* v_used_1680_ = _args[17];
lean_object* v_body_1681_ = _args[18];
lean_object* v_toBind_1682_ = _args[19];
lean_object* v_withNewLemmas_1683_ = _args[20];
lean_object* v_val_1684_ = _args[21];
lean_object* v___x_1685_ = _args[22];
lean_object* v_val_x27_1686_ = _args[23];
_start:
{
uint8_t v_nondep_13615__boxed_1687_; uint8_t v___x_13622__boxed_1688_; lean_object* v_res_1689_; 
v_nondep_13615__boxed_1687_ = lean_unbox(v_nondep_1666_);
v___x_13622__boxed_1688_ = lean_unbox(v___x_1685_);
v_res_1689_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1663_, v_type_1664_, v_value_1665_, v_nondep_13615__boxed_1687_, v_toApplicative_1667_, v___x_1668_, v_us_1669_, v_decl_1670_, v_x_1671_, v_i_1672_, v_xs_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_info_1678_, v_fixed_1679_, v_used_1680_, v_body_1681_, v_toBind_1682_, v_withNewLemmas_1683_, v_val_1684_, v___x_13622__boxed_1688_, v_val_x27_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1690_, lean_object* v_declName_1691_, lean_object* v_type_1692_, lean_object* v_value_1693_, uint8_t v_nondep_1694_, lean_object* v_toApplicative_1695_, lean_object* v___x_1696_, lean_object* v_us_1697_, lean_object* v_inst_1698_, lean_object* v_x_1699_, lean_object* v_i_1700_, lean_object* v_xs_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_info_1705_, lean_object* v_fixed_1706_, lean_object* v_used_1707_, lean_object* v_body_1708_, lean_object* v_toBind_1709_, lean_object* v_withNewLemmas_1710_, lean_object* v_____x_1711_){
_start:
{
lean_object* v_snd_1712_; lean_object* v_fst_1713_; lean_object* v_fst_1714_; lean_object* v_snd_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1734_; 
v_snd_1712_ = lean_ctor_get(v_____x_1711_, 1);
lean_inc(v_snd_1712_);
v_fst_1713_ = lean_ctor_get(v_____x_1711_, 0);
lean_inc(v_fst_1713_);
lean_dec_ref(v_____x_1711_);
v_fst_1714_ = lean_ctor_get(v_snd_1712_, 0);
v_snd_1715_ = lean_ctor_get(v_snd_1712_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_snd_1712_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1717_ = v_snd_1712_;
v_isShared_1718_ = v_isSharedCheck_1734_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_snd_1715_);
lean_inc(v_fst_1714_);
lean_dec(v_snd_1712_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1734_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_box(0);
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 1);
lean_ctor_set(v___x_1717_, 1, v___x_1719_);
lean_ctor_set(v___x_1717_, 0, v_decl_1690_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_decl_1690_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_box(v_nondep_1694_);
lean_inc_ref_n(v_inst_1698_, 2);
v___f_1724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1724_, 0, v_declName_1691_);
lean_closure_set(v___f_1724_, 1, v_type_1692_);
lean_closure_set(v___f_1724_, 2, v_fst_1713_);
lean_closure_set(v___f_1724_, 3, v___x_1722_);
lean_closure_set(v___f_1724_, 4, v_value_1693_);
lean_closure_set(v___f_1724_, 5, v___x_1723_);
lean_closure_set(v___f_1724_, 6, v_fst_1714_);
lean_closure_set(v___f_1724_, 7, v_toApplicative_1695_);
lean_closure_set(v___f_1724_, 8, v___x_1696_);
lean_closure_set(v___f_1724_, 9, v_us_1697_);
lean_closure_set(v___f_1724_, 10, v_snd_1715_);
lean_closure_set(v___f_1724_, 11, v_inst_1698_);
v___x_1725_ = lean_mk_empty_array_with_capacity(v___x_1722_);
lean_inc_ref(v_x_1699_);
v___x_1726_ = lean_array_push(v___x_1725_, v_x_1699_);
v___x_1727_ = lean_nat_add(v_i_1700_, v___x_1722_);
v___x_1728_ = lean_array_push(v_xs_1701_, v_x_1699_);
lean_inc_ref(v_inst_1703_);
v___x_1729_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1698_, v_inst_1702_, v_inst_1703_, v_inst_1704_, v_info_1705_, v_fixed_1706_, v_used_1707_, v_body_1708_, v___x_1727_, v___x_1728_);
v___x_1730_ = lean_apply_4(v_toBind_1709_, lean_box(0), lean_box(0), v___x_1729_, v___f_1724_);
v___x_1731_ = lean_apply_3(v_withNewLemmas_1710_, lean_box(0), v___x_1726_, v___x_1730_);
v___x_1732_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1703_, v_inst_1698_, v___x_1721_, v___x_1731_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1735_ = _args[0];
lean_object* v_declName_1736_ = _args[1];
lean_object* v_type_1737_ = _args[2];
lean_object* v_value_1738_ = _args[3];
lean_object* v_nondep_1739_ = _args[4];
lean_object* v_toApplicative_1740_ = _args[5];
lean_object* v___x_1741_ = _args[6];
lean_object* v_us_1742_ = _args[7];
lean_object* v_inst_1743_ = _args[8];
lean_object* v_x_1744_ = _args[9];
lean_object* v_i_1745_ = _args[10];
lean_object* v_xs_1746_ = _args[11];
lean_object* v_inst_1747_ = _args[12];
lean_object* v_inst_1748_ = _args[13];
lean_object* v_inst_1749_ = _args[14];
lean_object* v_info_1750_ = _args[15];
lean_object* v_fixed_1751_ = _args[16];
lean_object* v_used_1752_ = _args[17];
lean_object* v_body_1753_ = _args[18];
lean_object* v_toBind_1754_ = _args[19];
lean_object* v_withNewLemmas_1755_ = _args[20];
lean_object* v_____x_1756_ = _args[21];
_start:
{
uint8_t v_nondep_13557__boxed_1757_; lean_object* v_res_1758_; 
v_nondep_13557__boxed_1757_ = lean_unbox(v_nondep_1739_);
v_res_1758_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1735_, v_declName_1736_, v_type_1737_, v_value_1738_, v_nondep_13557__boxed_1757_, v_toApplicative_1740_, v___x_1741_, v_us_1742_, v_inst_1743_, v_x_1744_, v_i_1745_, v_xs_1746_, v_inst_1747_, v_inst_1748_, v_inst_1749_, v_info_1750_, v_fixed_1751_, v_used_1752_, v_body_1753_, v_toBind_1754_, v_withNewLemmas_1755_, v_____x_1756_);
lean_dec(v_i_1745_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1759_ = _args[0];
lean_object* v_declName_1760_ = _args[1];
lean_object* v_type_1761_ = _args[2];
lean_object* v_value_1762_ = _args[3];
lean_object* v_us_1763_ = _args[4];
lean_object* v___x_1764_ = _args[5];
lean_object* v_toApplicative_1765_ = _args[6];
lean_object* v_nondep_1766_ = _args[7];
lean_object* v_i_1767_ = _args[8];
lean_object* v_xs_1768_ = _args[9];
lean_object* v_inst_1769_ = _args[10];
lean_object* v_inst_1770_ = _args[11];
lean_object* v_inst_1771_ = _args[12];
lean_object* v_inst_1772_ = _args[13];
lean_object* v_info_1773_ = _args[14];
lean_object* v_fixed_1774_ = _args[15];
lean_object* v_used_1775_ = _args[16];
lean_object* v_body_1776_ = _args[17];
lean_object* v_toBind_1777_ = _args[18];
lean_object* v_____r_1778_ = _args[19];
_start:
{
uint8_t v_nondep_13540__boxed_1779_; lean_object* v_res_1780_; 
v_nondep_13540__boxed_1779_ = lean_unbox(v_nondep_1766_);
v_res_1780_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1759_, v_declName_1760_, v_type_1761_, v_value_1762_, v_us_1763_, v___x_1764_, v_toApplicative_1765_, v_nondep_13540__boxed_1779_, v_i_1767_, v_xs_1768_, v_inst_1769_, v_inst_1770_, v_inst_1771_, v_inst_1772_, v_info_1773_, v_fixed_1774_, v_used_1775_, v_body_1776_, v_toBind_1777_, v_____r_1778_);
lean_dec(v_i_1767_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_info_1785_, lean_object* v_fixed_1786_, lean_object* v_used_1787_, lean_object* v_e_1788_, lean_object* v_i_1789_, lean_object* v_xs_1790_){
_start:
{
lean_object* v_haveInfo_1796_; lean_object* v_body_1797_; lean_object* v_bodyType_1798_; lean_object* v_level_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_haveInfo_1796_ = lean_ctor_get(v_info_1785_, 0);
v_body_1797_ = lean_ctor_get(v_info_1785_, 3);
v_bodyType_1798_ = lean_ctor_get(v_info_1785_, 4);
v_level_1799_ = lean_ctor_get(v_info_1785_, 5);
v___x_1800_ = lean_array_get_size(v_haveInfo_1796_);
v___x_1801_ = lean_nat_dec_lt(v_i_1789_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v_toApplicative_1802_; lean_object* v_toBind_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1864_; 
lean_inc(v_level_1799_);
lean_inc_ref(v_bodyType_1798_);
lean_inc_ref(v_body_1797_);
lean_dec(v_i_1789_);
lean_dec_ref(v_used_1787_);
lean_dec_ref(v_fixed_1786_);
lean_dec_ref(v_info_1785_);
lean_dec_ref(v_inst_1783_);
v_toApplicative_1802_ = lean_ctor_get(v_inst_1781_, 0);
v_toBind_1803_ = lean_ctor_get(v_inst_1781_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_inst_1781_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1805_ = v_inst_1781_;
v_isShared_1806_ = v_isSharedCheck_1864_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_toBind_1803_);
lean_inc(v_toApplicative_1802_);
lean_dec(v_inst_1781_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1864_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_toApplicative_1808_; lean_object* v_toFunctor_1809_; lean_object* v_toSeq_1810_; lean_object* v_toSeqLeft_1811_; lean_object* v_toSeqRight_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___f_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___f_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1807_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1808_ = lean_ctor_get(v___x_1807_, 0);
v_toFunctor_1809_ = lean_ctor_get(v_toApplicative_1808_, 0);
v_toSeq_1810_ = lean_ctor_get(v_toApplicative_1808_, 2);
v_toSeqLeft_1811_ = lean_ctor_get(v_toApplicative_1808_, 3);
v_toSeqRight_1812_ = lean_ctor_get(v_toApplicative_1808_, 4);
v___f_1813_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1814_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1809_, 2);
v___f_1815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1815_, 0, v_toFunctor_1809_);
v___f_1816_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1816_, 0, v_toFunctor_1809_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___f_1815_);
lean_ctor_set(v___x_1817_, 1, v___f_1816_);
lean_inc(v_toSeqRight_1812_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeqRight_1812_);
lean_inc(v_toSeqLeft_1811_);
v___f_1819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1819_, 0, v_toSeqLeft_1811_);
lean_inc(v_toSeq_1810_);
v___f_1820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1820_, 0, v_toSeq_1810_);
v___x_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1817_);
lean_ctor_set(v___x_1821_, 1, v___f_1813_);
lean_ctor_set(v___x_1821_, 2, v___f_1820_);
lean_ctor_set(v___x_1821_, 3, v___f_1819_);
lean_ctor_set(v___x_1821_, 4, v___f_1818_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___f_1814_);
lean_ctor_set(v___x_1805_, 0, v___x_1821_);
v___x_1823_ = v___x_1805_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___f_1814_);
v___x_1823_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v_toApplicative_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1861_; 
v___x_1824_ = l_StateRefT_x27_instMonad___redArg(v___x_1823_);
v_toApplicative_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1824_, 1);
lean_dec(v_unused_1862_);
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1861_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_toApplicative_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1861_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_toFunctor_1829_; lean_object* v_toSeq_1830_; lean_object* v_toSeqLeft_1831_; lean_object* v_toSeqRight_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1859_; 
v_toFunctor_1829_ = lean_ctor_get(v_toApplicative_1825_, 0);
v_toSeq_1830_ = lean_ctor_get(v_toApplicative_1825_, 2);
v_toSeqLeft_1831_ = lean_ctor_get(v_toApplicative_1825_, 3);
v_toSeqRight_1832_ = lean_ctor_get(v_toApplicative_1825_, 4);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_toApplicative_1825_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v_toApplicative_1825_, 1);
lean_dec(v_unused_1860_);
v___x_1834_ = v_toApplicative_1825_;
v_isShared_1835_ = v_isSharedCheck_1859_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_toSeqRight_1832_);
lean_inc(v_toSeqLeft_1831_);
lean_inc(v_toSeq_1830_);
lean_inc(v_toFunctor_1829_);
lean_dec(v_toApplicative_1825_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1859_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___f_1837_; lean_object* v_cls_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___f_1846_; lean_object* v___x_1848_; 
v___x_1836_ = lean_box(v___x_1801_);
lean_inc(v_toBind_1803_);
lean_inc_ref(v_body_1797_);
v___f_1837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1837_, 0, v_inst_1784_);
lean_closure_set(v___f_1837_, 1, v_bodyType_1798_);
lean_closure_set(v___f_1837_, 2, v_xs_1790_);
lean_closure_set(v___f_1837_, 3, v_toApplicative_1802_);
lean_closure_set(v___f_1837_, 4, v_level_1799_);
lean_closure_set(v___f_1837_, 5, v_e_1788_);
lean_closure_set(v___f_1837_, 6, v___x_1836_);
lean_closure_set(v___f_1837_, 7, v_body_1797_);
lean_closure_set(v___f_1837_, 8, v_toBind_1803_);
v_cls_1838_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1839_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1840_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1829_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toFunctor_1829_);
v___f_1842_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1842_, 0, v_toFunctor_1829_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___f_1841_);
lean_ctor_set(v___x_1843_, 1, v___f_1842_);
v___f_1844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1844_, 0, v_toSeqRight_1832_);
v___f_1845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1845_, 0, v_toSeqLeft_1831_);
v___f_1846_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1846_, 0, v_toSeq_1830_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 4, v___f_1844_);
lean_ctor_set(v___x_1834_, 3, v___f_1845_);
lean_ctor_set(v___x_1834_, 2, v___f_1846_);
lean_ctor_set(v___x_1834_, 1, v___f_1839_);
lean_ctor_set(v___x_1834_, 0, v___x_1843_);
v___x_1848_ = v___x_1834_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___f_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v___f_1846_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v___f_1845_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v___f_1844_);
v___x_1848_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___f_1840_);
lean_ctor_set(v___x_1827_, 0, v___x_1848_);
v___x_1850_ = v___x_1827_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___f_1840_);
v___x_1850_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___f_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___f_1851_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1852_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1853_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1854_, 0, v_cls_1838_);
lean_closure_set(v___f_1854_, 1, v___x_1852_);
lean_closure_set(v___f_1854_, 2, v___f_1851_);
lean_closure_set(v___f_1854_, 3, v_body_1797_);
lean_closure_set(v___f_1854_, 4, v___x_1850_);
lean_closure_set(v___f_1854_, 5, v___x_1853_);
v___x_1855_ = lean_apply_2(v_inst_1782_, lean_box(0), v___f_1854_);
v___x_1856_ = lean_apply_4(v_toBind_1803_, lean_box(0), lean_box(0), v___x_1855_, v___f_1837_);
return v___x_1856_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_e_1788_) == 8)
{
uint8_t v_nondep_1865_; 
v_nondep_1865_ = lean_ctor_get_uint8(v_e_1788_, sizeof(void*)*4 + 8);
if (v_nondep_1865_ == 1)
{
lean_object* v_declName_1866_; lean_object* v_type_1867_; lean_object* v_value_1868_; lean_object* v_body_1869_; lean_object* v_hinfo_1870_; lean_object* v_decl_1871_; lean_object* v_level_1872_; lean_object* v_x_1873_; lean_object* v_val_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_us_1877_; uint8_t v___y_1879_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_declName_1866_ = lean_ctor_get(v_e_1788_, 0);
lean_inc(v_declName_1866_);
v_type_1867_ = lean_ctor_get(v_e_1788_, 1);
lean_inc_ref(v_type_1867_);
v_value_1868_ = lean_ctor_get(v_e_1788_, 2);
lean_inc_ref(v_value_1868_);
v_body_1869_ = lean_ctor_get(v_e_1788_, 3);
lean_inc_ref(v_body_1869_);
lean_dec_ref(v_e_1788_);
v_hinfo_1870_ = lean_array_fget_borrowed(v_haveInfo_1796_, v_i_1789_);
v_decl_1871_ = lean_ctor_get(v_hinfo_1870_, 2);
v_level_1872_ = lean_ctor_get(v_hinfo_1870_, 3);
lean_inc_ref(v_decl_1871_);
v_x_1873_ = l_Lean_LocalDecl_toExpr(v_decl_1871_);
v_val_1874_ = l_Lean_LocalDecl_value(v_decl_1871_, v_nondep_1865_);
v___x_1875_ = lean_box(0);
lean_inc(v_level_1799_);
v___x_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_level_1799_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
lean_inc_ref(v___x_1876_);
lean_inc(v_level_1872_);
v_us_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1877_, 0, v_level_1872_);
lean_ctor_set(v_us_1877_, 1, v___x_1876_);
v___x_1906_ = lean_array_get_size(v_used_1787_);
v___x_1907_ = lean_nat_dec_lt(v_i_1789_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_inc_ref(v_decl_1871_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = lean_array_fget_borrowed(v_used_1787_, v_i_1789_);
v___x_1909_ = lean_unbox(v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v_toApplicative_1910_; lean_object* v_toBind_1911_; lean_object* v___x_1912_; lean_object* v_toApplicative_1913_; lean_object* v_toFunctor_1914_; lean_object* v_toSeq_1915_; lean_object* v_toSeqLeft_1916_; lean_object* v_toSeqRight_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_toApplicative_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_x_1873_);
v_toApplicative_1910_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc_ref(v_toApplicative_1910_);
v_toBind_1911_ = lean_ctor_get(v_inst_1781_, 1);
lean_inc(v_toBind_1911_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1913_ = lean_ctor_get(v___x_1912_, 0);
v_toFunctor_1914_ = lean_ctor_get(v_toApplicative_1913_, 0);
v_toSeq_1915_ = lean_ctor_get(v_toApplicative_1913_, 2);
v_toSeqLeft_1916_ = lean_ctor_get(v_toApplicative_1913_, 3);
v_toSeqRight_1917_ = lean_ctor_get(v_toApplicative_1913_, 4);
v___f_1918_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1919_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1914_, 2);
v___f_1920_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1920_, 0, v_toFunctor_1914_);
v___f_1921_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1921_, 0, v_toFunctor_1914_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___f_1920_);
lean_ctor_set(v___x_1922_, 1, v___f_1921_);
lean_inc(v_toSeqRight_1917_);
v___f_1923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1923_, 0, v_toSeqRight_1917_);
lean_inc(v_toSeqLeft_1916_);
v___f_1924_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1924_, 0, v_toSeqLeft_1916_);
lean_inc(v_toSeq_1915_);
v___f_1925_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1925_, 0, v_toSeq_1915_);
v___x_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1922_);
lean_ctor_set(v___x_1926_, 1, v___f_1918_);
lean_ctor_set(v___x_1926_, 2, v___f_1925_);
lean_ctor_set(v___x_1926_, 3, v___f_1924_);
lean_ctor_set(v___x_1926_, 4, v___f_1923_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___f_1919_);
v___x_1928_ = l_StateRefT_x27_instMonad___redArg(v___x_1927_);
v_toApplicative_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1928_, 1);
lean_dec(v_unused_1966_);
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1965_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_toApplicative_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1965_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_toFunctor_1933_; lean_object* v_toSeq_1934_; lean_object* v_toSeqLeft_1935_; lean_object* v_toSeqRight_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1963_; 
v_toFunctor_1933_ = lean_ctor_get(v_toApplicative_1929_, 0);
v_toSeq_1934_ = lean_ctor_get(v_toApplicative_1929_, 2);
v_toSeqLeft_1935_ = lean_ctor_get(v_toApplicative_1929_, 3);
v_toSeqRight_1936_ = lean_ctor_get(v_toApplicative_1929_, 4);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_toApplicative_1929_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_toApplicative_1929_, 1);
lean_dec(v_unused_1964_);
v___x_1938_ = v_toApplicative_1929_;
v_isShared_1939_ = v_isSharedCheck_1963_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_toSeqRight_1936_);
lean_inc(v_toSeqLeft_1935_);
lean_inc(v_toSeq_1934_);
lean_inc(v_toFunctor_1933_);
lean_dec(v_toApplicative_1929_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1963_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v_cls_1942_; lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___x_1952_; 
v___x_1940_ = lean_box(v_nondep_1865_);
lean_inc(v_toBind_1911_);
lean_inc(v_inst_1782_);
lean_inc(v_declName_1866_);
v___f_1941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1941_, 0, v___x_1875_);
lean_closure_set(v___f_1941_, 1, v_declName_1866_);
lean_closure_set(v___f_1941_, 2, v_type_1867_);
lean_closure_set(v___f_1941_, 3, v_value_1868_);
lean_closure_set(v___f_1941_, 4, v_us_1877_);
lean_closure_set(v___f_1941_, 5, v___x_1876_);
lean_closure_set(v___f_1941_, 6, v_toApplicative_1910_);
lean_closure_set(v___f_1941_, 7, v___x_1940_);
lean_closure_set(v___f_1941_, 8, v_i_1789_);
lean_closure_set(v___f_1941_, 9, v_xs_1790_);
lean_closure_set(v___f_1941_, 10, v_inst_1781_);
lean_closure_set(v___f_1941_, 11, v_inst_1782_);
lean_closure_set(v___f_1941_, 12, v_inst_1783_);
lean_closure_set(v___f_1941_, 13, v_inst_1784_);
lean_closure_set(v___f_1941_, 14, v_info_1785_);
lean_closure_set(v___f_1941_, 15, v_fixed_1786_);
lean_closure_set(v___f_1941_, 16, v_used_1787_);
lean_closure_set(v___f_1941_, 17, v_body_1869_);
lean_closure_set(v___f_1941_, 18, v_toBind_1911_);
v_cls_1942_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1943_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1944_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1933_);
v___f_1945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1945_, 0, v_toFunctor_1933_);
v___f_1946_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1946_, 0, v_toFunctor_1933_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___f_1945_);
lean_ctor_set(v___x_1947_, 1, v___f_1946_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toSeqRight_1936_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toSeqLeft_1935_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toSeq_1934_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 4, v___f_1948_);
lean_ctor_set(v___x_1938_, 3, v___f_1949_);
lean_ctor_set(v___x_1938_, 2, v___f_1950_);
lean_ctor_set(v___x_1938_, 1, v___f_1943_);
lean_ctor_set(v___x_1938_, 0, v___x_1947_);
v___x_1952_ = v___x_1938_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___f_1943_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v___f_1950_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v___f_1949_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v___f_1948_);
v___x_1952_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v___f_1944_);
lean_ctor_set(v___x_1931_, 0, v___x_1952_);
v___x_1954_ = v___x_1931_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___f_1944_);
v___x_1954_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___f_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___f_1955_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1957_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1958_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1958_, 0, v_cls_1942_);
lean_closure_set(v___f_1958_, 1, v___x_1956_);
lean_closure_set(v___f_1958_, 2, v___f_1955_);
lean_closure_set(v___f_1958_, 3, v_declName_1866_);
lean_closure_set(v___f_1958_, 4, v_val_1874_);
lean_closure_set(v___f_1958_, 5, v___x_1954_);
lean_closure_set(v___f_1958_, 6, v___x_1957_);
v___x_1959_ = lean_apply_2(v_inst_1782_, lean_box(0), v___f_1958_);
v___x_1960_ = lean_apply_4(v_toBind_1911_, lean_box(0), lean_box(0), v___x_1959_, v___f_1941_);
return v___x_1960_;
}
}
}
}
}
else
{
lean_inc_ref(v_decl_1871_);
goto v___jp_1889_;
}
}
v___jp_1878_:
{
lean_object* v_toApplicative_1880_; lean_object* v_toBind_1881_; lean_object* v_withNewLemmas_1882_; lean_object* v_dsimp_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_toApplicative_1880_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc_ref(v_toApplicative_1880_);
v_toBind_1881_ = lean_ctor_get(v_inst_1781_, 1);
lean_inc_n(v_toBind_1881_, 2);
v_withNewLemmas_1882_ = lean_ctor_get(v_inst_1784_, 0);
lean_inc(v_withNewLemmas_1882_);
v_dsimp_1883_ = lean_ctor_get(v_inst_1784_, 1);
lean_inc(v_dsimp_1883_);
v___x_1884_ = lean_box(v_nondep_1865_);
v___x_1885_ = lean_box(v___y_1879_);
lean_inc_ref(v_val_1874_);
v___f_1886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 24, 23);
lean_closure_set(v___f_1886_, 0, v_declName_1866_);
lean_closure_set(v___f_1886_, 1, v_type_1867_);
lean_closure_set(v___f_1886_, 2, v_value_1868_);
lean_closure_set(v___f_1886_, 3, v___x_1884_);
lean_closure_set(v___f_1886_, 4, v_toApplicative_1880_);
lean_closure_set(v___f_1886_, 5, v___x_1876_);
lean_closure_set(v___f_1886_, 6, v_us_1877_);
lean_closure_set(v___f_1886_, 7, v_decl_1871_);
lean_closure_set(v___f_1886_, 8, v_x_1873_);
lean_closure_set(v___f_1886_, 9, v_i_1789_);
lean_closure_set(v___f_1886_, 10, v_xs_1790_);
lean_closure_set(v___f_1886_, 11, v_inst_1781_);
lean_closure_set(v___f_1886_, 12, v_inst_1782_);
lean_closure_set(v___f_1886_, 13, v_inst_1783_);
lean_closure_set(v___f_1886_, 14, v_inst_1784_);
lean_closure_set(v___f_1886_, 15, v_info_1785_);
lean_closure_set(v___f_1886_, 16, v_fixed_1786_);
lean_closure_set(v___f_1886_, 17, v_used_1787_);
lean_closure_set(v___f_1886_, 18, v_body_1869_);
lean_closure_set(v___f_1886_, 19, v_toBind_1881_);
lean_closure_set(v___f_1886_, 20, v_withNewLemmas_1882_);
lean_closure_set(v___f_1886_, 21, v_val_1874_);
lean_closure_set(v___f_1886_, 22, v___x_1885_);
v___x_1887_ = lean_apply_1(v_dsimp_1883_, v_val_1874_);
v___x_1888_ = lean_apply_4(v_toBind_1881_, lean_box(0), lean_box(0), v___x_1887_, v___f_1886_);
return v___x_1888_;
}
v___jp_1889_:
{
uint8_t v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = 0;
v___x_1891_ = lean_array_get_size(v_fixed_1786_);
v___x_1892_ = lean_nat_dec_lt(v_i_1789_, v___x_1891_);
if (v___x_1892_ == 0)
{
v___y_1879_ = v___x_1890_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_array_fget_borrowed(v_fixed_1786_, v_i_1789_);
v___x_1894_ = lean_unbox(v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v_toApplicative_1895_; lean_object* v_toBind_1896_; lean_object* v_withNewLemmas_1897_; lean_object* v_simp_1898_; lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_inc(v___x_1893_);
lean_inc(v_level_1872_);
v_toApplicative_1895_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc_ref_n(v_toApplicative_1895_, 2);
v_toBind_1896_ = lean_ctor_get(v_inst_1781_, 1);
lean_inc_n(v_toBind_1896_, 3);
v_withNewLemmas_1897_ = lean_ctor_get(v_inst_1784_, 0);
lean_inc(v_withNewLemmas_1897_);
v_simp_1898_ = lean_ctor_get(v_inst_1784_, 2);
lean_inc(v_simp_1898_);
v___x_1899_ = lean_box(v_nondep_1865_);
lean_inc(v_inst_1782_);
lean_inc_ref(v_xs_1790_);
lean_inc_ref(v_value_1868_);
lean_inc_ref(v_type_1867_);
lean_inc(v_declName_1866_);
v___f_1900_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_1900_, 0, v_decl_1871_);
lean_closure_set(v___f_1900_, 1, v_declName_1866_);
lean_closure_set(v___f_1900_, 2, v_type_1867_);
lean_closure_set(v___f_1900_, 3, v_value_1868_);
lean_closure_set(v___f_1900_, 4, v___x_1899_);
lean_closure_set(v___f_1900_, 5, v_toApplicative_1895_);
lean_closure_set(v___f_1900_, 6, v___x_1876_);
lean_closure_set(v___f_1900_, 7, v_us_1877_);
lean_closure_set(v___f_1900_, 8, v_inst_1781_);
lean_closure_set(v___f_1900_, 9, v_x_1873_);
lean_closure_set(v___f_1900_, 10, v_i_1789_);
lean_closure_set(v___f_1900_, 11, v_xs_1790_);
lean_closure_set(v___f_1900_, 12, v_inst_1782_);
lean_closure_set(v___f_1900_, 13, v_inst_1783_);
lean_closure_set(v___f_1900_, 14, v_inst_1784_);
lean_closure_set(v___f_1900_, 15, v_info_1785_);
lean_closure_set(v___f_1900_, 16, v_fixed_1786_);
lean_closure_set(v___f_1900_, 17, v_used_1787_);
lean_closure_set(v___f_1900_, 18, v_body_1869_);
lean_closure_set(v___f_1900_, 19, v_toBind_1896_);
lean_closure_set(v___f_1900_, 20, v_withNewLemmas_1897_);
v___f_1901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1901_, 0, v___f_1900_);
v___x_1902_ = lean_box(v_nondep_1865_);
lean_inc_ref(v_val_1874_);
lean_inc_ref(v___f_1901_);
v___f_1903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_1903_, 0, v_toApplicative_1895_);
lean_closure_set(v___f_1903_, 1, v_level_1872_);
lean_closure_set(v___f_1903_, 2, v___x_1875_);
lean_closure_set(v___f_1903_, 3, v_type_1867_);
lean_closure_set(v___f_1903_, 4, v_value_1868_);
lean_closure_set(v___f_1903_, 5, v___x_1893_);
lean_closure_set(v___f_1903_, 6, v_toBind_1896_);
lean_closure_set(v___f_1903_, 7, v___f_1901_);
lean_closure_set(v___f_1903_, 8, v_xs_1790_);
lean_closure_set(v___f_1903_, 9, v___x_1902_);
lean_closure_set(v___f_1903_, 10, v___f_1901_);
lean_closure_set(v___f_1903_, 11, v_declName_1866_);
lean_closure_set(v___f_1903_, 12, v_val_1874_);
lean_closure_set(v___f_1903_, 13, v_inst_1782_);
v___x_1904_ = lean_apply_1(v_simp_1898_, v_val_1874_);
v___x_1905_ = lean_apply_4(v_toBind_1896_, lean_box(0), lean_box(0), v___x_1904_, v___f_1903_);
return v___x_1905_;
}
else
{
v___y_1879_ = v___x_1890_;
goto v___jp_1878_;
}
}
}
}
else
{
lean_dec_ref(v_e_1788_);
lean_dec_ref(v_xs_1790_);
lean_dec(v_i_1789_);
lean_dec_ref(v_used_1787_);
lean_dec_ref(v_fixed_1786_);
lean_dec_ref(v_info_1785_);
lean_dec_ref(v_inst_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec(v_inst_1782_);
goto v___jp_1791_;
}
}
else
{
lean_dec_ref(v_xs_1790_);
lean_dec(v_i_1789_);
lean_dec_ref(v_e_1788_);
lean_dec_ref(v_used_1787_);
lean_dec_ref(v_fixed_1786_);
lean_dec_ref(v_info_1785_);
lean_dec_ref(v_inst_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec(v_inst_1782_);
goto v___jp_1791_;
}
}
v___jp_1791_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1792_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1793_ = l_instInhabitedOfMonad___redArg(v_inst_1781_, v___x_1792_);
v___x_1794_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1795_ = l_panic___redArg(v___x_1793_, v___x_1794_);
lean_dec(v___x_1793_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1967_, lean_object* v_declName_1968_, lean_object* v_type_1969_, lean_object* v_value_1970_, lean_object* v_us_1971_, lean_object* v___x_1972_, lean_object* v_toApplicative_1973_, uint8_t v_nondep_1974_, lean_object* v_i_1975_, lean_object* v_xs_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_info_1981_, lean_object* v_fixed_1982_, lean_object* v_used_1983_, lean_object* v_body_1984_, lean_object* v_toBind_1985_, lean_object* v_____r_1986_){
_start:
{
lean_object* v___x_1987_; lean_object* v_x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1987_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1988_ = l_Lean_mkConst(v___x_1987_, v___x_1967_);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_box(v_nondep_1974_);
v___f_1991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1991_, 0, v___x_1989_);
lean_closure_set(v___f_1991_, 1, v_declName_1968_);
lean_closure_set(v___f_1991_, 2, v_type_1969_);
lean_closure_set(v___f_1991_, 3, v_value_1970_);
lean_closure_set(v___f_1991_, 4, v_us_1971_);
lean_closure_set(v___f_1991_, 5, v___x_1972_);
lean_closure_set(v___f_1991_, 6, v_toApplicative_1973_);
lean_closure_set(v___f_1991_, 7, v___x_1990_);
v___x_1992_ = lean_nat_add(v_i_1975_, v___x_1989_);
v___x_1993_ = lean_array_push(v_xs_1976_, v_x_1988_);
v___x_1994_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1977_, v_inst_1978_, v_inst_1979_, v_inst_1980_, v_info_1981_, v_fixed_1982_, v_used_1983_, v_body_1984_, v___x_1992_, v___x_1993_);
v___x_1995_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v___x_1994_, v___f_1991_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_info_2001_, lean_object* v_fixed_2002_, lean_object* v_used_2003_, lean_object* v_e_2004_, lean_object* v_i_2005_, lean_object* v_xs_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1997_, v_inst_1998_, v_inst_1999_, v_inst_2000_, v_info_2001_, v_fixed_2002_, v_used_2003_, v_e_2004_, v_i_2005_, v_xs_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_2008_){
_start:
{
switch(v_x_2008_)
{
case 0:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_unsigned_to_nat(0u);
return v___x_2009_;
}
case 1:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
return v___x_2010_;
}
default: 
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_unsigned_to_nat(2u);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2012_){
_start:
{
uint8_t v_x_boxed_2013_; lean_object* v_res_2014_; 
v_x_boxed_2013_ = lean_unbox(v_x_2012_);
v_res_2014_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t v_x_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object* v_x_2017_){
_start:
{
uint8_t v_x_4__boxed_2018_; lean_object* v_res_2019_; 
v_x_4__boxed_2018_ = lean_unbox(v_x_2017_);
v_res_2019_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2020_){
_start:
{
lean_inc(v_k_2020_);
return v_k_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2021_);
lean_dec(v_k_2021_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2023_, lean_object* v_ctorIdx_2024_, uint8_t v_t_2025_, lean_object* v_h_2026_, lean_object* v_k_2027_){
_start:
{
lean_inc(v_k_2027_);
return v_k_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2028_, lean_object* v_ctorIdx_2029_, lean_object* v_t_2030_, lean_object* v_h_2031_, lean_object* v_k_2032_){
_start:
{
uint8_t v_t_boxed_2033_; lean_object* v_res_2034_; 
v_t_boxed_2033_ = lean_unbox(v_t_2030_);
v_res_2034_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2028_, v_ctorIdx_2029_, v_t_boxed_2033_, v_h_2031_, v_k_2032_);
lean_dec(v_k_2032_);
lean_dec(v_ctorIdx_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2035_){
_start:
{
lean_inc(v_no_2035_);
return v_no_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2036_);
lean_dec(v_no_2036_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2038_, uint8_t v_t_2039_, lean_object* v_h_2040_, lean_object* v_no_2041_){
_start:
{
lean_inc(v_no_2041_);
return v_no_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2042_, lean_object* v_t_2043_, lean_object* v_h_2044_, lean_object* v_no_2045_){
_start:
{
uint8_t v_t_boxed_2046_; lean_object* v_res_2047_; 
v_t_boxed_2046_ = lean_unbox(v_t_2043_);
v_res_2047_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2042_, v_t_boxed_2046_, v_h_2044_, v_no_2045_);
lean_dec(v_no_2045_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2048_){
_start:
{
lean_inc(v_singlePass_2048_);
return v_singlePass_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2049_);
lean_dec(v_singlePass_2049_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2051_, uint8_t v_t_2052_, lean_object* v_h_2053_, lean_object* v_singlePass_2054_){
_start:
{
lean_inc(v_singlePass_2054_);
return v_singlePass_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2055_, lean_object* v_t_2056_, lean_object* v_h_2057_, lean_object* v_singlePass_2058_){
_start:
{
uint8_t v_t_boxed_2059_; lean_object* v_res_2060_; 
v_t_boxed_2059_ = lean_unbox(v_t_2056_);
v_res_2060_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2055_, v_t_boxed_2059_, v_h_2057_, v_singlePass_2058_);
lean_dec(v_singlePass_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2061_){
_start:
{
lean_inc(v_twoPasses_2061_);
return v_twoPasses_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2062_);
lean_dec(v_twoPasses_2062_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2064_, uint8_t v_t_2065_, lean_object* v_h_2066_, lean_object* v_twoPasses_2067_){
_start:
{
lean_inc(v_twoPasses_2067_);
return v_twoPasses_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2068_, lean_object* v_t_2069_, lean_object* v_h_2070_, lean_object* v_twoPasses_2071_){
_start:
{
uint8_t v_t_boxed_2072_; lean_object* v_res_2073_; 
v_t_boxed_2072_ = lean_unbox(v_t_2069_);
v_res_2073_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2068_, v_t_boxed_2072_, v_h_2070_, v_twoPasses_2071_);
lean_dec(v_twoPasses_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2074_, lean_object* v_b_2075_, lean_object* v_c_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; 
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v___x_2082_ = lean_apply_7(v_k_2074_, v_b_2075_, v_c_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, lean_box(0));
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2083_, lean_object* v_b_2084_, lean_object* v_c_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2083_, v_b_2084_, v_c_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2092_, lean_object* v_k_2093_, uint8_t v_cleanupAnnotations_2094_, uint8_t v_preserveNondepLet_2095_, uint8_t v_nondepLetOnly_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___f_2102_; uint8_t v___x_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2102_, 0, v_k_2093_);
v___x_2103_ = 0;
v___x_2104_ = 1;
v___x_2105_ = lean_box(0);
v___x_2106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2092_, v___x_2103_, v___x_2104_, v_preserveNondepLet_2095_, v_nondepLetOnly_2096_, v___x_2105_, v___f_2102_, v_cleanupAnnotations_2094_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_a_2115_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2106_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2106_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2123_, lean_object* v_k_2124_, lean_object* v_cleanupAnnotations_2125_, lean_object* v_preserveNondepLet_2126_, lean_object* v_nondepLetOnly_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2133_; uint8_t v_preserveNondepLet_boxed_2134_; uint8_t v_nondepLetOnly_boxed_2135_; lean_object* v_res_2136_; 
v_cleanupAnnotations_boxed_2133_ = lean_unbox(v_cleanupAnnotations_2125_);
v_preserveNondepLet_boxed_2134_ = lean_unbox(v_preserveNondepLet_2126_);
v_nondepLetOnly_boxed_2135_ = lean_unbox(v_nondepLetOnly_2127_);
v_res_2136_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2123_, v_k_2124_, v_cleanupAnnotations_boxed_2133_, v_preserveNondepLet_boxed_2134_, v_nondepLetOnly_boxed_2135_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2137_, lean_object* v_e_2138_, lean_object* v_k_2139_, uint8_t v_cleanupAnnotations_2140_, uint8_t v_preserveNondepLet_2141_, uint8_t v_nondepLetOnly_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2138_, v_k_2139_, v_cleanupAnnotations_2140_, v_preserveNondepLet_2141_, v_nondepLetOnly_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_e_2150_, lean_object* v_k_2151_, lean_object* v_cleanupAnnotations_2152_, lean_object* v_preserveNondepLet_2153_, lean_object* v_nondepLetOnly_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2160_; uint8_t v_preserveNondepLet_boxed_2161_; uint8_t v_nondepLetOnly_boxed_2162_; lean_object* v_res_2163_; 
v_cleanupAnnotations_boxed_2160_ = lean_unbox(v_cleanupAnnotations_2152_);
v_preserveNondepLet_boxed_2161_ = lean_unbox(v_preserveNondepLet_2153_);
v_nondepLetOnly_boxed_2162_ = lean_unbox(v_nondepLetOnly_2154_);
v_res_2163_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2149_, v_e_2150_, v_k_2151_, v_cleanupAnnotations_boxed_2160_, v_preserveNondepLet_boxed_2161_, v_nondepLetOnly_boxed_2162_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2164_, lean_object* v_a_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_snd_2170_; lean_object* v_fst_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2226_; 
v_snd_2170_ = lean_ctor_get(v_a_2165_, 1);
v_fst_2171_ = lean_ctor_get(v_a_2165_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2173_ = v_a_2165_;
v_isShared_2174_ = v_isSharedCheck_2226_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2170_);
lean_inc(v_fst_2171_);
lean_dec(v_a_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2226_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2225_; 
v_fst_2175_ = lean_ctor_get(v_snd_2170_, 0);
v_snd_2176_ = lean_ctor_get(v_snd_2170_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_snd_2170_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2178_ = v_snd_2170_;
v_isShared_2179_ = v_isSharedCheck_2225_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_inc(v_fst_2175_);
lean_dec(v_snd_2170_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2225_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_nat_dec_lt(v___x_2180_, v_snd_2176_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2183_; 
if (v_isShared_2179_ == 0)
{
v___x_2183_ = v___x_2178_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_fst_2175_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_snd_2176_);
v___x_2183_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2185_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2183_);
v___x_2185_ = v___x_2173_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_fst_2171_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
}
else
{
lean_object* v_fvarSet_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_fvarSet_2189_ = lean_ctor_get(v_fst_2171_, 1);
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_nat_sub(v_snd_2176_, v___x_2190_);
lean_dec(v_snd_2176_);
v___x_2192_ = l_Lean_instInhabitedExpr;
v___x_2193_ = lean_array_get_borrowed(v___x_2192_, v_xs_2164_, v___x_2191_);
v___x_2194_ = l_Lean_Expr_fvarId_x21(v___x_2193_);
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2194_, v_fvarSet_2189_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2197_; 
lean_dec(v___x_2194_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2191_);
v___x_2197_ = v___x_2178_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_fst_2175_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2191_);
v___x_2197_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2197_);
v___x_2199_ = v___x_2173_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_fst_2171_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
v_a_2165_ = v___x_2199_;
goto _start;
}
}
}
else
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_FVarId_getDecl___redArg(v___x_2194_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_LocalDecl_type(v_a_2204_);
v___x_2206_ = l_Lean_collectFVars(v_fst_2171_, v___x_2205_);
v___x_2207_ = l_Lean_LocalDecl_value(v_a_2204_, v___x_2195_);
lean_dec(v_a_2204_);
v___x_2208_ = l_Lean_collectFVars(v___x_2206_, v___x_2207_);
lean_inc(v___x_2193_);
v___x_2209_ = lean_array_push(v_fst_2175_, v___x_2193_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2191_);
lean_ctor_set(v___x_2178_, 0, v___x_2209_);
v___x_2211_ = v___x_2178_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2191_);
v___x_2211_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2211_);
lean_ctor_set(v___x_2173_, 0, v___x_2208_);
v___x_2213_ = v___x_2173_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
v_a_2165_ = v___x_2213_;
goto _start;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v___x_2191_);
lean_del_object(v___x_2178_);
lean_dec(v_fst_2175_);
lean_del_object(v___x_2173_);
lean_dec(v_fst_2171_);
v_a_2217_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2203_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2203_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2227_, lean_object* v_a_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2227_, v_a_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v_xs_2227_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2234_, lean_object* v_e_2235_, lean_object* v_xs_2236_, lean_object* v_body_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_s_2246_; lean_object* v_i_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2243_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2234_);
lean_ctor_set(v___x_2245_, 2, v___x_2244_);
lean_inc_ref(v_body_2237_);
v_s_2246_ = l_Lean_collectFVars(v___x_2245_, v_body_2237_);
v_i_2247_ = lean_array_get_size(v_xs_2236_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2244_);
lean_ctor_set(v___x_2248_, 1, v_i_2247_);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v_s_2246_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2236_, v___x_2249_, v___y_2238_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2266_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2266_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2266_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_snd_2255_; lean_object* v_fst_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_snd_2255_ = lean_ctor_get(v_a_2251_, 1);
lean_inc(v_snd_2255_);
lean_dec(v_a_2251_);
v_fst_2256_ = lean_ctor_get(v_snd_2255_, 0);
lean_inc(v_fst_2256_);
lean_dec(v_snd_2255_);
v___x_2257_ = lean_array_get_size(v_fst_2256_);
v___x_2258_ = lean_nat_dec_eq(v___x_2257_, v_i_2247_);
if (v___x_2258_ == 0)
{
uint8_t v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; 
lean_del_object(v___x_2253_);
lean_dec_ref(v_e_2235_);
v___x_2259_ = 1;
v___x_2260_ = l_Array_reverse___redArg(v_fst_2256_);
v___x_2261_ = 1;
v___x_2262_ = l_Lean_Meta_mkLetFVars(v___x_2260_, v_body_2237_, v___x_2259_, v___x_2258_, v___x_2261_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec_ref(v___x_2260_);
return v___x_2262_;
}
else
{
lean_object* v___x_2264_; 
lean_dec(v_fst_2256_);
lean_dec_ref(v_body_2237_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v_e_2235_);
v___x_2264_ = v___x_2253_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_e_2235_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_body_2237_);
lean_dec_ref(v_e_2235_);
v_a_2267_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2250_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2250_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2275_, lean_object* v_e_2276_, lean_object* v_xs_2277_, lean_object* v_body_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2275_, v_e_2276_, v_xs_2277_, v_body_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v_xs_2277_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v___f_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2291_ = lean_box(1);
lean_inc_ref(v_e_2285_);
v___f_2292_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2292_, 0, v___x_2291_);
lean_closure_set(v___f_2292_, 1, v_e_2285_);
v___x_2293_ = 0;
v___x_2294_ = 1;
v___x_2295_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2285_, v___f_2292_, v___x_2293_, v___x_2294_, v___x_2293_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Meta_zetaUnused(v_e_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2303_, lean_object* v_inst_2304_, lean_object* v_a_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2303_, v_a_2305_, v___y_2306_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2312_, lean_object* v_inst_2313_, lean_object* v_a_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2312_, v_inst_2313_, v_a_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_xs_2312_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2325_, lean_object* v_source_2326_, lean_object* v_result_2327_, uint8_t v_keepUnused_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
uint8_t v_modified_2334_; 
v_modified_2334_ = lean_ctor_get_uint8(v_result_2327_, sizeof(void*)*5);
if (v_modified_2334_ == 0)
{
if (v_keepUnused_2328_ == 0)
{
lean_object* v_exprType_2335_; lean_object* v___x_2336_; 
v_exprType_2335_ = lean_ctor_get(v_result_2327_, 1);
lean_inc_ref(v_exprType_2335_);
lean_dec_ref(v_result_2327_);
lean_inc_ref(v_source_2326_);
v___x_2336_ = l_Lean_Meta_zetaUnused(v_source_2326_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2355_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2355_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2355_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_expr_eqv(v_a_2337_, v_source_2326_);
lean_dec_ref(v_source_2326_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_u_2325_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_mkConst(v___x_2342_, v___x_2344_);
lean_inc(v_a_2337_);
v___x_2346_ = l_Lean_mkAppB(v___x_2345_, v_exprType_2335_, v_a_2337_);
v___x_2347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_a_2337_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2347_);
v___x_2349_ = v___x_2339_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
lean_dec(v_a_2337_);
lean_dec_ref(v_exprType_2335_);
lean_dec(v_u_2325_);
v___x_2351_ = lean_box(0);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2351_);
v___x_2353_ = v___x_2339_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v_exprType_2335_);
lean_dec_ref(v_source_2326_);
lean_dec(v_u_2325_);
v_a_2356_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2336_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2336_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec_ref(v_result_2327_);
lean_dec_ref(v_source_2326_);
lean_dec(v_u_2325_);
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
else
{
lean_object* v_expr_2366_; lean_object* v_exprType_2367_; lean_object* v_exprInit_2368_; lean_object* v_exprResult_2369_; lean_object* v_proof_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_proof_2378_; 
v_expr_2366_ = lean_ctor_get(v_result_2327_, 0);
lean_inc_ref(v_expr_2366_);
v_exprType_2367_ = lean_ctor_get(v_result_2327_, 1);
lean_inc_ref_n(v_exprType_2367_, 3);
v_exprInit_2368_ = lean_ctor_get(v_result_2327_, 2);
lean_inc_ref(v_exprInit_2368_);
v_exprResult_2369_ = lean_ctor_get(v_result_2327_, 3);
lean_inc_ref_n(v_exprResult_2369_, 2);
v_proof_2370_ = lean_ctor_get(v_result_2327_, 4);
lean_inc_ref(v_proof_2370_);
lean_dec_ref(v_result_2327_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_u_2325_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
lean_inc_ref(v___x_2373_);
v___x_2374_ = l_Lean_mkConst(v___x_2371_, v___x_2373_);
lean_inc_ref(v___x_2374_);
v___x_2375_ = l_Lean_mkApp3(v___x_2374_, v_exprType_2367_, v_exprInit_2368_, v_expr_2366_);
v___x_2376_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2370_, v___x_2375_);
lean_inc_ref(v_source_2326_);
v___x_2377_ = l_Lean_mkApp3(v___x_2374_, v_exprType_2367_, v_source_2326_, v_exprResult_2369_);
v_proof_2378_ = l_Lean_Meta_mkExpectedPropHint(v___x_2376_, v___x_2377_);
if (v_keepUnused_2328_ == 0)
{
lean_object* v___x_2379_; 
lean_inc_ref(v_exprResult_2369_);
v___x_2379_ = l_Lean_Meta_zetaUnused(v_exprResult_2369_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2399_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2399_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2399_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_expr_eqv(v_a_2380_, v_exprResult_2369_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2373_);
v___x_2386_ = l_Lean_mkConst(v___x_2385_, v___x_2373_);
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2388_ = l_Lean_mkConst(v___x_2387_, v___x_2373_);
lean_inc_n(v_a_2380_, 2);
lean_inc_ref(v_exprType_2367_);
v___x_2389_ = l_Lean_mkAppB(v___x_2388_, v_exprType_2367_, v_a_2380_);
v___x_2390_ = l_Lean_mkApp6(v___x_2386_, v_exprType_2367_, v_source_2326_, v_exprResult_2369_, v_a_2380_, v_proof_2378_, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_a_2380_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2391_);
v___x_2393_ = v___x_2382_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec(v_a_2380_);
lean_dec_ref(v___x_2373_);
lean_dec_ref(v_exprType_2367_);
lean_dec_ref(v_source_2326_);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_exprResult_2369_);
lean_ctor_set(v___x_2395_, 1, v_proof_2378_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2395_);
v___x_2397_ = v___x_2382_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v_proof_2378_);
lean_dec_ref(v___x_2373_);
lean_dec_ref(v_exprResult_2369_);
lean_dec_ref(v_exprType_2367_);
lean_dec_ref(v_source_2326_);
v_a_2400_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2379_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2379_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec_ref(v___x_2373_);
lean_dec_ref(v_exprType_2367_);
lean_dec_ref(v_source_2326_);
v___x_2408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_exprResult_2369_);
lean_ctor_set(v___x_2408_, 1, v_proof_2378_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2410_, lean_object* v_source_2411_, lean_object* v_result_2412_, lean_object* v_keepUnused_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
uint8_t v_keepUnused_boxed_2419_; lean_object* v_res_2420_; 
v_keepUnused_boxed_2419_ = lean_unbox(v_keepUnused_2413_);
v_res_2420_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2410_, v_source_2411_, v_result_2412_, v_keepUnused_boxed_2419_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2421_, lean_object* v_e_2422_, lean_object* v_inst_2423_, uint8_t v_zetaUnusedMode_2424_, uint8_t v___x_2425_, uint8_t v___x_2426_, lean_object* v_r_2427_){
_start:
{
uint8_t v___y_2429_; 
switch(v_zetaUnusedMode_2424_)
{
case 0:
{
v___y_2429_ = v___x_2425_;
goto v___jp_2428_;
}
case 1:
{
v___y_2429_ = v___x_2425_;
goto v___jp_2428_;
}
default: 
{
v___y_2429_ = v___x_2426_;
goto v___jp_2428_;
}
}
v___jp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_box(v___y_2429_);
v___x_2431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2431_, 0, v_level_2421_);
lean_closure_set(v___x_2431_, 1, v_e_2422_);
lean_closure_set(v___x_2431_, 2, v_r_2427_);
lean_closure_set(v___x_2431_, 3, v___x_2430_);
v___x_2432_ = lean_apply_2(v_inst_2423_, lean_box(0), v___x_2431_);
return v___x_2432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2433_, lean_object* v_e_2434_, lean_object* v_inst_2435_, lean_object* v_zetaUnusedMode_2436_, lean_object* v___x_2437_, lean_object* v___x_2438_, lean_object* v_r_2439_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2440_; uint8_t v___x_363__boxed_2441_; uint8_t v___x_364__boxed_2442_; lean_object* v_res_2443_; 
v_zetaUnusedMode_boxed_2440_ = lean_unbox(v_zetaUnusedMode_2436_);
v___x_363__boxed_2441_ = lean_unbox(v___x_2437_);
v___x_364__boxed_2442_ = lean_unbox(v___x_2438_);
v_res_2443_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2433_, v_e_2434_, v_inst_2435_, v_zetaUnusedMode_boxed_2440_, v___x_363__boxed_2441_, v___x_364__boxed_2442_, v_r_2439_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_info_2449_, lean_object* v_e_2450_, lean_object* v___x_2451_, lean_object* v_toBind_2452_, lean_object* v___f_2453_, lean_object* v_____x_2454_){
_start:
{
lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_fst_2455_ = lean_ctor_get(v_____x_2454_, 0);
lean_inc(v_fst_2455_);
v_snd_2456_ = lean_ctor_get(v_____x_2454_, 1);
lean_inc(v_snd_2456_);
lean_dec_ref(v_____x_2454_);
v___x_2457_ = lean_mk_empty_array_with_capacity(v___x_2444_);
v___x_2458_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2445_, v_inst_2446_, v_inst_2447_, v_inst_2448_, v_info_2449_, v_fst_2455_, v_snd_2456_, v_e_2450_, v___x_2451_, v___x_2457_);
v___x_2459_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2458_, v___f_2453_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_info_2465_, lean_object* v_e_2466_, lean_object* v___x_2467_, lean_object* v_toBind_2468_, lean_object* v___f_2469_, lean_object* v_____x_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2460_, v_inst_2461_, v_inst_2462_, v_inst_2463_, v_inst_2464_, v_info_2465_, v_e_2466_, v___x_2467_, v_toBind_2468_, v___f_2469_, v_____x_2470_);
lean_dec(v___x_2460_);
return v_res_2471_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2474_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2475_ = lean_unsigned_to_nat(2u);
v___x_2476_ = lean_unsigned_to_nat(456u);
v___x_2477_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2479_ = l_mkPanicMessageWithDecl(v___x_2478_, v___x_2477_, v___x_2476_, v___x_2475_, v___x_2474_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2480_, lean_object* v_inst_2481_, uint8_t v_zetaUnusedMode_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_toBind_2486_, lean_object* v_info_2487_){
_start:
{
lean_object* v_haveInfo_2488_; lean_object* v_level_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_haveInfo_2488_ = lean_ctor_get(v_info_2487_, 0);
v_level_2489_ = lean_ctor_get(v_info_2487_, 5);
v___x_2490_ = lean_array_get_size(v_haveInfo_2488_);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_nat_dec_eq(v___x_2490_, v___x_2491_);
if (v___x_2492_ == 0)
{
uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___f_2497_; lean_object* v___f_2498_; uint8_t v___y_2500_; 
v___x_2493_ = 1;
v___x_2494_ = lean_box(v_zetaUnusedMode_2482_);
v___x_2495_ = lean_box(v___x_2493_);
v___x_2496_ = lean_box(v___x_2492_);
lean_inc_n(v_inst_2481_, 2);
lean_inc_ref(v_e_2480_);
lean_inc(v_level_2489_);
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2497_, 0, v_level_2489_);
lean_closure_set(v___f_2497_, 1, v_e_2480_);
lean_closure_set(v___f_2497_, 2, v_inst_2481_);
lean_closure_set(v___f_2497_, 3, v___x_2494_);
lean_closure_set(v___f_2497_, 4, v___x_2495_);
lean_closure_set(v___f_2497_, 5, v___x_2496_);
lean_inc(v_toBind_2486_);
lean_inc_ref(v_info_2487_);
v___f_2498_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2498_, 0, v___x_2490_);
lean_closure_set(v___f_2498_, 1, v_inst_2483_);
lean_closure_set(v___f_2498_, 2, v_inst_2481_);
lean_closure_set(v___f_2498_, 3, v_inst_2484_);
lean_closure_set(v___f_2498_, 4, v_inst_2485_);
lean_closure_set(v___f_2498_, 5, v_info_2487_);
lean_closure_set(v___f_2498_, 6, v_e_2480_);
lean_closure_set(v___f_2498_, 7, v___x_2491_);
lean_closure_set(v___f_2498_, 8, v_toBind_2486_);
lean_closure_set(v___f_2498_, 9, v___f_2497_);
switch(v_zetaUnusedMode_2482_)
{
case 0:
{
v___y_2500_ = v___x_2493_;
goto v___jp_2499_;
}
case 2:
{
v___y_2500_ = v___x_2493_;
goto v___jp_2499_;
}
default: 
{
v___y_2500_ = v___x_2492_;
goto v___jp_2499_;
}
}
v___jp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2501_ = lean_box(v___y_2500_);
v___x_2502_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2502_, 0, v_info_2487_);
lean_closure_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_apply_2(v_inst_2481_, lean_box(0), v___x_2502_);
v___x_2504_ = lean_apply_4(v_toBind_2486_, lean_box(0), lean_box(0), v___x_2503_, v___f_2498_);
return v___x_2504_;
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec_ref(v_info_2487_);
lean_dec(v_toBind_2486_);
lean_dec_ref(v_inst_2485_);
lean_dec_ref(v_inst_2484_);
lean_dec(v_inst_2481_);
lean_dec_ref(v_e_2480_);
v___x_2505_ = lean_box(0);
v___x_2506_ = l_instInhabitedOfMonad___redArg(v_inst_2483_, v___x_2505_);
v___x_2507_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2508_ = l_panic___redArg(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2509_, lean_object* v_inst_2510_, lean_object* v_zetaUnusedMode_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_toBind_2515_, lean_object* v_info_2516_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2517_; lean_object* v_res_2518_; 
v_zetaUnusedMode_boxed_2517_ = lean_unbox(v_zetaUnusedMode_2511_);
v_res_2518_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2509_, v_inst_2510_, v_zetaUnusedMode_boxed_2517_, v_inst_2512_, v_inst_2513_, v_inst_2514_, v_toBind_2515_, v_info_2516_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_e_2523_, uint8_t v_zetaUnusedMode_2524_){
_start:
{
lean_object* v_toBind_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_toBind_2525_ = lean_ctor_get(v_inst_2519_, 1);
lean_inc_n(v_toBind_2525_, 2);
v___x_2526_ = lean_box(v_zetaUnusedMode_2524_);
lean_inc(v_inst_2520_);
lean_inc_ref(v_e_2523_);
v___f_2527_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2527_, 0, v_e_2523_);
lean_closure_set(v___f_2527_, 1, v_inst_2520_);
lean_closure_set(v___f_2527_, 2, v___x_2526_);
lean_closure_set(v___f_2527_, 3, v_inst_2519_);
lean_closure_set(v___f_2527_, 4, v_inst_2521_);
lean_closure_set(v___f_2527_, 5, v_inst_2522_);
lean_closure_set(v___f_2527_, 6, v_toBind_2525_);
v___x_2528_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2528_, 0, v_e_2523_);
v___x_2529_ = lean_apply_2(v_inst_2520_, lean_box(0), v___x_2528_);
v___x_2530_ = lean_apply_4(v_toBind_2525_, lean_box(0), lean_box(0), v___x_2529_, v___f_2527_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_e_2535_, lean_object* v_zetaUnusedMode_2536_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2537_; lean_object* v_res_2538_; 
v_zetaUnusedMode_boxed_2537_ = lean_unbox(v_zetaUnusedMode_2536_);
v_res_2538_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2531_, v_inst_2532_, v_inst_2533_, v_inst_2534_, v_e_2535_, v_zetaUnusedMode_boxed_2537_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_e_2544_, uint8_t v_zetaUnusedMode_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2540_, v_inst_2541_, v_inst_2542_, v_inst_2543_, v_e_2544_, v_zetaUnusedMode_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_e_2552_, lean_object* v_zetaUnusedMode_2553_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2554_; lean_object* v_res_2555_; 
v_zetaUnusedMode_boxed_2554_ = lean_unbox(v_zetaUnusedMode_2553_);
v_res_2555_ = l_Lean_Meta_simpHaveTelescope(v_m_2547_, v_inst_2548_, v_inst_2549_, v_inst_2550_, v_inst_2551_, v_e_2552_, v_zetaUnusedMode_boxed_2554_);
return v_res_2555_;
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
