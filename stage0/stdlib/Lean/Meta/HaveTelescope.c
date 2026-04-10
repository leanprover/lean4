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
lean_object* v___x_344_; lean_object* v_ngen_345_; lean_object* v_namePrefix_346_; lean_object* v_idx_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_376_; 
v___x_344_ = lean_st_ref_get(v___y_342_);
v_ngen_345_ = lean_ctor_get(v___x_344_, 2);
lean_inc_ref(v_ngen_345_);
lean_dec(v___x_344_);
v_namePrefix_346_ = lean_ctor_get(v_ngen_345_, 0);
v_idx_347_ = lean_ctor_get(v_ngen_345_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_ngen_345_);
if (v_isSharedCheck_376_ == 0)
{
v___x_349_ = v_ngen_345_;
v_isShared_350_ = v_isSharedCheck_376_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_idx_347_);
lean_inc(v_namePrefix_346_);
lean_dec(v_ngen_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_376_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v_nextMacroScope_353_; lean_object* v_auxDeclNGen_354_; lean_object* v_traceState_355_; lean_object* v_cache_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_374_; 
v___x_351_ = lean_st_ref_take(v___y_342_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
v_nextMacroScope_353_ = lean_ctor_get(v___x_351_, 1);
v_auxDeclNGen_354_ = lean_ctor_get(v___x_351_, 3);
v_traceState_355_ = lean_ctor_get(v___x_351_, 4);
v_cache_356_ = lean_ctor_get(v___x_351_, 5);
v_messages_357_ = lean_ctor_get(v___x_351_, 6);
v_infoState_358_ = lean_ctor_get(v___x_351_, 7);
v_snapshotTasks_359_ = lean_ctor_get(v___x_351_, 8);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_351_, 2);
lean_dec(v_unused_375_);
v___x_361_ = v___x_351_;
v_isShared_362_ = v_isSharedCheck_374_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_cache_356_);
lean_inc(v_traceState_355_);
lean_inc(v_auxDeclNGen_354_);
lean_inc(v_nextMacroScope_353_);
lean_inc(v_env_352_);
lean_dec(v___x_351_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_374_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_r_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc(v_idx_347_);
lean_inc(v_namePrefix_346_);
v_r_363_ = l_Lean_Name_num___override(v_namePrefix_346_, v_idx_347_);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_add(v_idx_347_, v___x_364_);
lean_dec(v_idx_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_365_);
v___x_367_ = v___x_349_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_namePrefix_346_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_373_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 2, v___x_367_);
v___x_369_ = v___x_361_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_env_352_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_nextMacroScope_353_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_auxDeclNGen_354_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_traceState_355_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_cache_356_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_snapshotTasks_359_);
v___x_369_ = v_reuseFailAlloc_372_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_st_ref_set(v___y_342_, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_r_363_);
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_377_);
lean_dec(v___y_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v___x_385_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_383_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_400_, lean_object* v_numHaves_401_, lean_object* v_info_402_, lean_object* v_lctx_403_, lean_object* v_fvars_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; 
v___x_410_ = lean_box(1);
if (lean_obj_tag(v_e_400_) == 8)
{
uint8_t v_nondep_420_; 
v_nondep_420_ = lean_ctor_get_uint8(v_e_400_, sizeof(void*)*4 + 8);
if (v_nondep_420_ == 1)
{
lean_object* v_declName_421_; lean_object* v_type_422_; lean_object* v_value_423_; lean_object* v_body_424_; lean_object* v_t_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_declName_421_ = lean_ctor_get(v_e_400_, 0);
lean_inc(v_declName_421_);
v_type_422_ = lean_ctor_get(v_e_400_, 1);
lean_inc_ref(v_type_422_);
v_value_423_ = lean_ctor_get(v_e_400_, 2);
lean_inc_ref(v_value_423_);
v_body_424_ = lean_ctor_get(v_e_400_, 3);
lean_inc_ref(v_body_424_);
lean_dec_ref(v_e_400_);
v_t_425_ = lean_expr_instantiate_rev(v_type_422_, v_fvars_404_);
lean_inc_ref(v_t_425_);
v___x_426_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_426_, 0, v_t_425_);
lean_inc_ref(v_lctx_403_);
v___x_427_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_403_, v___x_426_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref(v___x_427_);
v___x_429_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_haveInfo_431_; lean_object* v_bodyDeps_432_; lean_object* v_bodyTypeDeps_433_; lean_object* v_body_434_; lean_object* v_bodyType_435_; lean_object* v_level_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
v_haveInfo_431_ = lean_ctor_get(v_info_402_, 0);
v_bodyDeps_432_ = lean_ctor_get(v_info_402_, 1);
v_bodyTypeDeps_433_ = lean_ctor_get(v_info_402_, 2);
v_body_434_ = lean_ctor_get(v_info_402_, 3);
v_bodyType_435_ = lean_ctor_get(v_info_402_, 4);
v_level_436_ = lean_ctor_get(v_info_402_, 5);
v_isSharedCheck_457_ = !lean_is_exclusive(v_info_402_);
if (v_isSharedCheck_457_ == 0)
{
v___x_438_ = v_info_402_;
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_level_436_);
lean_inc(v_bodyType_435_);
lean_inc(v_body_434_);
lean_inc(v_bodyTypeDeps_433_);
lean_inc(v_bodyDeps_432_);
lean_inc(v_haveInfo_431_);
lean_dec(v_info_402_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_typeBackDeps_440_; lean_object* v_valueBackDeps_441_; lean_object* v_v_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v_typeBackDeps_440_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_401_, v_type_422_);
lean_inc_ref(v_value_423_);
v_valueBackDeps_441_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_401_, v_value_423_);
v_v_442_ = lean_expr_instantiate_rev(v_value_423_, v_fvars_404_);
lean_dec_ref(v_value_423_);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = 0;
lean_inc(v_a_430_);
v___x_445_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v_a_430_);
lean_ctor_set(v___x_445_, 2, v_declName_421_);
lean_ctor_set(v___x_445_, 3, v_t_425_);
lean_ctor_set(v___x_445_, 4, v_v_442_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*5, v_nondep_420_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*5 + 1, v___x_444_);
lean_inc_ref(v___x_445_);
v___x_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_446_, 0, v_typeBackDeps_440_);
lean_ctor_set(v___x_446_, 1, v_valueBackDeps_441_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
lean_ctor_set(v___x_446_, 3, v_a_428_);
v___x_447_ = lean_array_push(v_haveInfo_431_, v___x_446_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_447_);
v___x_449_ = v___x_438_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_bodyDeps_432_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_bodyTypeDeps_433_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_body_434_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_bodyType_435_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_level_436_);
v___x_449_ = v_reuseFailAlloc_456_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = l_Lean_LocalContext_addDecl(v_lctx_403_, v___x_445_);
v___x_451_ = l_Lean_mkFVar(v_a_430_);
v___x_452_ = lean_array_push(v_fvars_404_, v___x_451_);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_numHaves_401_, v___x_453_);
lean_dec(v_numHaves_401_);
v_e_400_ = v_body_424_;
v_numHaves_401_ = v___x_454_;
v_info_402_ = v___x_449_;
v_lctx_403_ = v___x_450_;
v_fvars_404_ = v___x_452_;
goto _start;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_a_428_);
lean_dec_ref(v_t_425_);
lean_dec_ref(v_body_424_);
lean_dec_ref(v_value_423_);
lean_dec_ref(v_type_422_);
lean_dec(v_declName_421_);
lean_dec_ref(v_fvars_404_);
lean_dec_ref(v_lctx_403_);
lean_dec_ref(v_info_402_);
lean_dec(v_numHaves_401_);
v_a_458_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_429_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_429_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v_t_425_);
lean_dec_ref(v_body_424_);
lean_dec_ref(v_value_423_);
lean_dec_ref(v_type_422_);
lean_dec(v_declName_421_);
lean_dec_ref(v_fvars_404_);
lean_dec_ref(v_lctx_403_);
lean_dec_ref(v_info_402_);
lean_dec(v_numHaves_401_);
v_a_466_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_427_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_427_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
v___y_412_ = v_a_405_;
v___y_413_ = v_a_406_;
v___y_414_ = v_a_407_;
v___y_415_ = v_a_408_;
goto v___jp_411_;
}
}
else
{
v___y_412_ = v_a_405_;
v___y_413_ = v_a_406_;
v___y_414_ = v_a_407_;
v___y_415_ = v_a_408_;
goto v___jp_411_;
}
v___jp_411_:
{
lean_object* v_bodyDeps_416_; lean_object* v_body_417_; lean_object* v___f_418_; lean_object* v___x_419_; 
lean_inc_ref(v_e_400_);
v_bodyDeps_416_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_401_, v_e_400_);
lean_dec(v_numHaves_401_);
v_body_417_ = lean_expr_instantiate_rev(v_e_400_, v_fvars_404_);
lean_dec_ref(v_e_400_);
v___f_418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_418_, 0, v_body_417_);
lean_closure_set(v___f_418_, 1, v___x_410_);
lean_closure_set(v___f_418_, 2, v_fvars_404_);
lean_closure_set(v___f_418_, 3, v_info_402_);
lean_closure_set(v___f_418_, 4, v_bodyDeps_416_);
v___x_419_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_403_, v___f_418_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_474_, lean_object* v_numHaves_475_, lean_object* v_info_476_, lean_object* v_lctx_477_, lean_object* v_fvars_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_474_, v_numHaves_475_, v_info_476_, v_lctx_477_, v_fvars_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_a_487_, lean_object* v_b_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_486_, v_a_487_, v_b_488_);
return v___x_489_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_490_, lean_object* v_k_491_, lean_object* v_t_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_491_, v_t_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_494_, lean_object* v_k_495_, lean_object* v_t_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_494_, v_k_495_, v_t_496_);
lean_dec(v_t_496_);
lean_dec(v_k_495_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_499_, lean_object* v___x_500_, lean_object* v_n_501_, lean_object* v_j_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_499_, v___x_500_, v_n_501_, v_j_502_, v_a_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_506_, lean_object* v___x_507_, lean_object* v_n_508_, lean_object* v_j_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_506_, v___x_507_, v_n_508_, v_j_509_, v_a_510_, v_a_511_);
lean_dec(v_n_508_);
lean_dec(v___x_507_);
lean_dec_ref(v_fvars_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_529_, v_a_530_, v_x_531_);
lean_dec(v_x_531_);
lean_dec(v_a_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_534_, lean_object* v_data_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_537_, lean_object* v_i_538_, lean_object* v_source_539_, lean_object* v_target_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_538_, v_source_539_, v_target_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_lctx_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_lctx_552_ = lean_ctor_get(v_a_547_, 2);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_555_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_552_);
v___x_556_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_546_, v___x_553_, v___x_555_, v_lctx_552_, v___x_554_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
return v_x_564_;
}
else
{
lean_object* v_key_566_; lean_object* v_tail_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_key_566_ = lean_ctor_get(v_x_565_, 0);
v_tail_567_ = lean_ctor_get(v_x_565_, 2);
v___x_568_ = 1;
v___x_569_ = lean_box(v___x_568_);
v___x_570_ = lean_array_set(v_x_564_, v_key_566_, v___x_569_);
v_x_564_ = v___x_570_;
v_x_565_ = v_tail_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_572_, v_x_573_);
lean_dec(v_x_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_575_, size_t v_i_576_, size_t v_stop_577_, lean_object* v_b_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_eq(v_i_576_, v_stop_577_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; 
v___x_580_ = lean_array_uget_borrowed(v_as_575_, v_i_576_);
v___x_581_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_578_, v___x_580_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_576_, v___x_582_);
v_i_576_ = v___x_583_;
v_b_578_ = v___x_581_;
goto _start;
}
else
{
return v_b_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_585_, lean_object* v_i_586_, lean_object* v_stop_587_, lean_object* v_b_588_){
_start:
{
size_t v_i_boxed_589_; size_t v_stop_boxed_590_; lean_object* v_res_591_; 
v_i_boxed_589_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_stop_boxed_590_ = lean_unbox_usize(v_stop_587_);
lean_dec(v_stop_587_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_585_, v_i_boxed_589_, v_stop_boxed_590_, v_b_588_);
lean_dec_ref(v_as_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_592_, lean_object* v_s_593_){
_start:
{
lean_object* v_buckets_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_buckets_594_ = lean_ctor_get(v_s_593_, 1);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_array_get_size(v_buckets_594_);
v___x_597_ = lean_nat_dec_lt(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
return v_arr_592_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_le(v___x_596_, v___x_596_);
if (v___x_598_ == 0)
{
if (v___x_597_ == 0)
{
return v_arr_592_;
}
else
{
size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_596_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_594_, v___x_599_, v___x_600_, v_arr_592_);
return v___x_601_;
}
}
else
{
size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v___x_602_ = ((size_t)0ULL);
v___x_603_ = lean_usize_of_nat(v___x_596_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_594_, v___x_602_, v___x_603_, v_arr_592_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_605_, lean_object* v_s_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_605_, v_s_606_);
lean_dec_ref(v_s_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_608_, lean_object* v_numHaves_609_, lean_object* v___x_610_, lean_object* v_a_611_, lean_object* v_b_612_){
_start:
{
lean_object* v_a_615_; uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_lt(v_a_611_, v_upperBound_608_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v_a_611_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_b_612_);
return v___x_620_;
}
else
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_621_ = 0;
v___x_622_ = lean_nat_sub(v_numHaves_609_, v_a_611_);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_sub(v___x_622_, v___x_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(v___x_621_);
v___x_626_ = lean_array_get(v___x_625_, v_b_612_, v___x_624_);
lean_dec(v___x_625_);
v___x_627_ = lean_unbox(v___x_626_);
lean_dec(v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v___x_624_);
v_a_615_ = v_b_612_;
goto v___jp_614_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_typeBackDeps_630_; lean_object* v_valueBackDeps_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_628_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_629_ = lean_array_get_borrowed(v___x_628_, v___x_610_, v___x_624_);
lean_dec(v___x_624_);
v_typeBackDeps_630_ = lean_ctor_get(v___x_629_, 0);
v_valueBackDeps_631_ = lean_ctor_get(v___x_629_, 1);
v___x_632_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_612_, v_typeBackDeps_630_);
v___x_633_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_632_, v_valueBackDeps_631_);
v_a_615_ = v___x_633_;
goto v___jp_614_;
}
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_a_611_, v___x_616_);
lean_dec(v_a_611_);
v_a_611_ = v___x_617_;
v_b_612_ = v_a_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_634_, lean_object* v_numHaves_635_, lean_object* v___x_636_, lean_object* v_a_637_, lean_object* v_b_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_634_, v_numHaves_635_, v___x_636_, v_a_637_, v_b_638_);
lean_dec_ref(v___x_636_);
lean_dec(v_numHaves_635_);
lean_dec(v_upperBound_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_641_, lean_object* v_init_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_haveInfo_648_; lean_object* v_numHaves_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v_used_652_; lean_object* v___x_653_; lean_object* v_used_654_; lean_object* v___x_655_; 
v_haveInfo_648_ = lean_ctor_get(v_info_641_, 0);
v_numHaves_649_ = lean_array_get_size(v_haveInfo_648_);
v___x_650_ = 0;
v___x_651_ = lean_box(v___x_650_);
v_used_652_ = lean_mk_array(v_numHaves_649_, v___x_651_);
v___x_653_ = lean_unsigned_to_nat(0u);
v_used_654_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_652_, v_init_642_);
v___x_655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_649_, v_numHaves_649_, v_haveInfo_648_, v___x_653_, v_used_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_656_, lean_object* v_init_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_656_, v_init_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec_ref(v_init_657_);
lean_dec_ref(v_info_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_664_, lean_object* v_numHaves_665_, lean_object* v___x_666_, lean_object* v_inst_667_, lean_object* v_R_668_, lean_object* v_a_669_, lean_object* v_b_670_, lean_object* v_c_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_664_, v_numHaves_665_, v___x_666_, v_a_669_, v_b_670_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_678_, lean_object* v_numHaves_679_, lean_object* v___x_680_, lean_object* v_inst_681_, lean_object* v_R_682_, lean_object* v_a_683_, lean_object* v_b_684_, lean_object* v_c_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_678_, v_numHaves_679_, v___x_680_, v_inst_681_, v_R_682_, v_a_683_, v_b_684_, v_c_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___x_680_);
lean_dec(v_numHaves_679_);
lean_dec(v_upperBound_678_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_694_, uint8_t v_keepUnused_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_bodyDeps_701_; lean_object* v_bodyTypeDeps_702_; lean_object* v___x_703_; 
v_bodyDeps_701_ = lean_ctor_get(v_info_694_, 1);
v_bodyTypeDeps_702_ = lean_ctor_get(v_info_694_, 2);
v___x_703_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_694_, v_bodyTypeDeps_702_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
if (lean_obj_tag(v___x_703_) == 0)
{
if (v_keepUnused_695_ == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_703_);
v___x_705_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_694_, v_bodyDeps_701_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_a_704_);
lean_ctor_set(v___x_710_, 1, v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_a_704_);
v_a_715_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_705_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_705_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_732_; 
v_a_723_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_732_ == 0)
{
v___x_725_ = v___x_703_;
v_isShared_726_ = v_isSharedCheck_732_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_703_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_732_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_a_723_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_728_);
v___x_730_ = v___x_725_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
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
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_703_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_703_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_741_, lean_object* v_keepUnused_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
uint8_t v_keepUnused_boxed_748_; lean_object* v_res_749_; 
v_keepUnused_boxed_748_ = lean_unbox(v_keepUnused_742_);
v_res_749_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_741_, v_keepUnused_boxed_748_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec_ref(v_info_741_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_box(0);
v___x_754_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_755_ = l_Lean_Expr_const___override(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = 0;
v___x_757_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_758_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
lean_ctor_set(v___x_758_, 2, v___x_757_);
lean_ctor_set(v___x_758_, 3, v___x_757_);
lean_ctor_set(v___x_758_, 4, v___x_757_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*5, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_759_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_toApplicative_777_, lean_object* v_level_778_, lean_object* v_exprType_779_, lean_object* v_e_780_, uint8_t v___x_781_, lean_object* v_xs_782_, lean_object* v_____do__lift_783_){
_start:
{
if (lean_obj_tag(v_____do__lift_783_) == 0)
{
lean_object* v_toPure_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_proof_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_toPure_784_ = lean_ctor_get(v_toApplicative_777_, 1);
lean_inc(v_toPure_784_);
lean_dec_ref(v_toApplicative_777_);
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_786_ = lean_box(0);
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v_level_778_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_mkConst(v___x_785_, v___x_787_);
lean_inc_ref_n(v_e_780_, 3);
lean_inc_ref(v_exprType_779_);
v_proof_789_ = l_Lean_mkAppB(v___x_788_, v_exprType_779_, v_e_780_);
v___x_790_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_790_, 0, v_e_780_);
lean_ctor_set(v___x_790_, 1, v_exprType_779_);
lean_ctor_set(v___x_790_, 2, v_e_780_);
lean_ctor_set(v___x_790_, 3, v_e_780_);
lean_ctor_set(v___x_790_, 4, v_proof_789_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*5, v___x_781_);
v___x_791_ = lean_apply_2(v_toPure_784_, lean_box(0), v___x_790_);
return v___x_791_;
}
else
{
lean_object* v_e_792_; lean_object* v_h_793_; lean_object* v_expr_794_; lean_object* v_proof_795_; lean_object* v___x_801_; uint8_t v___x_802_; 
lean_dec(v_level_778_);
v_e_792_ = lean_ctor_get(v_____do__lift_783_, 0);
v_h_793_ = lean_ctor_get(v_____do__lift_783_, 1);
v_expr_794_ = lean_expr_abstract(v_e_792_, v_xs_782_);
v_proof_795_ = lean_expr_abstract(v_h_793_, v_xs_782_);
lean_inc_ref(v_proof_795_);
v___x_801_ = l_Lean_Expr_cleanupAnnotations(v_proof_795_);
v___x_802_ = l_Lean_Expr_isApp(v___x_801_);
if (v___x_802_ == 0)
{
lean_dec_ref(v___x_801_);
goto v___jp_796_;
}
else
{
lean_object* v_arg_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_arg_803_ = lean_ctor_get(v___x_801_, 1);
lean_inc_ref(v_arg_803_);
v___x_804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_801_);
v___x_805_ = l_Lean_Expr_isApp(v___x_804_);
if (v___x_805_ == 0)
{
lean_dec_ref(v___x_804_);
lean_dec_ref(v_arg_803_);
goto v___jp_796_;
}
else
{
lean_object* v_arg_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_arg_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc_ref(v_arg_806_);
v___x_807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_804_);
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_809_ = l_Lean_Expr_isConstOf(v___x_807_, v___x_808_);
lean_dec_ref(v___x_807_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
goto v___jp_796_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_811_ = lean_unsigned_to_nat(3u);
v___x_812_ = l_Lean_Expr_isAppOfArity(v_arg_806_, v___x_810_, v___x_811_);
lean_dec_ref(v_arg_806_);
if (v___x_812_ == 0)
{
lean_dec_ref(v_arg_803_);
goto v___jp_796_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = l_Lean_Expr_cleanupAnnotations(v_arg_803_);
v___x_814_ = l_Lean_Expr_isApp(v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v___x_813_);
goto v___jp_796_;
}
else
{
lean_object* v_arg_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_arg_815_ = lean_ctor_get(v___x_813_, 1);
lean_inc_ref(v_arg_815_);
v___x_816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_813_);
v___x_817_ = l_Lean_Expr_isApp(v___x_816_);
if (v___x_817_ == 0)
{
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v_arg_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_arg_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc_ref(v_arg_818_);
v___x_819_ = l_Lean_Expr_appFnCleanup___redArg(v___x_816_);
v___x_820_ = l_Lean_Expr_isConstOf(v___x_819_, v___x_808_);
lean_dec_ref(v___x_819_);
if (v___x_820_ == 0)
{
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = l_Lean_Expr_cleanupAnnotations(v_arg_818_);
v___x_822_ = l_Lean_Expr_isApp(v___x_821_);
if (v___x_822_ == 0)
{
lean_dec_ref(v___x_821_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v_arg_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_arg_823_ = lean_ctor_get(v___x_821_, 1);
lean_inc_ref(v_arg_823_);
v___x_824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_821_);
v___x_825_ = l_Lean_Expr_isApp(v___x_824_);
if (v___x_825_ == 0)
{
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v_arg_826_; uint8_t v___y_828_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_arg_826_ = lean_ctor_get(v___x_824_, 1);
lean_inc_ref(v_arg_826_);
v___x_832_ = l_Lean_Expr_appFnCleanup___redArg(v___x_824_);
v___x_833_ = l_Lean_Expr_isApp(v___x_832_);
if (v___x_833_ == 0)
{
lean_dec_ref(v___x_832_);
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_832_);
v___x_835_ = l_Lean_Expr_isConstOf(v___x_834_, v___x_810_);
lean_dec_ref(v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Expr_getAppFn(v_arg_815_);
if (lean_obj_tag(v___x_836_) == 4)
{
lean_object* v_declName_837_; 
v_declName_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_declName_837_);
lean_dec_ref(v___x_836_);
if (lean_obj_tag(v_declName_837_) == 1)
{
lean_object* v_pre_838_; 
v_pre_838_ = lean_ctor_get(v_declName_837_, 0);
if (lean_obj_tag(v_pre_838_) == 0)
{
lean_object* v_str_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_str_839_ = lean_ctor_get(v_declName_837_, 1);
lean_inc_ref(v_str_839_);
lean_dec_ref(v_declName_837_);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_841_ = lean_string_dec_eq(v_str_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_843_ = lean_string_dec_eq(v_str_839_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_845_ = lean_string_dec_eq(v_str_839_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_847_ = lean_string_dec_eq(v_str_839_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_849_ = lean_string_dec_eq(v_str_839_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_851_ = lean_string_dec_eq(v_str_839_, v___x_850_);
lean_dec_ref(v_str_839_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
v___y_828_ = v___x_809_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v_str_839_);
v___y_828_ = v___x_809_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v_str_839_);
v___y_828_ = v___x_809_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v_str_839_);
v___y_828_ = v___x_809_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v_str_839_);
v___y_828_ = v___x_809_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v_str_839_);
v___y_828_ = v___x_809_;
goto v___jp_827_;
}
}
else
{
lean_dec_ref(v_declName_837_);
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
}
else
{
lean_dec(v_declName_837_);
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
}
else
{
lean_dec_ref(v___x_836_);
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
}
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_dec_ref(v_arg_826_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_815_);
goto v___jp_796_;
}
else
{
lean_object* v_toPure_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v_proof_795_);
lean_dec_ref(v_e_780_);
v_toPure_829_ = lean_ctor_get(v_toApplicative_777_, 1);
lean_inc(v_toPure_829_);
lean_dec_ref(v_toApplicative_777_);
v___x_830_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_830_, 0, v_arg_823_);
lean_ctor_set(v___x_830_, 1, v_exprType_779_);
lean_ctor_set(v___x_830_, 2, v_arg_826_);
lean_ctor_set(v___x_830_, 3, v_expr_794_);
lean_ctor_set(v___x_830_, 4, v_arg_815_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*5, v___x_809_);
v___x_831_ = lean_apply_2(v_toPure_829_, lean_box(0), v___x_830_);
return v___x_831_;
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
v___jp_796_:
{
lean_object* v_toPure_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_toPure_797_ = lean_ctor_get(v_toApplicative_777_, 1);
lean_inc(v_toPure_797_);
lean_dec_ref(v_toApplicative_777_);
v___x_798_ = 1;
lean_inc_ref(v_expr_794_);
v___x_799_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_799_, 0, v_expr_794_);
lean_ctor_set(v___x_799_, 1, v_exprType_779_);
lean_ctor_set(v___x_799_, 2, v_e_780_);
lean_ctor_set(v___x_799_, 3, v_expr_794_);
lean_ctor_set(v___x_799_, 4, v_proof_795_);
lean_ctor_set_uint8(v___x_799_, sizeof(void*)*5, v___x_798_);
v___x_800_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_toApplicative_852_, lean_object* v_level_853_, lean_object* v_exprType_854_, lean_object* v_e_855_, lean_object* v___x_856_, lean_object* v_xs_857_, lean_object* v_____do__lift_858_){
_start:
{
uint8_t v___x_12300__boxed_859_; lean_object* v_res_860_; 
v___x_12300__boxed_859_ = lean_unbox(v___x_856_);
v_res_860_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_852_, v_level_853_, v_exprType_854_, v_e_855_, v___x_12300__boxed_859_, v_xs_857_, v_____do__lift_858_);
lean_dec(v_____do__lift_858_);
lean_dec_ref(v_xs_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_861_, lean_object* v_bodyType_862_, lean_object* v_xs_863_, lean_object* v_toApplicative_864_, lean_object* v_level_865_, lean_object* v_e_866_, uint8_t v___x_867_, lean_object* v_body_868_, lean_object* v_toBind_869_, lean_object* v_____r_870_){
_start:
{
lean_object* v_simp_871_; lean_object* v_exprType_872_; lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_simp_871_ = lean_ctor_get(v_inst_861_, 2);
lean_inc(v_simp_871_);
lean_dec_ref(v_inst_861_);
v_exprType_872_ = lean_expr_abstract(v_bodyType_862_, v_xs_863_);
v___x_873_ = lean_box(v___x_867_);
v___f_874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_874_, 0, v_toApplicative_864_);
lean_closure_set(v___f_874_, 1, v_level_865_);
lean_closure_set(v___f_874_, 2, v_exprType_872_);
lean_closure_set(v___f_874_, 3, v_e_866_);
lean_closure_set(v___f_874_, 4, v___x_873_);
lean_closure_set(v___f_874_, 5, v_xs_863_);
v___x_875_ = lean_apply_1(v_simp_871_, v_body_868_);
v___x_876_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_875_, v___f_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_877_, lean_object* v_bodyType_878_, lean_object* v_xs_879_, lean_object* v_toApplicative_880_, lean_object* v_level_881_, lean_object* v_e_882_, lean_object* v___x_883_, lean_object* v_body_884_, lean_object* v_toBind_885_, lean_object* v_____r_886_){
_start:
{
uint8_t v___x_12453__boxed_887_; lean_object* v_res_888_; 
v___x_12453__boxed_887_ = lean_unbox(v___x_883_);
v_res_888_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_877_, v_bodyType_878_, v_xs_879_, v_toApplicative_880_, v_level_881_, v_e_882_, v___x_12453__boxed_887_, v_body_884_, v_toBind_885_, v_____r_886_);
lean_dec_ref(v_bodyType_878_);
return v_res_888_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4));
v___x_896_ = l_Lean_stringToMessageData(v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_897_, lean_object* v___x_898_, lean_object* v___f_899_, lean_object* v_body_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_options_911_; uint8_t v_hasTrace_912_; 
v_options_911_ = lean_ctor_get(v___y_905_, 2);
v_hasTrace_912_ = lean_ctor_get_uint8(v_options_911_, sizeof(void*)*1);
if (v_hasTrace_912_ == 0)
{
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v_body_900_);
lean_dec(v___f_899_);
lean_dec(v___x_898_);
lean_dec(v_cls_897_);
goto v___jp_908_;
}
else
{
lean_object* v_inheritedTraceOptions_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_inheritedTraceOptions_913_ = lean_ctor_get(v___y_905_, 13);
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_897_);
v___x_915_ = l_Lean_Name_append(v___x_914_, v_cls_897_);
v___x_916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_913_, v_options_911_, v___x_915_);
lean_dec(v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v_body_900_);
lean_dec(v___f_899_);
lean_dec(v___x_898_);
lean_dec(v_cls_897_);
goto v___jp_908_;
}
else
{
lean_object* v___f_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_toMonadRef_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_11855__overap_927_; lean_object* v___x_928_; 
v___f_917_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_919_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_920_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_918_, v___x_898_, v___x_919_);
v___x_921_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_917_, v___f_899_, v___x_920_);
v_toMonadRef_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5);
v___x_925_ = l_Lean_MessageData_ofExpr(v_body_900_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_11855__overap_927_ = l_Lean_addTrace___redArg(v___x_901_, v___x_902_, v_toMonadRef_922_, v___x_923_, v_cls_897_, v___x_926_);
v___x_928_ = lean_apply_5(v___x_11855__overap_927_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
return v___x_928_;
}
}
v___jp_908_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_929_, lean_object* v___x_930_, lean_object* v___f_931_, lean_object* v_body_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_929_, v___x_930_, v___f_931_, v_body_932_, v___x_933_, v___x_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_943_, lean_object* v_type_944_, lean_object* v___y_945_, lean_object* v_value_946_, uint8_t v_nondep_947_, lean_object* v_toApplicative_948_, lean_object* v___x_949_, uint8_t v___y_950_, lean_object* v_us_951_, lean_object* v_rb_952_){
_start:
{
lean_object* v_expr_953_; lean_object* v_exprType_954_; lean_object* v_exprInit_955_; lean_object* v_exprResult_956_; lean_object* v_proof_957_; uint8_t v_modified_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_987_; 
v_expr_953_ = lean_ctor_get(v_rb_952_, 0);
v_exprType_954_ = lean_ctor_get(v_rb_952_, 1);
v_exprInit_955_ = lean_ctor_get(v_rb_952_, 2);
v_exprResult_956_ = lean_ctor_get(v_rb_952_, 3);
v_proof_957_ = lean_ctor_get(v_rb_952_, 4);
v_modified_958_ = lean_ctor_get_uint8(v_rb_952_, sizeof(void*)*5);
v_isSharedCheck_987_ = !lean_is_exclusive(v_rb_952_);
if (v_isSharedCheck_987_ == 0)
{
v___x_960_ = v_rb_952_;
v_isShared_961_ = v_isSharedCheck_987_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_proof_957_);
lean_inc(v_exprResult_956_);
lean_inc(v_exprInit_955_);
lean_inc(v_exprType_954_);
lean_inc(v_expr_953_);
lean_dec(v_rb_952_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_987_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v_expr_964_; lean_object* v___x_965_; lean_object* v_exprType_966_; lean_object* v___x_967_; lean_object* v_exprInit_968_; lean_object* v_exprResult_969_; 
v___x_962_ = 0;
lean_inc_ref_n(v_type_944_, 4);
lean_inc_n(v_declName_943_, 4);
v___x_963_ = l_Lean_mkLambda(v_declName_943_, v___x_962_, v_type_944_, v_expr_953_);
lean_inc_ref_n(v___y_945_, 3);
lean_inc_ref(v___x_963_);
v_expr_964_ = l_Lean_Expr_app___override(v___x_963_, v___y_945_);
v___x_965_ = l_Lean_mkLambda(v_declName_943_, v___x_962_, v_type_944_, v_exprType_954_);
lean_inc_ref(v___x_965_);
v_exprType_966_ = l_Lean_Expr_app___override(v___x_965_, v___y_945_);
v___x_967_ = l_Lean_mkLambda(v_declName_943_, v___x_962_, v_type_944_, v_exprInit_955_);
lean_inc_ref(v___x_967_);
v_exprInit_968_ = l_Lean_Expr_app___override(v___x_967_, v_value_946_);
v_exprResult_969_ = l_Lean_Expr_letE___override(v_declName_943_, v_type_944_, v___y_945_, v_exprResult_956_, v_nondep_947_);
if (v_modified_958_ == 0)
{
lean_object* v_toPure_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_proof_973_; lean_object* v___x_975_; 
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_965_);
lean_dec_ref(v___x_963_);
lean_dec_ref(v_proof_957_);
lean_dec(v_us_951_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_type_944_);
lean_dec(v_declName_943_);
v_toPure_970_ = lean_ctor_get(v_toApplicative_948_, 1);
lean_inc(v_toPure_970_);
lean_dec_ref(v_toApplicative_948_);
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_972_ = l_Lean_mkConst(v___x_971_, v___x_949_);
lean_inc_ref(v_expr_964_);
lean_inc_ref(v_exprType_966_);
v_proof_973_ = l_Lean_mkAppB(v___x_972_, v_exprType_966_, v_expr_964_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v_proof_973_);
lean_ctor_set(v___x_960_, 3, v_exprResult_969_);
lean_ctor_set(v___x_960_, 2, v_exprInit_968_);
lean_ctor_set(v___x_960_, 1, v_exprType_966_);
lean_ctor_set(v___x_960_, 0, v_expr_964_);
v___x_975_ = v___x_960_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_expr_964_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_exprType_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_exprInit_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_exprResult_969_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_proof_973_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; 
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*5, v___y_950_);
v___x_976_ = lean_apply_2(v_toPure_970_, lean_box(0), v___x_975_);
return v___x_976_;
}
}
else
{
lean_object* v_toPure_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_proof_982_; lean_object* v___x_984_; 
lean_dec(v___x_949_);
v_toPure_978_ = lean_ctor_get(v_toApplicative_948_, 1);
lean_inc(v_toPure_978_);
lean_dec_ref(v_toApplicative_948_);
lean_inc_ref(v_type_944_);
v___x_979_ = l_Lean_mkLambda(v_declName_943_, v___x_962_, v_type_944_, v_proof_957_);
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_981_ = l_Lean_mkConst(v___x_980_, v_us_951_);
v_proof_982_ = l_Lean_mkApp6(v___x_981_, v_type_944_, v___x_965_, v___y_945_, v___x_967_, v___x_963_, v___x_979_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v_proof_982_);
lean_ctor_set(v___x_960_, 3, v_exprResult_969_);
lean_ctor_set(v___x_960_, 2, v_exprInit_968_);
lean_ctor_set(v___x_960_, 1, v_exprType_966_);
lean_ctor_set(v___x_960_, 0, v_expr_964_);
v___x_984_ = v___x_960_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_expr_964_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_exprType_966_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_exprInit_968_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_exprResult_969_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_proof_982_);
v___x_984_ = v_reuseFailAlloc_986_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; 
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*5, v_nondep_947_);
v___x_985_ = lean_apply_2(v_toPure_978_, lean_box(0), v___x_984_);
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_988_, lean_object* v_type_989_, lean_object* v___y_990_, lean_object* v_value_991_, lean_object* v_nondep_992_, lean_object* v_toApplicative_993_, lean_object* v___x_994_, lean_object* v___y_995_, lean_object* v_us_996_, lean_object* v_rb_997_){
_start:
{
uint8_t v_nondep_12569__boxed_998_; uint8_t v___y_12571__boxed_999_; lean_object* v_res_1000_; 
v_nondep_12569__boxed_998_ = lean_unbox(v_nondep_992_);
v___y_12571__boxed_999_ = lean_unbox(v___y_995_);
v_res_1000_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_988_, v_type_989_, v___y_990_, v_value_991_, v_nondep_12569__boxed_998_, v_toApplicative_993_, v___x_994_, v___y_12571__boxed_999_, v_us_996_, v_rb_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1001_, lean_object* v_____x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_apply_1(v___f_1001_, v_____x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1008_, lean_object* v_declName_1009_, lean_object* v_type_1010_, lean_object* v_value_1011_, lean_object* v_us_1012_, lean_object* v___x_1013_, lean_object* v_toApplicative_1014_, uint8_t v_nondep_1015_, lean_object* v_rb_1016_){
_start:
{
lean_object* v_expr_1017_; lean_object* v_exprType_1018_; lean_object* v_exprInit_1019_; lean_object* v_exprResult_1020_; lean_object* v_proof_1021_; uint8_t v_modified_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1052_; 
v_expr_1017_ = lean_ctor_get(v_rb_1016_, 0);
v_exprType_1018_ = lean_ctor_get(v_rb_1016_, 1);
v_exprInit_1019_ = lean_ctor_get(v_rb_1016_, 2);
v_exprResult_1020_ = lean_ctor_get(v_rb_1016_, 3);
v_proof_1021_ = lean_ctor_get(v_rb_1016_, 4);
v_modified_1022_ = lean_ctor_get_uint8(v_rb_1016_, sizeof(void*)*5);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_rb_1016_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1024_ = v_rb_1016_;
v_isShared_1025_ = v_isSharedCheck_1052_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_proof_1021_);
lean_inc(v_exprResult_1020_);
lean_inc(v_exprInit_1019_);
lean_inc(v_exprType_1018_);
lean_inc(v_expr_1017_);
lean_dec(v_rb_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1052_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_expr_1026_; lean_object* v_exprType_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v_exprInit_1030_; lean_object* v_exprResult_1031_; 
v_expr_1026_ = lean_expr_lower_loose_bvars(v_expr_1017_, v___x_1008_, v___x_1008_);
lean_dec_ref(v_expr_1017_);
v_exprType_1027_ = lean_expr_lower_loose_bvars(v_exprType_1018_, v___x_1008_, v___x_1008_);
lean_dec_ref(v_exprType_1018_);
v___x_1028_ = 0;
lean_inc_ref(v_type_1010_);
lean_inc(v_declName_1009_);
v___x_1029_ = l_Lean_mkLambda(v_declName_1009_, v___x_1028_, v_type_1010_, v_exprInit_1019_);
lean_inc_ref(v_value_1011_);
lean_inc_ref(v___x_1029_);
v_exprInit_1030_ = l_Lean_Expr_app___override(v___x_1029_, v_value_1011_);
v_exprResult_1031_ = lean_expr_lower_loose_bvars(v_exprResult_1020_, v___x_1008_, v___x_1008_);
lean_dec_ref(v_exprResult_1020_);
if (v_modified_1022_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_proof_1037_; lean_object* v_toPure_1038_; lean_object* v___x_1040_; 
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_proof_1021_);
lean_dec(v_declName_1009_);
v___x_1032_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1033_ = l_Lean_mkConst(v___x_1032_, v_us_1012_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1035_ = l_Lean_mkConst(v___x_1034_, v___x_1013_);
lean_inc_ref_n(v_expr_1026_, 3);
lean_inc_ref_n(v_exprType_1027_, 2);
v___x_1036_ = l_Lean_mkAppB(v___x_1035_, v_exprType_1027_, v_expr_1026_);
v_proof_1037_ = l_Lean_mkApp6(v___x_1033_, v_type_1010_, v_exprType_1027_, v_value_1011_, v_expr_1026_, v_expr_1026_, v___x_1036_);
v_toPure_1038_ = lean_ctor_get(v_toApplicative_1014_, 1);
lean_inc(v_toPure_1038_);
lean_dec_ref(v_toApplicative_1014_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v_proof_1037_);
lean_ctor_set(v___x_1024_, 3, v_exprResult_1031_);
lean_ctor_set(v___x_1024_, 2, v_exprInit_1030_);
lean_ctor_set(v___x_1024_, 1, v_exprType_1027_);
lean_ctor_set(v___x_1024_, 0, v_expr_1026_);
v___x_1040_ = v___x_1024_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_expr_1026_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_exprType_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_exprInit_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_exprResult_1031_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_proof_1037_);
v___x_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
lean_ctor_set_uint8(v___x_1040_, sizeof(void*)*5, v_nondep_1015_);
v___x_1041_ = lean_apply_2(v_toPure_1038_, lean_box(0), v___x_1040_);
return v___x_1041_;
}
}
else
{
lean_object* v_toPure_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_proof_1047_; lean_object* v___x_1049_; 
lean_dec(v___x_1013_);
v_toPure_1043_ = lean_ctor_get(v_toApplicative_1014_, 1);
lean_inc(v_toPure_1043_);
lean_dec_ref(v_toApplicative_1014_);
lean_inc_ref(v_type_1010_);
v___x_1044_ = l_Lean_mkLambda(v_declName_1009_, v___x_1028_, v_type_1010_, v_proof_1021_);
v___x_1045_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1046_ = l_Lean_mkConst(v___x_1045_, v_us_1012_);
lean_inc_ref(v_expr_1026_);
lean_inc_ref(v_exprType_1027_);
v_proof_1047_ = l_Lean_mkApp6(v___x_1046_, v_type_1010_, v_exprType_1027_, v_value_1011_, v___x_1029_, v_expr_1026_, v___x_1044_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v_proof_1047_);
lean_ctor_set(v___x_1024_, 3, v_exprResult_1031_);
lean_ctor_set(v___x_1024_, 2, v_exprInit_1030_);
lean_ctor_set(v___x_1024_, 1, v_exprType_1027_);
lean_ctor_set(v___x_1024_, 0, v_expr_1026_);
v___x_1049_ = v___x_1024_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_expr_1026_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_exprType_1027_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_exprInit_1030_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_exprResult_1031_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_proof_1047_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*5, v_nondep_1015_);
v___x_1050_ = lean_apply_2(v_toPure_1043_, lean_box(0), v___x_1049_);
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1053_, lean_object* v_declName_1054_, lean_object* v_type_1055_, lean_object* v_value_1056_, lean_object* v_us_1057_, lean_object* v___x_1058_, lean_object* v_toApplicative_1059_, lean_object* v_nondep_1060_, lean_object* v_rb_1061_){
_start:
{
uint8_t v_nondep_12656__boxed_1062_; lean_object* v_res_1063_; 
v_nondep_12656__boxed_1062_ = lean_unbox(v_nondep_1060_);
v_res_1063_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1053_, v_declName_1054_, v_type_1055_, v_value_1056_, v_us_1057_, v___x_1058_, v_toApplicative_1059_, v_nondep_12656__boxed_1062_, v_rb_1061_);
lean_dec(v___x_1053_);
return v_res_1063_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1070_, lean_object* v___x_1071_, lean_object* v___f_1072_, lean_object* v_declName_1073_, lean_object* v_val_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_options_1085_; uint8_t v_hasTrace_1086_; 
v_options_1085_ = lean_ctor_get(v___y_1079_, 2);
v_hasTrace_1086_ = lean_ctor_get_uint8(v_options_1085_, sizeof(void*)*1);
if (v_hasTrace_1086_ == 0)
{
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v_val_1074_);
lean_dec(v_declName_1073_);
lean_dec(v___f_1072_);
lean_dec(v___x_1071_);
lean_dec(v_cls_1070_);
goto v___jp_1082_;
}
else
{
lean_object* v_inheritedTraceOptions_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_inheritedTraceOptions_1087_ = lean_ctor_get(v___y_1079_, 13);
v___x_1088_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1070_);
v___x_1089_ = l_Lean_Name_append(v___x_1088_, v_cls_1070_);
v___x_1090_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1087_, v_options_1085_, v___x_1089_);
lean_dec(v___x_1089_);
if (v___x_1090_ == 0)
{
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v_val_1074_);
lean_dec(v_declName_1073_);
lean_dec(v___f_1072_);
lean_dec(v___x_1071_);
lean_dec(v_cls_1070_);
goto v___jp_1082_;
}
else
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_toMonadRef_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_12266__overap_1105_; lean_object* v___x_1106_; 
v___f_1091_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1092_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1093_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1094_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1092_, v___x_1071_, v___x_1093_);
v___x_1095_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1091_, v___f_1072_, v___x_1094_);
v_toMonadRef_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_toMonadRef_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1099_ = l_Lean_MessageData_ofName(v_declName_1073_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_ofExpr(v_val_1074_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_12266__overap_1105_ = l_Lean_addTrace___redArg(v___x_1075_, v___x_1076_, v_toMonadRef_1096_, v___x_1097_, v_cls_1070_, v___x_1104_);
v___x_1106_ = lean_apply_5(v___x_12266__overap_1105_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, lean_box(0));
return v___x_1106_;
}
}
v___jp_1082_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1107_, lean_object* v___x_1108_, lean_object* v___f_1109_, lean_object* v_declName_1110_, lean_object* v_val_1111_, lean_object* v___x_1112_, lean_object* v___x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1107_, v___x_1108_, v___f_1109_, v_declName_1110_, v_val_1111_, v___x_1112_, v___x_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v_res_1119_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1126_, lean_object* v___x_1127_, lean_object* v___f_1128_, lean_object* v_declName_1129_, lean_object* v_val_1130_, lean_object* v_val_x27_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_options_1142_; uint8_t v_hasTrace_1143_; 
v_options_1142_ = lean_ctor_get(v___y_1136_, 2);
v_hasTrace_1143_ = lean_ctor_get_uint8(v_options_1142_, sizeof(void*)*1);
if (v_hasTrace_1143_ == 0)
{
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_val_x27_1131_);
lean_dec_ref(v_val_1130_);
lean_dec(v_declName_1129_);
lean_dec(v___f_1128_);
lean_dec(v___x_1127_);
lean_dec(v_cls_1126_);
goto v___jp_1139_;
}
else
{
lean_object* v_inheritedTraceOptions_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_inheritedTraceOptions_1144_ = lean_ctor_get(v___y_1136_, 13);
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1126_);
v___x_1146_ = l_Lean_Name_append(v___x_1145_, v_cls_1126_);
v___x_1147_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1144_, v_options_1142_, v___x_1146_);
lean_dec(v___x_1146_);
if (v___x_1147_ == 0)
{
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_val_x27_1131_);
lean_dec_ref(v_val_1130_);
lean_dec(v_declName_1129_);
lean_dec(v___f_1128_);
lean_dec(v___x_1127_);
lean_dec(v_cls_1126_);
goto v___jp_1139_;
}
else
{
lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_toMonadRef_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_11948__overap_1166_; lean_object* v___x_1167_; 
v___f_1148_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1150_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1151_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1149_, v___x_1127_, v___x_1150_);
v___x_1152_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1148_, v___f_1128_, v___x_1151_);
v_toMonadRef_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc_ref(v_toMonadRef_1153_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1155_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1156_ = l_Lean_MessageData_ofName(v_declName_1129_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_ofExpr(v_val_1130_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_ofExpr(v_val_x27_1131_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_11948__overap_1166_ = l_Lean_addTrace___redArg(v___x_1132_, v___x_1133_, v_toMonadRef_1153_, v___x_1154_, v_cls_1126_, v___x_1165_);
v___x_1167_ = lean_apply_5(v___x_11948__overap_1166_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, lean_box(0));
return v___x_1167_;
}
}
v___jp_1139_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1168_, lean_object* v___x_1169_, lean_object* v___f_1170_, lean_object* v_declName_1171_, lean_object* v_val_1172_, lean_object* v_val_x27_1173_, lean_object* v___x_1174_, lean_object* v___x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1168_, v___x_1169_, v___f_1170_, v_declName_1171_, v_val_1172_, v_val_x27_1173_, v___x_1174_, v___x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_toApplicative_1182_, lean_object* v_e_1183_, lean_object* v_xs_1184_, lean_object* v_h_1185_, uint8_t v_nondep_1186_, lean_object* v_toBind_1187_, lean_object* v___f_1188_, lean_object* v_____r_1189_){
_start:
{
lean_object* v_toPure_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_toPure_1190_ = lean_ctor_get(v_toApplicative_1182_, 1);
lean_inc(v_toPure_1190_);
lean_dec_ref(v_toApplicative_1182_);
v___x_1191_ = lean_expr_abstract(v_e_1183_, v_xs_1184_);
v___x_1192_ = lean_expr_abstract(v_h_1185_, v_xs_1184_);
v___x_1193_ = lean_box(v_nondep_1186_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___x_1192_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1191_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_apply_2(v_toPure_1190_, lean_box(0), v___x_1195_);
v___x_1197_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1196_, v___f_1188_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_toApplicative_1198_, lean_object* v_e_1199_, lean_object* v_xs_1200_, lean_object* v_h_1201_, lean_object* v_nondep_1202_, lean_object* v_toBind_1203_, lean_object* v___f_1204_, lean_object* v_____r_1205_){
_start:
{
uint8_t v_nondep_12922__boxed_1206_; lean_object* v_res_1207_; 
v_nondep_12922__boxed_1206_ = lean_unbox(v_nondep_1202_);
v_res_1207_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1198_, v_e_1199_, v_xs_1200_, v_h_1201_, v_nondep_12922__boxed_1206_, v_toBind_1203_, v___f_1204_, v_____r_1205_);
lean_dec_ref(v_h_1201_);
lean_dec_ref(v_xs_1200_);
lean_dec_ref(v_e_1199_);
return v_res_1207_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1211_, lean_object* v___x_1212_, lean_object* v___f_1213_, lean_object* v_declName_1214_, lean_object* v_val_1215_, lean_object* v_e_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_options_1227_; uint8_t v_hasTrace_1228_; 
v_options_1227_ = lean_ctor_get(v___y_1221_, 2);
v_hasTrace_1228_ = lean_ctor_get_uint8(v_options_1227_, sizeof(void*)*1);
if (v_hasTrace_1228_ == 0)
{
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_val_1215_);
lean_dec(v_declName_1214_);
lean_dec(v___f_1213_);
lean_dec(v___x_1212_);
lean_dec(v_cls_1211_);
goto v___jp_1224_;
}
else
{
lean_object* v_inheritedTraceOptions_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_inheritedTraceOptions_1229_ = lean_ctor_get(v___y_1221_, 13);
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1211_);
v___x_1231_ = l_Lean_Name_append(v___x_1230_, v_cls_1211_);
v___x_1232_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1229_, v_options_1227_, v___x_1231_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_val_1215_);
lean_dec(v_declName_1214_);
lean_dec(v___f_1213_);
lean_dec(v___x_1212_);
lean_dec(v_cls_1211_);
goto v___jp_1224_;
}
else
{
lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_toMonadRef_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_12128__overap_1251_; lean_object* v___x_1252_; 
v___f_1233_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1235_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1236_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1234_, v___x_1212_, v___x_1235_);
v___x_1237_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1233_, v___f_1213_, v___x_1236_);
v_toMonadRef_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc_ref(v_toMonadRef_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1240_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1241_ = l_Lean_MessageData_ofName(v_declName_1214_);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_MessageData_ofExpr(v_val_1215_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = l_Lean_MessageData_ofExpr(v_e_1216_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_12128__overap_1251_ = l_Lean_addTrace___redArg(v___x_1217_, v___x_1218_, v_toMonadRef_1238_, v___x_1239_, v_cls_1211_, v___x_1250_);
v___x_1252_ = lean_apply_5(v___x_12128__overap_1251_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, lean_box(0));
return v___x_1252_;
}
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1253_, lean_object* v___x_1254_, lean_object* v___f_1255_, lean_object* v_declName_1256_, lean_object* v_val_1257_, lean_object* v_e_1258_, lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1253_, v___x_1254_, v___f_1255_, v_declName_1256_, v_val_1257_, v_e_1258_, v___x_1259_, v___x_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v_res_1266_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_instMonadEIO(lean_box(0));
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
v___x_1269_ = l_StateRefT_x27_instMonad___redArg(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1287_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1286_, v___x_1285_);
return v___x_1287_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
v___f_1289_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1290_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1289_, v___x_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_toApplicative_1291_, lean_object* v_level_1292_, lean_object* v___x_1293_, lean_object* v_type_1294_, lean_object* v_value_1295_, uint8_t v___x_1296_, lean_object* v_toBind_1297_, lean_object* v___f_1298_, lean_object* v_xs_1299_, uint8_t v_nondep_1300_, lean_object* v___f_1301_, lean_object* v_declName_1302_, lean_object* v_val_1303_, lean_object* v_inst_1304_, lean_object* v_____do__lift_1305_){
_start:
{
if (lean_obj_tag(v_____do__lift_1305_) == 0)
{
lean_object* v_toPure_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_inst_1304_);
lean_dec_ref(v_val_1303_);
lean_dec(v_declName_1302_);
lean_dec(v___f_1301_);
lean_dec_ref(v_xs_1299_);
v_toPure_1306_ = lean_ctor_get(v_toApplicative_1291_, 1);
lean_inc(v_toPure_1306_);
lean_dec_ref(v_toApplicative_1291_);
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_level_1292_);
lean_ctor_set(v___x_1308_, 1, v___x_1293_);
v___x_1309_ = l_Lean_mkConst(v___x_1307_, v___x_1308_);
lean_inc_ref(v_value_1295_);
v___x_1310_ = l_Lean_mkAppB(v___x_1309_, v_type_1294_, v_value_1295_);
v___x_1311_ = lean_box(v___x_1296_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_value_1295_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_apply_2(v_toPure_1306_, lean_box(0), v___x_1313_);
v___x_1315_ = lean_apply_4(v_toBind_1297_, lean_box(0), lean_box(0), v___x_1314_, v___f_1298_);
return v___x_1315_;
}
else
{
lean_object* v_e_1316_; lean_object* v_h_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v___f_1298_);
lean_dec_ref(v_value_1295_);
lean_dec_ref(v_type_1294_);
lean_dec(v___x_1293_);
lean_dec(v_level_1292_);
v_e_1316_ = lean_ctor_get(v_____do__lift_1305_, 0);
v_h_1317_ = lean_ctor_get(v_____do__lift_1305_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_____do__lift_1305_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1319_ = v_____do__lift_1305_;
v_isShared_1320_ = v_isSharedCheck_1378_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_h_1317_);
lean_inc(v_e_1316_);
lean_dec(v_____do__lift_1305_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1378_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v_toApplicative_1322_; lean_object* v_toFunctor_1323_; lean_object* v_toSeq_1324_; lean_object* v_toSeqLeft_1325_; lean_object* v_toSeqRight_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___f_1329_; lean_object* v___f_1330_; lean_object* v___x_1332_; 
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1322_ = lean_ctor_get(v___x_1321_, 0);
v_toFunctor_1323_ = lean_ctor_get(v_toApplicative_1322_, 0);
v_toSeq_1324_ = lean_ctor_get(v_toApplicative_1322_, 2);
v_toSeqLeft_1325_ = lean_ctor_get(v_toApplicative_1322_, 3);
v_toSeqRight_1326_ = lean_ctor_get(v_toApplicative_1322_, 4);
v___f_1327_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1328_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1323_, 2);
v___f_1329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1329_, 0, v_toFunctor_1323_);
v___f_1330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1330_, 0, v_toFunctor_1323_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
lean_ctor_set(v___x_1319_, 1, v___f_1330_);
lean_ctor_set(v___x_1319_, 0, v___f_1329_);
v___x_1332_ = v___x_1319_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___f_1329_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___f_1330_);
v___x_1332_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___f_1333_; lean_object* v___f_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_toApplicative_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1375_; 
lean_inc(v_toSeqRight_1326_);
v___f_1333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1333_, 0, v_toSeqRight_1326_);
lean_inc(v_toSeqLeft_1325_);
v___f_1334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1334_, 0, v_toSeqLeft_1325_);
lean_inc(v_toSeq_1324_);
v___f_1335_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1335_, 0, v_toSeq_1324_);
v___x_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1332_);
lean_ctor_set(v___x_1336_, 1, v___f_1327_);
lean_ctor_set(v___x_1336_, 2, v___f_1335_);
lean_ctor_set(v___x_1336_, 3, v___f_1334_);
lean_ctor_set(v___x_1336_, 4, v___f_1333_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___f_1328_);
v___x_1338_ = l_StateRefT_x27_instMonad___redArg(v___x_1337_);
v_toApplicative_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1338_, 1);
lean_dec(v_unused_1376_);
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1375_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_toApplicative_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1375_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_toFunctor_1343_; lean_object* v_toSeq_1344_; lean_object* v_toSeqLeft_1345_; lean_object* v_toSeqRight_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1373_; 
v_toFunctor_1343_ = lean_ctor_get(v_toApplicative_1339_, 0);
v_toSeq_1344_ = lean_ctor_get(v_toApplicative_1339_, 2);
v_toSeqLeft_1345_ = lean_ctor_get(v_toApplicative_1339_, 3);
v_toSeqRight_1346_ = lean_ctor_get(v_toApplicative_1339_, 4);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_toApplicative_1339_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_toApplicative_1339_, 1);
lean_dec(v_unused_1374_);
v___x_1348_ = v_toApplicative_1339_;
v_isShared_1349_ = v_isSharedCheck_1373_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_toSeqRight_1346_);
lean_inc(v_toSeqLeft_1345_);
lean_inc(v_toSeq_1344_);
lean_inc(v_toFunctor_1343_);
lean_dec(v_toApplicative_1339_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1373_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v_cls_1352_; lean_object* v___f_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1362_; 
v___x_1350_ = lean_box(v_nondep_1300_);
lean_inc(v_toBind_1297_);
lean_inc_ref(v_e_1316_);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1351_, 0, v_toApplicative_1291_);
lean_closure_set(v___f_1351_, 1, v_e_1316_);
lean_closure_set(v___f_1351_, 2, v_xs_1299_);
lean_closure_set(v___f_1351_, 3, v_h_1317_);
lean_closure_set(v___f_1351_, 4, v___x_1350_);
lean_closure_set(v___f_1351_, 5, v_toBind_1297_);
lean_closure_set(v___f_1351_, 6, v___f_1301_);
v_cls_1352_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1353_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1354_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1343_);
v___f_1355_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1355_, 0, v_toFunctor_1343_);
v___f_1356_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1356_, 0, v_toFunctor_1343_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___f_1355_);
lean_ctor_set(v___x_1357_, 1, v___f_1356_);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1358_, 0, v_toSeqRight_1346_);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1359_, 0, v_toSeqLeft_1345_);
v___f_1360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1360_, 0, v_toSeq_1344_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___f_1358_);
lean_ctor_set(v___x_1348_, 3, v___f_1359_);
lean_ctor_set(v___x_1348_, 2, v___f_1360_);
lean_ctor_set(v___x_1348_, 1, v___f_1353_);
lean_ctor_set(v___x_1348_, 0, v___x_1357_);
v___x_1362_ = v___x_1348_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___f_1353_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___f_1360_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v___f_1359_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v___f_1358_);
v___x_1362_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___f_1354_);
lean_ctor_set(v___x_1341_, 0, v___x_1362_);
v___x_1364_ = v___x_1341_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___f_1354_);
v___x_1364_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___f_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___f_1365_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1366_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1367_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1368_, 0, v_cls_1352_);
lean_closure_set(v___f_1368_, 1, v___x_1366_);
lean_closure_set(v___f_1368_, 2, v___f_1365_);
lean_closure_set(v___f_1368_, 3, v_declName_1302_);
lean_closure_set(v___f_1368_, 4, v_val_1303_);
lean_closure_set(v___f_1368_, 5, v_e_1316_);
lean_closure_set(v___f_1368_, 6, v___x_1364_);
lean_closure_set(v___f_1368_, 7, v___x_1367_);
v___x_1369_ = lean_apply_2(v_inst_1304_, lean_box(0), v___f_1368_);
v___x_1370_ = lean_apply_4(v_toBind_1297_, lean_box(0), lean_box(0), v___x_1369_, v___f_1351_);
return v___x_1370_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object* v_toApplicative_1379_, lean_object* v_level_1380_, lean_object* v___x_1381_, lean_object* v_type_1382_, lean_object* v_value_1383_, lean_object* v___x_1384_, lean_object* v_toBind_1385_, lean_object* v___f_1386_, lean_object* v_xs_1387_, lean_object* v_nondep_1388_, lean_object* v___f_1389_, lean_object* v_declName_1390_, lean_object* v_val_1391_, lean_object* v_inst_1392_, lean_object* v_____do__lift_1393_){
_start:
{
uint8_t v___x_13109__boxed_1394_; uint8_t v_nondep_13111__boxed_1395_; lean_object* v_res_1396_; 
v___x_13109__boxed_1394_ = lean_unbox(v___x_1384_);
v_nondep_13111__boxed_1395_ = lean_unbox(v_nondep_1388_);
v_res_1396_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1379_, v_level_1380_, v___x_1381_, v_type_1382_, v_value_1383_, v___x_13109__boxed_1394_, v_toBind_1385_, v___f_1386_, v_xs_1387_, v_nondep_13111__boxed_1395_, v___f_1389_, v_declName_1390_, v_val_1391_, v_inst_1392_, v_____do__lift_1393_);
return v_res_1396_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1407_ = lean_unsigned_to_nat(8u);
v___x_1408_ = lean_unsigned_to_nat(287u);
v___x_1409_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1411_ = l_mkPanicMessageWithDecl(v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1412_, lean_object* v_type_1413_, lean_object* v_fst_1414_, lean_object* v___x_1415_, lean_object* v_value_1416_, uint8_t v_nondep_1417_, uint8_t v_fst_1418_, lean_object* v_toApplicative_1419_, lean_object* v___x_1420_, lean_object* v_us_1421_, lean_object* v_snd_1422_, lean_object* v_inst_1423_, lean_object* v_rb_1424_){
_start:
{
lean_object* v_expr_1425_; lean_object* v_exprType_1426_; lean_object* v_exprInit_1427_; lean_object* v_exprResult_1428_; lean_object* v_proof_1429_; uint8_t v_modified_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1481_; 
v_expr_1425_ = lean_ctor_get(v_rb_1424_, 0);
v_exprType_1426_ = lean_ctor_get(v_rb_1424_, 1);
v_exprInit_1427_ = lean_ctor_get(v_rb_1424_, 2);
v_exprResult_1428_ = lean_ctor_get(v_rb_1424_, 3);
v_proof_1429_ = lean_ctor_get(v_rb_1424_, 4);
v_modified_1430_ = lean_ctor_get_uint8(v_rb_1424_, sizeof(void*)*5);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_rb_1424_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1432_ = v_rb_1424_;
v_isShared_1433_ = v_isSharedCheck_1481_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_proof_1429_);
lean_inc(v_exprResult_1428_);
lean_inc(v_exprInit_1427_);
lean_inc(v_exprType_1426_);
lean_inc(v_expr_1425_);
lean_dec(v_rb_1424_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1481_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_expr_has_loose_bvar(v_exprType_1426_, v___x_1434_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v_expr_1438_; lean_object* v_exprType_1439_; lean_object* v___x_1440_; lean_object* v_exprInit_1441_; lean_object* v_exprResult_1442_; 
lean_dec_ref(v_inst_1423_);
v___x_1436_ = 0;
lean_inc_ref_n(v_type_1413_, 3);
lean_inc_n(v_declName_1412_, 3);
v___x_1437_ = l_Lean_mkLambda(v_declName_1412_, v___x_1436_, v_type_1413_, v_expr_1425_);
lean_inc_ref_n(v_fst_1414_, 2);
lean_inc_ref(v___x_1437_);
v_expr_1438_ = l_Lean_Expr_app___override(v___x_1437_, v_fst_1414_);
v_exprType_1439_ = lean_expr_lower_loose_bvars(v_exprType_1426_, v___x_1415_, v___x_1415_);
lean_dec_ref(v_exprType_1426_);
v___x_1440_ = l_Lean_mkLambda(v_declName_1412_, v___x_1436_, v_type_1413_, v_exprInit_1427_);
lean_inc_ref(v_value_1416_);
lean_inc_ref(v___x_1440_);
v_exprInit_1441_ = l_Lean_Expr_app___override(v___x_1440_, v_value_1416_);
v_exprResult_1442_ = l_Lean_Expr_letE___override(v_declName_1412_, v_type_1413_, v_fst_1414_, v_exprResult_1428_, v_nondep_1417_);
if (v_fst_1418_ == 0)
{
lean_dec_ref(v_snd_1422_);
lean_dec_ref(v_fst_1414_);
if (v_modified_1430_ == 0)
{
lean_object* v_toPure_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v_proof_1446_; lean_object* v___x_1448_; 
lean_dec_ref(v___x_1440_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v_proof_1429_);
lean_dec(v_us_1421_);
lean_dec_ref(v_value_1416_);
lean_dec_ref(v_type_1413_);
lean_dec(v_declName_1412_);
v_toPure_1443_ = lean_ctor_get(v_toApplicative_1419_, 1);
lean_inc(v_toPure_1443_);
lean_dec_ref(v_toApplicative_1419_);
v___x_1444_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1445_ = l_Lean_mkConst(v___x_1444_, v___x_1420_);
lean_inc_ref(v_expr_1438_);
lean_inc_ref(v_exprType_1439_);
v_proof_1446_ = l_Lean_mkAppB(v___x_1445_, v_exprType_1439_, v_expr_1438_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1446_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1442_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1441_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1439_);
lean_ctor_set(v___x_1432_, 0, v_expr_1438_);
v___x_1448_ = v___x_1432_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_expr_1438_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_exprType_1439_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_exprInit_1441_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_exprResult_1442_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_proof_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1450_, sizeof(void*)*5, v_modified_1430_);
v___x_1448_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_apply_2(v_toPure_1443_, lean_box(0), v___x_1448_);
return v___x_1449_;
}
}
else
{
lean_object* v_toPure_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_proof_1455_; lean_object* v___x_1457_; 
lean_dec(v___x_1420_);
v_toPure_1451_ = lean_ctor_get(v_toApplicative_1419_, 1);
lean_inc(v_toPure_1451_);
lean_dec_ref(v_toApplicative_1419_);
lean_inc_ref(v_type_1413_);
v___x_1452_ = l_Lean_mkLambda(v_declName_1412_, v___x_1436_, v_type_1413_, v_proof_1429_);
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1454_ = l_Lean_mkConst(v___x_1453_, v_us_1421_);
lean_inc_ref(v_exprType_1439_);
v_proof_1455_ = l_Lean_mkApp6(v___x_1454_, v_type_1413_, v_exprType_1439_, v_value_1416_, v___x_1440_, v___x_1437_, v___x_1452_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1455_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1442_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1441_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1439_);
lean_ctor_set(v___x_1432_, 0, v_expr_1438_);
v___x_1457_ = v___x_1432_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_expr_1438_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_exprType_1439_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_exprInit_1441_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_exprResult_1442_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_proof_1455_);
v___x_1457_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*5, v_nondep_1417_);
v___x_1458_ = lean_apply_2(v_toPure_1451_, lean_box(0), v___x_1457_);
return v___x_1458_;
}
}
}
else
{
lean_dec(v___x_1420_);
if (v_modified_1430_ == 0)
{
lean_object* v_toPure_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_proof_1463_; lean_object* v___x_1465_; 
lean_dec_ref(v___x_1437_);
lean_dec_ref(v_proof_1429_);
lean_dec(v_declName_1412_);
v_toPure_1460_ = lean_ctor_get(v_toApplicative_1419_, 1);
lean_inc(v_toPure_1460_);
lean_dec_ref(v_toApplicative_1419_);
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1462_ = l_Lean_mkConst(v___x_1461_, v_us_1421_);
lean_inc_ref(v_exprType_1439_);
v_proof_1463_ = l_Lean_mkApp6(v___x_1462_, v_type_1413_, v_exprType_1439_, v_value_1416_, v_fst_1414_, v___x_1440_, v_snd_1422_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1463_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1442_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1441_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1439_);
lean_ctor_set(v___x_1432_, 0, v_expr_1438_);
v___x_1465_ = v___x_1432_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_expr_1438_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_exprType_1439_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_exprInit_1441_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_exprResult_1442_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_proof_1463_);
v___x_1465_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*5, v_nondep_1417_);
v___x_1466_ = lean_apply_2(v_toPure_1460_, lean_box(0), v___x_1465_);
return v___x_1466_;
}
}
else
{
lean_object* v_toPure_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_proof_1472_; lean_object* v___x_1474_; 
v_toPure_1468_ = lean_ctor_get(v_toApplicative_1419_, 1);
lean_inc(v_toPure_1468_);
lean_dec_ref(v_toApplicative_1419_);
lean_inc_ref(v_type_1413_);
v___x_1469_ = l_Lean_mkLambda(v_declName_1412_, v___x_1436_, v_type_1413_, v_proof_1429_);
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1471_ = l_Lean_mkConst(v___x_1470_, v_us_1421_);
lean_inc_ref(v_exprType_1439_);
v_proof_1472_ = l_Lean_mkApp8(v___x_1471_, v_type_1413_, v_exprType_1439_, v_value_1416_, v_fst_1414_, v___x_1440_, v___x_1437_, v_snd_1422_, v___x_1469_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1472_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1442_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1441_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1439_);
lean_ctor_set(v___x_1432_, 0, v_expr_1438_);
v___x_1474_ = v___x_1432_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_expr_1438_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_exprType_1439_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_exprInit_1441_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_exprResult_1442_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_proof_1472_);
v___x_1474_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; 
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*5, v_nondep_1417_);
v___x_1475_ = lean_apply_2(v_toPure_1468_, lean_box(0), v___x_1474_);
return v___x_1475_;
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_del_object(v___x_1432_);
lean_dec_ref(v_proof_1429_);
lean_dec_ref(v_exprResult_1428_);
lean_dec_ref(v_exprInit_1427_);
lean_dec_ref(v_exprType_1426_);
lean_dec_ref(v_expr_1425_);
lean_dec_ref(v_snd_1422_);
lean_dec(v_us_1421_);
lean_dec(v___x_1420_);
lean_dec_ref(v_toApplicative_1419_);
lean_dec_ref(v_value_1416_);
lean_dec_ref(v_fst_1414_);
lean_dec_ref(v_type_1413_);
lean_dec(v_declName_1412_);
v___x_1477_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1478_ = l_instInhabitedOfMonad___redArg(v_inst_1423_, v___x_1477_);
v___x_1479_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1480_ = l_panic___redArg(v___x_1478_, v___x_1479_);
lean_dec(v___x_1478_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1482_, lean_object* v_type_1483_, lean_object* v_fst_1484_, lean_object* v___x_1485_, lean_object* v_value_1486_, lean_object* v_nondep_1487_, lean_object* v_fst_1488_, lean_object* v_toApplicative_1489_, lean_object* v___x_1490_, lean_object* v_us_1491_, lean_object* v_snd_1492_, lean_object* v_inst_1493_, lean_object* v_rb_1494_){
_start:
{
uint8_t v_nondep_13327__boxed_1495_; uint8_t v_fst_13328__boxed_1496_; lean_object* v_res_1497_; 
v_nondep_13327__boxed_1495_ = lean_unbox(v_nondep_1487_);
v_fst_13328__boxed_1496_ = lean_unbox(v_fst_1488_);
v_res_1497_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1482_, v_type_1483_, v_fst_1484_, v___x_1485_, v_value_1486_, v_nondep_13327__boxed_1495_, v_fst_13328__boxed_1496_, v_toApplicative_1489_, v___x_1490_, v_us_1491_, v_snd_1492_, v_inst_1493_, v_rb_1494_);
lean_dec(v___x_1485_);
return v_res_1497_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0));
v___x_1503_ = lean_unsigned_to_nat(34u);
v___x_1504_ = lean_unsigned_to_nat(217u);
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1506_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1507_ = l_mkPanicMessageWithDecl(v___x_1506_, v___x_1505_, v___x_1504_, v___x_1503_, v___x_1502_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1508_, lean_object* v_type_1509_, lean_object* v_value_1510_, uint8_t v_nondep_1511_, lean_object* v_toApplicative_1512_, lean_object* v___x_1513_, lean_object* v_us_1514_, lean_object* v_decl_1515_, lean_object* v_x_1516_, lean_object* v_i_1517_, lean_object* v_xs_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_info_1523_, lean_object* v_fixed_1524_, lean_object* v_used_1525_, lean_object* v_body_1526_, lean_object* v_toBind_1527_, lean_object* v_withNewLemmas_1528_, lean_object* v_val_x27_1529_, lean_object* v_val_1530_, uint8_t v___x_1531_, lean_object* v_____r_1532_){
_start:
{
uint8_t v___y_1534_; lean_object* v___y_1535_; uint8_t v___y_1551_; uint8_t v___x_1553_; 
v___x_1553_ = lean_expr_eqv(v_val_1530_, v_val_x27_1529_);
if (v___x_1553_ == 0)
{
v___y_1551_ = v_nondep_1511_;
goto v___jp_1550_;
}
else
{
v___y_1551_ = v___x_1531_;
goto v___jp_1550_;
}
v___jp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___f_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1536_ = lean_box(v_nondep_1511_);
v___x_1537_ = lean_box(v___y_1534_);
v___f_1538_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1538_, 0, v_declName_1508_);
lean_closure_set(v___f_1538_, 1, v_type_1509_);
lean_closure_set(v___f_1538_, 2, v___y_1535_);
lean_closure_set(v___f_1538_, 3, v_value_1510_);
lean_closure_set(v___f_1538_, 4, v___x_1536_);
lean_closure_set(v___f_1538_, 5, v_toApplicative_1512_);
lean_closure_set(v___f_1538_, 6, v___x_1513_);
lean_closure_set(v___f_1538_, 7, v___x_1537_);
lean_closure_set(v___f_1538_, 8, v_us_1514_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_decl_1515_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_mk_empty_array_with_capacity(v___x_1541_);
lean_inc_ref(v_x_1516_);
v___x_1543_ = lean_array_push(v___x_1542_, v_x_1516_);
v___x_1544_ = lean_nat_add(v_i_1517_, v___x_1541_);
v___x_1545_ = lean_array_push(v_xs_1518_, v_x_1516_);
lean_inc_ref(v_inst_1521_);
lean_inc_ref(v_inst_1519_);
v___x_1546_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_info_1523_, v_fixed_1524_, v_used_1525_, v_body_1526_, v___x_1544_, v___x_1545_);
v___x_1547_ = lean_apply_4(v_toBind_1527_, lean_box(0), lean_box(0), v___x_1546_, v___f_1538_);
v___x_1548_ = lean_apply_3(v_withNewLemmas_1528_, lean_box(0), v___x_1543_, v___x_1547_);
v___x_1549_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1521_, v_inst_1519_, v___x_1540_, v___x_1548_);
return v___x_1549_;
}
v___jp_1550_:
{
if (v___y_1551_ == 0)
{
lean_inc_ref(v_value_1510_);
v___y_1534_ = v___y_1551_;
v___y_1535_ = v_value_1510_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_expr_abstract(v_val_x27_1529_, v_xs_1518_);
v___y_1534_ = v___y_1551_;
v___y_1535_ = v___x_1552_;
goto v___jp_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1554_ = _args[0];
lean_object* v_type_1555_ = _args[1];
lean_object* v_value_1556_ = _args[2];
lean_object* v_nondep_1557_ = _args[3];
lean_object* v_toApplicative_1558_ = _args[4];
lean_object* v___x_1559_ = _args[5];
lean_object* v_us_1560_ = _args[6];
lean_object* v_decl_1561_ = _args[7];
lean_object* v_x_1562_ = _args[8];
lean_object* v_i_1563_ = _args[9];
lean_object* v_xs_1564_ = _args[10];
lean_object* v_inst_1565_ = _args[11];
lean_object* v_inst_1566_ = _args[12];
lean_object* v_inst_1567_ = _args[13];
lean_object* v_inst_1568_ = _args[14];
lean_object* v_info_1569_ = _args[15];
lean_object* v_fixed_1570_ = _args[16];
lean_object* v_used_1571_ = _args[17];
lean_object* v_body_1572_ = _args[18];
lean_object* v_toBind_1573_ = _args[19];
lean_object* v_withNewLemmas_1574_ = _args[20];
lean_object* v_val_x27_1575_ = _args[21];
lean_object* v_val_1576_ = _args[22];
lean_object* v___x_1577_ = _args[23];
lean_object* v_____r_1578_ = _args[24];
_start:
{
uint8_t v_nondep_13583__boxed_1579_; uint8_t v___x_13590__boxed_1580_; lean_object* v_res_1581_; 
v_nondep_13583__boxed_1579_ = lean_unbox(v_nondep_1557_);
v___x_13590__boxed_1580_ = lean_unbox(v___x_1577_);
v_res_1581_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1554_, v_type_1555_, v_value_1556_, v_nondep_13583__boxed_1579_, v_toApplicative_1558_, v___x_1559_, v_us_1560_, v_decl_1561_, v_x_1562_, v_i_1563_, v_xs_1564_, v_inst_1565_, v_inst_1566_, v_inst_1567_, v_inst_1568_, v_info_1569_, v_fixed_1570_, v_used_1571_, v_body_1572_, v_toBind_1573_, v_withNewLemmas_1574_, v_val_x27_1575_, v_val_1576_, v___x_13590__boxed_1580_, v_____r_1578_);
lean_dec_ref(v_val_1576_);
lean_dec_ref(v_val_x27_1575_);
lean_dec(v_i_1563_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1582_, lean_object* v_type_1583_, lean_object* v_value_1584_, uint8_t v_nondep_1585_, lean_object* v_toApplicative_1586_, lean_object* v___x_1587_, lean_object* v_us_1588_, lean_object* v_decl_1589_, lean_object* v_x_1590_, lean_object* v_i_1591_, lean_object* v_xs_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_info_1597_, lean_object* v_fixed_1598_, lean_object* v_used_1599_, lean_object* v_body_1600_, lean_object* v_toBind_1601_, lean_object* v_withNewLemmas_1602_, lean_object* v_val_1603_, uint8_t v___x_1604_, lean_object* v_val_x27_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v_toApplicative_1607_; lean_object* v_toFunctor_1608_; lean_object* v_toSeq_1609_; lean_object* v_toSeqLeft_1610_; lean_object* v_toSeqRight_1611_; lean_object* v___f_1612_; lean_object* v___f_1613_; lean_object* v___f_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_toApplicative_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1660_; 
v___x_1606_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1607_ = lean_ctor_get(v___x_1606_, 0);
v_toFunctor_1608_ = lean_ctor_get(v_toApplicative_1607_, 0);
v_toSeq_1609_ = lean_ctor_get(v_toApplicative_1607_, 2);
v_toSeqLeft_1610_ = lean_ctor_get(v_toApplicative_1607_, 3);
v_toSeqRight_1611_ = lean_ctor_get(v_toApplicative_1607_, 4);
v___f_1612_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1613_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1608_, 2);
v___f_1614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1614_, 0, v_toFunctor_1608_);
v___f_1615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1615_, 0, v_toFunctor_1608_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___f_1614_);
lean_ctor_set(v___x_1616_, 1, v___f_1615_);
lean_inc(v_toSeqRight_1611_);
v___f_1617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1617_, 0, v_toSeqRight_1611_);
lean_inc(v_toSeqLeft_1610_);
v___f_1618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1618_, 0, v_toSeqLeft_1610_);
lean_inc(v_toSeq_1609_);
v___f_1619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1619_, 0, v_toSeq_1609_);
v___x_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v___f_1612_);
lean_ctor_set(v___x_1620_, 2, v___f_1619_);
lean_ctor_set(v___x_1620_, 3, v___f_1618_);
lean_ctor_set(v___x_1620_, 4, v___f_1617_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___f_1613_);
v___x_1622_ = l_StateRefT_x27_instMonad___redArg(v___x_1621_);
v_toApplicative_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v___x_1622_, 1);
lean_dec(v_unused_1661_);
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1660_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_toApplicative_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1660_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_toFunctor_1627_; lean_object* v_toSeq_1628_; lean_object* v_toSeqLeft_1629_; lean_object* v_toSeqRight_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1658_; 
v_toFunctor_1627_ = lean_ctor_get(v_toApplicative_1623_, 0);
v_toSeq_1628_ = lean_ctor_get(v_toApplicative_1623_, 2);
v_toSeqLeft_1629_ = lean_ctor_get(v_toApplicative_1623_, 3);
v_toSeqRight_1630_ = lean_ctor_get(v_toApplicative_1623_, 4);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_toApplicative_1623_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_toApplicative_1623_, 1);
lean_dec(v_unused_1659_);
v___x_1632_ = v_toApplicative_1623_;
v_isShared_1633_ = v_isSharedCheck_1658_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_toSeqRight_1630_);
lean_inc(v_toSeqLeft_1629_);
lean_inc(v_toSeq_1628_);
lean_inc(v_toFunctor_1627_);
lean_dec(v_toApplicative_1623_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1658_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___f_1636_; lean_object* v_cls_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___f_1643_; lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___x_1647_; 
v___x_1634_ = lean_box(v_nondep_1585_);
v___x_1635_ = lean_box(v___x_1604_);
lean_inc_ref(v_val_1603_);
lean_inc_ref(v_val_x27_1605_);
lean_inc(v_toBind_1601_);
lean_inc(v_inst_1594_);
lean_inc(v_declName_1582_);
v___f_1636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 25, 24);
lean_closure_set(v___f_1636_, 0, v_declName_1582_);
lean_closure_set(v___f_1636_, 1, v_type_1583_);
lean_closure_set(v___f_1636_, 2, v_value_1584_);
lean_closure_set(v___f_1636_, 3, v___x_1634_);
lean_closure_set(v___f_1636_, 4, v_toApplicative_1586_);
lean_closure_set(v___f_1636_, 5, v___x_1587_);
lean_closure_set(v___f_1636_, 6, v_us_1588_);
lean_closure_set(v___f_1636_, 7, v_decl_1589_);
lean_closure_set(v___f_1636_, 8, v_x_1590_);
lean_closure_set(v___f_1636_, 9, v_i_1591_);
lean_closure_set(v___f_1636_, 10, v_xs_1592_);
lean_closure_set(v___f_1636_, 11, v_inst_1593_);
lean_closure_set(v___f_1636_, 12, v_inst_1594_);
lean_closure_set(v___f_1636_, 13, v_inst_1595_);
lean_closure_set(v___f_1636_, 14, v_inst_1596_);
lean_closure_set(v___f_1636_, 15, v_info_1597_);
lean_closure_set(v___f_1636_, 16, v_fixed_1598_);
lean_closure_set(v___f_1636_, 17, v_used_1599_);
lean_closure_set(v___f_1636_, 18, v_body_1600_);
lean_closure_set(v___f_1636_, 19, v_toBind_1601_);
lean_closure_set(v___f_1636_, 20, v_withNewLemmas_1602_);
lean_closure_set(v___f_1636_, 21, v_val_x27_1605_);
lean_closure_set(v___f_1636_, 22, v_val_1603_);
lean_closure_set(v___f_1636_, 23, v___x_1635_);
v_cls_1637_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1638_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1639_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1627_);
v___f_1640_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1640_, 0, v_toFunctor_1627_);
v___f_1641_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1641_, 0, v_toFunctor_1627_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___f_1640_);
lean_ctor_set(v___x_1642_, 1, v___f_1641_);
v___f_1643_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1643_, 0, v_toSeqRight_1630_);
v___f_1644_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1644_, 0, v_toSeqLeft_1629_);
v___f_1645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1645_, 0, v_toSeq_1628_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 4, v___f_1643_);
lean_ctor_set(v___x_1632_, 3, v___f_1644_);
lean_ctor_set(v___x_1632_, 2, v___f_1645_);
lean_ctor_set(v___x_1632_, 1, v___f_1638_);
lean_ctor_set(v___x_1632_, 0, v___x_1642_);
v___x_1647_ = v___x_1632_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___f_1638_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v___f_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v___f_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v___f_1643_);
v___x_1647_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___f_1639_);
lean_ctor_set(v___x_1625_, 0, v___x_1647_);
v___x_1649_ = v___x_1625_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___f_1639_);
v___x_1649_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___f_1650_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1653_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1653_, 0, v_cls_1637_);
lean_closure_set(v___f_1653_, 1, v___x_1651_);
lean_closure_set(v___f_1653_, 2, v___f_1650_);
lean_closure_set(v___f_1653_, 3, v_declName_1582_);
lean_closure_set(v___f_1653_, 4, v_val_1603_);
lean_closure_set(v___f_1653_, 5, v_val_x27_1605_);
lean_closure_set(v___f_1653_, 6, v___x_1649_);
lean_closure_set(v___f_1653_, 7, v___x_1652_);
v___x_1654_ = lean_apply_2(v_inst_1594_, lean_box(0), v___f_1653_);
v___x_1655_ = lean_apply_4(v_toBind_1601_, lean_box(0), lean_box(0), v___x_1654_, v___f_1636_);
return v___x_1655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1662_ = _args[0];
lean_object* v_type_1663_ = _args[1];
lean_object* v_value_1664_ = _args[2];
lean_object* v_nondep_1665_ = _args[3];
lean_object* v_toApplicative_1666_ = _args[4];
lean_object* v___x_1667_ = _args[5];
lean_object* v_us_1668_ = _args[6];
lean_object* v_decl_1669_ = _args[7];
lean_object* v_x_1670_ = _args[8];
lean_object* v_i_1671_ = _args[9];
lean_object* v_xs_1672_ = _args[10];
lean_object* v_inst_1673_ = _args[11];
lean_object* v_inst_1674_ = _args[12];
lean_object* v_inst_1675_ = _args[13];
lean_object* v_inst_1676_ = _args[14];
lean_object* v_info_1677_ = _args[15];
lean_object* v_fixed_1678_ = _args[16];
lean_object* v_used_1679_ = _args[17];
lean_object* v_body_1680_ = _args[18];
lean_object* v_toBind_1681_ = _args[19];
lean_object* v_withNewLemmas_1682_ = _args[20];
lean_object* v_val_1683_ = _args[21];
lean_object* v___x_1684_ = _args[22];
lean_object* v_val_x27_1685_ = _args[23];
_start:
{
uint8_t v_nondep_13614__boxed_1686_; uint8_t v___x_13621__boxed_1687_; lean_object* v_res_1688_; 
v_nondep_13614__boxed_1686_ = lean_unbox(v_nondep_1665_);
v___x_13621__boxed_1687_ = lean_unbox(v___x_1684_);
v_res_1688_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1662_, v_type_1663_, v_value_1664_, v_nondep_13614__boxed_1686_, v_toApplicative_1666_, v___x_1667_, v_us_1668_, v_decl_1669_, v_x_1670_, v_i_1671_, v_xs_1672_, v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_info_1677_, v_fixed_1678_, v_used_1679_, v_body_1680_, v_toBind_1681_, v_withNewLemmas_1682_, v_val_1683_, v___x_13621__boxed_1687_, v_val_x27_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1689_, lean_object* v_declName_1690_, lean_object* v_type_1691_, lean_object* v_value_1692_, uint8_t v_nondep_1693_, lean_object* v_toApplicative_1694_, lean_object* v___x_1695_, lean_object* v_us_1696_, lean_object* v_inst_1697_, lean_object* v_x_1698_, lean_object* v_i_1699_, lean_object* v_xs_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_info_1704_, lean_object* v_fixed_1705_, lean_object* v_used_1706_, lean_object* v_body_1707_, lean_object* v_toBind_1708_, lean_object* v_withNewLemmas_1709_, lean_object* v_____x_1710_){
_start:
{
lean_object* v_snd_1711_; lean_object* v_fst_1712_; lean_object* v_fst_1713_; lean_object* v_snd_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1733_; 
v_snd_1711_ = lean_ctor_get(v_____x_1710_, 1);
lean_inc(v_snd_1711_);
v_fst_1712_ = lean_ctor_get(v_____x_1710_, 0);
lean_inc(v_fst_1712_);
lean_dec_ref(v_____x_1710_);
v_fst_1713_ = lean_ctor_get(v_snd_1711_, 0);
v_snd_1714_ = lean_ctor_get(v_snd_1711_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_snd_1711_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1716_ = v_snd_1711_;
v_isShared_1717_ = v_isSharedCheck_1733_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_snd_1714_);
lean_inc(v_fst_1713_);
lean_dec(v_snd_1711_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1733_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_box(0);
if (v_isShared_1717_ == 0)
{
lean_ctor_set_tag(v___x_1716_, 1);
lean_ctor_set(v___x_1716_, 1, v___x_1718_);
lean_ctor_set(v___x_1716_, 0, v_decl_1689_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_decl_1689_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_box(v_nondep_1693_);
lean_inc_ref_n(v_inst_1697_, 2);
v___f_1723_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1723_, 0, v_declName_1690_);
lean_closure_set(v___f_1723_, 1, v_type_1691_);
lean_closure_set(v___f_1723_, 2, v_fst_1712_);
lean_closure_set(v___f_1723_, 3, v___x_1721_);
lean_closure_set(v___f_1723_, 4, v_value_1692_);
lean_closure_set(v___f_1723_, 5, v___x_1722_);
lean_closure_set(v___f_1723_, 6, v_fst_1713_);
lean_closure_set(v___f_1723_, 7, v_toApplicative_1694_);
lean_closure_set(v___f_1723_, 8, v___x_1695_);
lean_closure_set(v___f_1723_, 9, v_us_1696_);
lean_closure_set(v___f_1723_, 10, v_snd_1714_);
lean_closure_set(v___f_1723_, 11, v_inst_1697_);
v___x_1724_ = lean_mk_empty_array_with_capacity(v___x_1721_);
lean_inc_ref(v_x_1698_);
v___x_1725_ = lean_array_push(v___x_1724_, v_x_1698_);
v___x_1726_ = lean_nat_add(v_i_1699_, v___x_1721_);
v___x_1727_ = lean_array_push(v_xs_1700_, v_x_1698_);
lean_inc_ref(v_inst_1702_);
v___x_1728_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1697_, v_inst_1701_, v_inst_1702_, v_inst_1703_, v_info_1704_, v_fixed_1705_, v_used_1706_, v_body_1707_, v___x_1726_, v___x_1727_);
v___x_1729_ = lean_apply_4(v_toBind_1708_, lean_box(0), lean_box(0), v___x_1728_, v___f_1723_);
v___x_1730_ = lean_apply_3(v_withNewLemmas_1709_, lean_box(0), v___x_1725_, v___x_1729_);
v___x_1731_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1702_, v_inst_1697_, v___x_1720_, v___x_1730_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1734_ = _args[0];
lean_object* v_declName_1735_ = _args[1];
lean_object* v_type_1736_ = _args[2];
lean_object* v_value_1737_ = _args[3];
lean_object* v_nondep_1738_ = _args[4];
lean_object* v_toApplicative_1739_ = _args[5];
lean_object* v___x_1740_ = _args[6];
lean_object* v_us_1741_ = _args[7];
lean_object* v_inst_1742_ = _args[8];
lean_object* v_x_1743_ = _args[9];
lean_object* v_i_1744_ = _args[10];
lean_object* v_xs_1745_ = _args[11];
lean_object* v_inst_1746_ = _args[12];
lean_object* v_inst_1747_ = _args[13];
lean_object* v_inst_1748_ = _args[14];
lean_object* v_info_1749_ = _args[15];
lean_object* v_fixed_1750_ = _args[16];
lean_object* v_used_1751_ = _args[17];
lean_object* v_body_1752_ = _args[18];
lean_object* v_toBind_1753_ = _args[19];
lean_object* v_withNewLemmas_1754_ = _args[20];
lean_object* v_____x_1755_ = _args[21];
_start:
{
uint8_t v_nondep_13556__boxed_1756_; lean_object* v_res_1757_; 
v_nondep_13556__boxed_1756_ = lean_unbox(v_nondep_1738_);
v_res_1757_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1734_, v_declName_1735_, v_type_1736_, v_value_1737_, v_nondep_13556__boxed_1756_, v_toApplicative_1739_, v___x_1740_, v_us_1741_, v_inst_1742_, v_x_1743_, v_i_1744_, v_xs_1745_, v_inst_1746_, v_inst_1747_, v_inst_1748_, v_info_1749_, v_fixed_1750_, v_used_1751_, v_body_1752_, v_toBind_1753_, v_withNewLemmas_1754_, v_____x_1755_);
lean_dec(v_i_1744_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1758_ = _args[0];
lean_object* v_declName_1759_ = _args[1];
lean_object* v_type_1760_ = _args[2];
lean_object* v_value_1761_ = _args[3];
lean_object* v_us_1762_ = _args[4];
lean_object* v___x_1763_ = _args[5];
lean_object* v_toApplicative_1764_ = _args[6];
lean_object* v_nondep_1765_ = _args[7];
lean_object* v_i_1766_ = _args[8];
lean_object* v_xs_1767_ = _args[9];
lean_object* v_inst_1768_ = _args[10];
lean_object* v_inst_1769_ = _args[11];
lean_object* v_inst_1770_ = _args[12];
lean_object* v_inst_1771_ = _args[13];
lean_object* v_info_1772_ = _args[14];
lean_object* v_fixed_1773_ = _args[15];
lean_object* v_used_1774_ = _args[16];
lean_object* v_body_1775_ = _args[17];
lean_object* v_toBind_1776_ = _args[18];
lean_object* v_____r_1777_ = _args[19];
_start:
{
uint8_t v_nondep_13539__boxed_1778_; lean_object* v_res_1779_; 
v_nondep_13539__boxed_1778_ = lean_unbox(v_nondep_1765_);
v_res_1779_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1758_, v_declName_1759_, v_type_1760_, v_value_1761_, v_us_1762_, v___x_1763_, v_toApplicative_1764_, v_nondep_13539__boxed_1778_, v_i_1766_, v_xs_1767_, v_inst_1768_, v_inst_1769_, v_inst_1770_, v_inst_1771_, v_info_1772_, v_fixed_1773_, v_used_1774_, v_body_1775_, v_toBind_1776_, v_____r_1777_);
lean_dec(v_i_1766_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_info_1784_, lean_object* v_fixed_1785_, lean_object* v_used_1786_, lean_object* v_e_1787_, lean_object* v_i_1788_, lean_object* v_xs_1789_){
_start:
{
lean_object* v_haveInfo_1795_; lean_object* v_body_1796_; lean_object* v_bodyType_1797_; lean_object* v_level_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_haveInfo_1795_ = lean_ctor_get(v_info_1784_, 0);
v_body_1796_ = lean_ctor_get(v_info_1784_, 3);
v_bodyType_1797_ = lean_ctor_get(v_info_1784_, 4);
v_level_1798_ = lean_ctor_get(v_info_1784_, 5);
v___x_1799_ = lean_array_get_size(v_haveInfo_1795_);
v___x_1800_ = lean_nat_dec_lt(v_i_1788_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v_toApplicative_1801_; lean_object* v_toBind_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1863_; 
lean_inc(v_level_1798_);
lean_inc_ref(v_bodyType_1797_);
lean_inc_ref(v_body_1796_);
lean_dec(v_i_1788_);
lean_dec_ref(v_used_1786_);
lean_dec_ref(v_fixed_1785_);
lean_dec_ref(v_info_1784_);
lean_dec_ref(v_inst_1782_);
v_toApplicative_1801_ = lean_ctor_get(v_inst_1780_, 0);
v_toBind_1802_ = lean_ctor_get(v_inst_1780_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_inst_1780_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1804_ = v_inst_1780_;
v_isShared_1805_ = v_isSharedCheck_1863_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_toBind_1802_);
lean_inc(v_toApplicative_1801_);
lean_dec(v_inst_1780_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1863_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v_toApplicative_1807_; lean_object* v_toFunctor_1808_; lean_object* v_toSeq_1809_; lean_object* v_toSeqLeft_1810_; lean_object* v_toSeqRight_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1807_ = lean_ctor_get(v___x_1806_, 0);
v_toFunctor_1808_ = lean_ctor_get(v_toApplicative_1807_, 0);
v_toSeq_1809_ = lean_ctor_get(v_toApplicative_1807_, 2);
v_toSeqLeft_1810_ = lean_ctor_get(v_toApplicative_1807_, 3);
v_toSeqRight_1811_ = lean_ctor_get(v_toApplicative_1807_, 4);
v___f_1812_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1813_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1808_, 2);
v___f_1814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1814_, 0, v_toFunctor_1808_);
v___f_1815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1815_, 0, v_toFunctor_1808_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___f_1814_);
lean_ctor_set(v___x_1816_, 1, v___f_1815_);
lean_inc(v_toSeqRight_1811_);
v___f_1817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1817_, 0, v_toSeqRight_1811_);
lean_inc(v_toSeqLeft_1810_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeqLeft_1810_);
lean_inc(v_toSeq_1809_);
v___f_1819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1819_, 0, v_toSeq_1809_);
v___x_1820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1816_);
lean_ctor_set(v___x_1820_, 1, v___f_1812_);
lean_ctor_set(v___x_1820_, 2, v___f_1819_);
lean_ctor_set(v___x_1820_, 3, v___f_1818_);
lean_ctor_set(v___x_1820_, 4, v___f_1817_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___f_1813_);
lean_ctor_set(v___x_1804_, 0, v___x_1820_);
v___x_1822_ = v___x_1804_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___f_1813_);
v___x_1822_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v_toApplicative_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1860_; 
v___x_1823_ = l_StateRefT_x27_instMonad___redArg(v___x_1822_);
v_toApplicative_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1823_, 1);
lean_dec(v_unused_1861_);
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1860_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_toApplicative_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1860_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_toFunctor_1828_; lean_object* v_toSeq_1829_; lean_object* v_toSeqLeft_1830_; lean_object* v_toSeqRight_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1858_; 
v_toFunctor_1828_ = lean_ctor_get(v_toApplicative_1824_, 0);
v_toSeq_1829_ = lean_ctor_get(v_toApplicative_1824_, 2);
v_toSeqLeft_1830_ = lean_ctor_get(v_toApplicative_1824_, 3);
v_toSeqRight_1831_ = lean_ctor_get(v_toApplicative_1824_, 4);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_toApplicative_1824_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_toApplicative_1824_, 1);
lean_dec(v_unused_1859_);
v___x_1833_ = v_toApplicative_1824_;
v_isShared_1834_ = v_isSharedCheck_1858_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_toSeqRight_1831_);
lean_inc(v_toSeqLeft_1830_);
lean_inc(v_toSeq_1829_);
lean_inc(v_toFunctor_1828_);
lean_dec(v_toApplicative_1824_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1858_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___f_1836_; lean_object* v_cls_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___x_1847_; 
v___x_1835_ = lean_box(v___x_1800_);
lean_inc(v_toBind_1802_);
lean_inc_ref(v_body_1796_);
v___f_1836_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1836_, 0, v_inst_1783_);
lean_closure_set(v___f_1836_, 1, v_bodyType_1797_);
lean_closure_set(v___f_1836_, 2, v_xs_1789_);
lean_closure_set(v___f_1836_, 3, v_toApplicative_1801_);
lean_closure_set(v___f_1836_, 4, v_level_1798_);
lean_closure_set(v___f_1836_, 5, v_e_1787_);
lean_closure_set(v___f_1836_, 6, v___x_1835_);
lean_closure_set(v___f_1836_, 7, v_body_1796_);
lean_closure_set(v___f_1836_, 8, v_toBind_1802_);
v_cls_1837_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1838_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1839_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1828_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toFunctor_1828_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toFunctor_1828_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___f_1840_);
lean_ctor_set(v___x_1842_, 1, v___f_1841_);
v___f_1843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1843_, 0, v_toSeqRight_1831_);
v___f_1844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1844_, 0, v_toSeqLeft_1830_);
v___f_1845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1845_, 0, v_toSeq_1829_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v___f_1843_);
lean_ctor_set(v___x_1833_, 3, v___f_1844_);
lean_ctor_set(v___x_1833_, 2, v___f_1845_);
lean_ctor_set(v___x_1833_, 1, v___f_1838_);
lean_ctor_set(v___x_1833_, 0, v___x_1842_);
v___x_1847_ = v___x_1833_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___f_1838_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v___f_1845_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v___f_1844_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___f_1843_);
v___x_1847_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___f_1839_);
lean_ctor_set(v___x_1826_, 0, v___x_1847_);
v___x_1849_ = v___x_1826_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___f_1839_);
v___x_1849_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___f_1850_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1851_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1852_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1853_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1853_, 0, v_cls_1837_);
lean_closure_set(v___f_1853_, 1, v___x_1851_);
lean_closure_set(v___f_1853_, 2, v___f_1850_);
lean_closure_set(v___f_1853_, 3, v_body_1796_);
lean_closure_set(v___f_1853_, 4, v___x_1849_);
lean_closure_set(v___f_1853_, 5, v___x_1852_);
v___x_1854_ = lean_apply_2(v_inst_1781_, lean_box(0), v___f_1853_);
v___x_1855_ = lean_apply_4(v_toBind_1802_, lean_box(0), lean_box(0), v___x_1854_, v___f_1836_);
return v___x_1855_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_e_1787_) == 8)
{
uint8_t v_nondep_1864_; 
v_nondep_1864_ = lean_ctor_get_uint8(v_e_1787_, sizeof(void*)*4 + 8);
if (v_nondep_1864_ == 1)
{
lean_object* v_declName_1865_; lean_object* v_type_1866_; lean_object* v_value_1867_; lean_object* v_body_1868_; lean_object* v_hinfo_1869_; lean_object* v_decl_1870_; lean_object* v_level_1871_; lean_object* v_x_1872_; lean_object* v_val_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_us_1876_; uint8_t v___y_1878_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v_declName_1865_ = lean_ctor_get(v_e_1787_, 0);
lean_inc(v_declName_1865_);
v_type_1866_ = lean_ctor_get(v_e_1787_, 1);
lean_inc_ref(v_type_1866_);
v_value_1867_ = lean_ctor_get(v_e_1787_, 2);
lean_inc_ref(v_value_1867_);
v_body_1868_ = lean_ctor_get(v_e_1787_, 3);
lean_inc_ref(v_body_1868_);
lean_dec_ref(v_e_1787_);
v_hinfo_1869_ = lean_array_fget_borrowed(v_haveInfo_1795_, v_i_1788_);
v_decl_1870_ = lean_ctor_get(v_hinfo_1869_, 2);
v_level_1871_ = lean_ctor_get(v_hinfo_1869_, 3);
lean_inc_ref(v_decl_1870_);
v_x_1872_ = l_Lean_LocalDecl_toExpr(v_decl_1870_);
v_val_1873_ = l_Lean_LocalDecl_value(v_decl_1870_, v_nondep_1864_);
v___x_1874_ = lean_box(0);
lean_inc(v_level_1798_);
v___x_1875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_level_1798_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_inc_ref(v___x_1875_);
lean_inc(v_level_1871_);
v_us_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1876_, 0, v_level_1871_);
lean_ctor_set(v_us_1876_, 1, v___x_1875_);
v___x_1905_ = lean_array_get_size(v_used_1786_);
v___x_1906_ = lean_nat_dec_lt(v_i_1788_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_inc_ref(v_decl_1870_);
goto v___jp_1888_;
}
else
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = lean_array_fget_borrowed(v_used_1786_, v_i_1788_);
v___x_1908_ = lean_unbox(v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v_toApplicative_1909_; lean_object* v_toBind_1910_; lean_object* v___x_1911_; lean_object* v_toApplicative_1912_; lean_object* v_toFunctor_1913_; lean_object* v_toSeq_1914_; lean_object* v_toSeqLeft_1915_; lean_object* v_toSeqRight_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___f_1920_; lean_object* v___x_1921_; lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_toApplicative_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_x_1872_);
v_toApplicative_1909_ = lean_ctor_get(v_inst_1780_, 0);
lean_inc_ref(v_toApplicative_1909_);
v_toBind_1910_ = lean_ctor_get(v_inst_1780_, 1);
lean_inc(v_toBind_1910_);
v___x_1911_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1912_ = lean_ctor_get(v___x_1911_, 0);
v_toFunctor_1913_ = lean_ctor_get(v_toApplicative_1912_, 0);
v_toSeq_1914_ = lean_ctor_get(v_toApplicative_1912_, 2);
v_toSeqLeft_1915_ = lean_ctor_get(v_toApplicative_1912_, 3);
v_toSeqRight_1916_ = lean_ctor_get(v_toApplicative_1912_, 4);
v___f_1917_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1918_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1913_, 2);
v___f_1919_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1919_, 0, v_toFunctor_1913_);
v___f_1920_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1920_, 0, v_toFunctor_1913_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___f_1919_);
lean_ctor_set(v___x_1921_, 1, v___f_1920_);
lean_inc(v_toSeqRight_1916_);
v___f_1922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1922_, 0, v_toSeqRight_1916_);
lean_inc(v_toSeqLeft_1915_);
v___f_1923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1923_, 0, v_toSeqLeft_1915_);
lean_inc(v_toSeq_1914_);
v___f_1924_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1924_, 0, v_toSeq_1914_);
v___x_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1921_);
lean_ctor_set(v___x_1925_, 1, v___f_1917_);
lean_ctor_set(v___x_1925_, 2, v___f_1924_);
lean_ctor_set(v___x_1925_, 3, v___f_1923_);
lean_ctor_set(v___x_1925_, 4, v___f_1922_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___f_1918_);
v___x_1927_ = l_StateRefT_x27_instMonad___redArg(v___x_1926_);
v_toApplicative_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v___x_1927_, 1);
lean_dec(v_unused_1965_);
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1964_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_toApplicative_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1964_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_toFunctor_1932_; lean_object* v_toSeq_1933_; lean_object* v_toSeqLeft_1934_; lean_object* v_toSeqRight_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1962_; 
v_toFunctor_1932_ = lean_ctor_get(v_toApplicative_1928_, 0);
v_toSeq_1933_ = lean_ctor_get(v_toApplicative_1928_, 2);
v_toSeqLeft_1934_ = lean_ctor_get(v_toApplicative_1928_, 3);
v_toSeqRight_1935_ = lean_ctor_get(v_toApplicative_1928_, 4);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_toApplicative_1928_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_toApplicative_1928_, 1);
lean_dec(v_unused_1963_);
v___x_1937_ = v_toApplicative_1928_;
v_isShared_1938_ = v_isSharedCheck_1962_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_toSeqRight_1935_);
lean_inc(v_toSeqLeft_1934_);
lean_inc(v_toSeq_1933_);
lean_inc(v_toFunctor_1932_);
lean_dec(v_toApplicative_1928_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1962_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___f_1940_; lean_object* v_cls_1941_; lean_object* v___f_1942_; lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___x_1951_; 
v___x_1939_ = lean_box(v_nondep_1864_);
lean_inc(v_toBind_1910_);
lean_inc(v_inst_1781_);
lean_inc(v_declName_1865_);
v___f_1940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1940_, 0, v___x_1874_);
lean_closure_set(v___f_1940_, 1, v_declName_1865_);
lean_closure_set(v___f_1940_, 2, v_type_1866_);
lean_closure_set(v___f_1940_, 3, v_value_1867_);
lean_closure_set(v___f_1940_, 4, v_us_1876_);
lean_closure_set(v___f_1940_, 5, v___x_1875_);
lean_closure_set(v___f_1940_, 6, v_toApplicative_1909_);
lean_closure_set(v___f_1940_, 7, v___x_1939_);
lean_closure_set(v___f_1940_, 8, v_i_1788_);
lean_closure_set(v___f_1940_, 9, v_xs_1789_);
lean_closure_set(v___f_1940_, 10, v_inst_1780_);
lean_closure_set(v___f_1940_, 11, v_inst_1781_);
lean_closure_set(v___f_1940_, 12, v_inst_1782_);
lean_closure_set(v___f_1940_, 13, v_inst_1783_);
lean_closure_set(v___f_1940_, 14, v_info_1784_);
lean_closure_set(v___f_1940_, 15, v_fixed_1785_);
lean_closure_set(v___f_1940_, 16, v_used_1786_);
lean_closure_set(v___f_1940_, 17, v_body_1868_);
lean_closure_set(v___f_1940_, 18, v_toBind_1910_);
v_cls_1941_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1942_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1943_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1932_);
v___f_1944_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1944_, 0, v_toFunctor_1932_);
v___f_1945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1945_, 0, v_toFunctor_1932_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___f_1944_);
lean_ctor_set(v___x_1946_, 1, v___f_1945_);
v___f_1947_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1947_, 0, v_toSeqRight_1935_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toSeqLeft_1934_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toSeq_1933_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 4, v___f_1947_);
lean_ctor_set(v___x_1937_, 3, v___f_1948_);
lean_ctor_set(v___x_1937_, 2, v___f_1949_);
lean_ctor_set(v___x_1937_, 1, v___f_1942_);
lean_ctor_set(v___x_1937_, 0, v___x_1946_);
v___x_1951_ = v___x_1937_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___f_1942_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v___f_1949_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v___f_1948_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v___f_1947_);
v___x_1951_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___f_1943_);
lean_ctor_set(v___x_1930_, 0, v___x_1951_);
v___x_1953_ = v___x_1930_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___f_1943_);
v___x_1953_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___f_1954_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1956_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1957_, 0, v_cls_1941_);
lean_closure_set(v___f_1957_, 1, v___x_1955_);
lean_closure_set(v___f_1957_, 2, v___f_1954_);
lean_closure_set(v___f_1957_, 3, v_declName_1865_);
lean_closure_set(v___f_1957_, 4, v_val_1873_);
lean_closure_set(v___f_1957_, 5, v___x_1953_);
lean_closure_set(v___f_1957_, 6, v___x_1956_);
v___x_1958_ = lean_apply_2(v_inst_1781_, lean_box(0), v___f_1957_);
v___x_1959_ = lean_apply_4(v_toBind_1910_, lean_box(0), lean_box(0), v___x_1958_, v___f_1940_);
return v___x_1959_;
}
}
}
}
}
else
{
lean_inc_ref(v_decl_1870_);
goto v___jp_1888_;
}
}
v___jp_1877_:
{
lean_object* v_toApplicative_1879_; lean_object* v_toBind_1880_; lean_object* v_withNewLemmas_1881_; lean_object* v_dsimp_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_toApplicative_1879_ = lean_ctor_get(v_inst_1780_, 0);
lean_inc_ref(v_toApplicative_1879_);
v_toBind_1880_ = lean_ctor_get(v_inst_1780_, 1);
lean_inc_n(v_toBind_1880_, 2);
v_withNewLemmas_1881_ = lean_ctor_get(v_inst_1783_, 0);
lean_inc(v_withNewLemmas_1881_);
v_dsimp_1882_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc(v_dsimp_1882_);
v___x_1883_ = lean_box(v_nondep_1864_);
v___x_1884_ = lean_box(v___y_1878_);
lean_inc_ref(v_val_1873_);
v___f_1885_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 24, 23);
lean_closure_set(v___f_1885_, 0, v_declName_1865_);
lean_closure_set(v___f_1885_, 1, v_type_1866_);
lean_closure_set(v___f_1885_, 2, v_value_1867_);
lean_closure_set(v___f_1885_, 3, v___x_1883_);
lean_closure_set(v___f_1885_, 4, v_toApplicative_1879_);
lean_closure_set(v___f_1885_, 5, v___x_1875_);
lean_closure_set(v___f_1885_, 6, v_us_1876_);
lean_closure_set(v___f_1885_, 7, v_decl_1870_);
lean_closure_set(v___f_1885_, 8, v_x_1872_);
lean_closure_set(v___f_1885_, 9, v_i_1788_);
lean_closure_set(v___f_1885_, 10, v_xs_1789_);
lean_closure_set(v___f_1885_, 11, v_inst_1780_);
lean_closure_set(v___f_1885_, 12, v_inst_1781_);
lean_closure_set(v___f_1885_, 13, v_inst_1782_);
lean_closure_set(v___f_1885_, 14, v_inst_1783_);
lean_closure_set(v___f_1885_, 15, v_info_1784_);
lean_closure_set(v___f_1885_, 16, v_fixed_1785_);
lean_closure_set(v___f_1885_, 17, v_used_1786_);
lean_closure_set(v___f_1885_, 18, v_body_1868_);
lean_closure_set(v___f_1885_, 19, v_toBind_1880_);
lean_closure_set(v___f_1885_, 20, v_withNewLemmas_1881_);
lean_closure_set(v___f_1885_, 21, v_val_1873_);
lean_closure_set(v___f_1885_, 22, v___x_1884_);
v___x_1886_ = lean_apply_1(v_dsimp_1882_, v_val_1873_);
v___x_1887_ = lean_apply_4(v_toBind_1880_, lean_box(0), lean_box(0), v___x_1886_, v___f_1885_);
return v___x_1887_;
}
v___jp_1888_:
{
uint8_t v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = 0;
v___x_1890_ = lean_array_get_size(v_fixed_1785_);
v___x_1891_ = lean_nat_dec_lt(v_i_1788_, v___x_1890_);
if (v___x_1891_ == 0)
{
v___y_1878_ = v___x_1889_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_array_fget_borrowed(v_fixed_1785_, v_i_1788_);
v___x_1893_ = lean_unbox(v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v_toApplicative_1894_; lean_object* v_toBind_1895_; lean_object* v_withNewLemmas_1896_; lean_object* v_simp_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; lean_object* v___f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_inc(v___x_1892_);
lean_inc(v_level_1871_);
v_toApplicative_1894_ = lean_ctor_get(v_inst_1780_, 0);
lean_inc_ref_n(v_toApplicative_1894_, 2);
v_toBind_1895_ = lean_ctor_get(v_inst_1780_, 1);
lean_inc_n(v_toBind_1895_, 3);
v_withNewLemmas_1896_ = lean_ctor_get(v_inst_1783_, 0);
lean_inc(v_withNewLemmas_1896_);
v_simp_1897_ = lean_ctor_get(v_inst_1783_, 2);
lean_inc(v_simp_1897_);
v___x_1898_ = lean_box(v_nondep_1864_);
lean_inc(v_inst_1781_);
lean_inc_ref(v_xs_1789_);
lean_inc_ref(v_value_1867_);
lean_inc_ref(v_type_1866_);
lean_inc(v_declName_1865_);
v___f_1899_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_1899_, 0, v_decl_1870_);
lean_closure_set(v___f_1899_, 1, v_declName_1865_);
lean_closure_set(v___f_1899_, 2, v_type_1866_);
lean_closure_set(v___f_1899_, 3, v_value_1867_);
lean_closure_set(v___f_1899_, 4, v___x_1898_);
lean_closure_set(v___f_1899_, 5, v_toApplicative_1894_);
lean_closure_set(v___f_1899_, 6, v___x_1875_);
lean_closure_set(v___f_1899_, 7, v_us_1876_);
lean_closure_set(v___f_1899_, 8, v_inst_1780_);
lean_closure_set(v___f_1899_, 9, v_x_1872_);
lean_closure_set(v___f_1899_, 10, v_i_1788_);
lean_closure_set(v___f_1899_, 11, v_xs_1789_);
lean_closure_set(v___f_1899_, 12, v_inst_1781_);
lean_closure_set(v___f_1899_, 13, v_inst_1782_);
lean_closure_set(v___f_1899_, 14, v_inst_1783_);
lean_closure_set(v___f_1899_, 15, v_info_1784_);
lean_closure_set(v___f_1899_, 16, v_fixed_1785_);
lean_closure_set(v___f_1899_, 17, v_used_1786_);
lean_closure_set(v___f_1899_, 18, v_body_1868_);
lean_closure_set(v___f_1899_, 19, v_toBind_1895_);
lean_closure_set(v___f_1899_, 20, v_withNewLemmas_1896_);
v___f_1900_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1900_, 0, v___f_1899_);
v___x_1901_ = lean_box(v_nondep_1864_);
lean_inc_ref(v_val_1873_);
lean_inc_ref(v___f_1900_);
v___f_1902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_1902_, 0, v_toApplicative_1894_);
lean_closure_set(v___f_1902_, 1, v_level_1871_);
lean_closure_set(v___f_1902_, 2, v___x_1874_);
lean_closure_set(v___f_1902_, 3, v_type_1866_);
lean_closure_set(v___f_1902_, 4, v_value_1867_);
lean_closure_set(v___f_1902_, 5, v___x_1892_);
lean_closure_set(v___f_1902_, 6, v_toBind_1895_);
lean_closure_set(v___f_1902_, 7, v___f_1900_);
lean_closure_set(v___f_1902_, 8, v_xs_1789_);
lean_closure_set(v___f_1902_, 9, v___x_1901_);
lean_closure_set(v___f_1902_, 10, v___f_1900_);
lean_closure_set(v___f_1902_, 11, v_declName_1865_);
lean_closure_set(v___f_1902_, 12, v_val_1873_);
lean_closure_set(v___f_1902_, 13, v_inst_1781_);
v___x_1903_ = lean_apply_1(v_simp_1897_, v_val_1873_);
v___x_1904_ = lean_apply_4(v_toBind_1895_, lean_box(0), lean_box(0), v___x_1903_, v___f_1902_);
return v___x_1904_;
}
else
{
v___y_1878_ = v___x_1889_;
goto v___jp_1877_;
}
}
}
}
else
{
lean_dec_ref(v_e_1787_);
lean_dec_ref(v_xs_1789_);
lean_dec(v_i_1788_);
lean_dec_ref(v_used_1786_);
lean_dec_ref(v_fixed_1785_);
lean_dec_ref(v_info_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
lean_dec(v_inst_1781_);
goto v___jp_1790_;
}
}
else
{
lean_dec_ref(v_xs_1789_);
lean_dec(v_i_1788_);
lean_dec_ref(v_e_1787_);
lean_dec_ref(v_used_1786_);
lean_dec_ref(v_fixed_1785_);
lean_dec_ref(v_info_1784_);
lean_dec_ref(v_inst_1783_);
lean_dec_ref(v_inst_1782_);
lean_dec(v_inst_1781_);
goto v___jp_1790_;
}
}
v___jp_1790_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1791_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1792_ = l_instInhabitedOfMonad___redArg(v_inst_1780_, v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1794_ = l_panic___redArg(v___x_1792_, v___x_1793_);
lean_dec(v___x_1792_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1966_, lean_object* v_declName_1967_, lean_object* v_type_1968_, lean_object* v_value_1969_, lean_object* v_us_1970_, lean_object* v___x_1971_, lean_object* v_toApplicative_1972_, uint8_t v_nondep_1973_, lean_object* v_i_1974_, lean_object* v_xs_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_info_1980_, lean_object* v_fixed_1981_, lean_object* v_used_1982_, lean_object* v_body_1983_, lean_object* v_toBind_1984_, lean_object* v_____r_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v_x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1987_ = l_Lean_mkConst(v___x_1986_, v___x_1966_);
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = lean_box(v_nondep_1973_);
v___f_1990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1990_, 0, v___x_1988_);
lean_closure_set(v___f_1990_, 1, v_declName_1967_);
lean_closure_set(v___f_1990_, 2, v_type_1968_);
lean_closure_set(v___f_1990_, 3, v_value_1969_);
lean_closure_set(v___f_1990_, 4, v_us_1970_);
lean_closure_set(v___f_1990_, 5, v___x_1971_);
lean_closure_set(v___f_1990_, 6, v_toApplicative_1972_);
lean_closure_set(v___f_1990_, 7, v___x_1989_);
v___x_1991_ = lean_nat_add(v_i_1974_, v___x_1988_);
v___x_1992_ = lean_array_push(v_xs_1975_, v_x_1987_);
v___x_1993_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1976_, v_inst_1977_, v_inst_1978_, v_inst_1979_, v_info_1980_, v_fixed_1981_, v_used_1982_, v_body_1983_, v___x_1991_, v___x_1992_);
v___x_1994_ = lean_apply_4(v_toBind_1984_, lean_box(0), lean_box(0), v___x_1993_, v___f_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1995_, lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_info_2000_, lean_object* v_fixed_2001_, lean_object* v_used_2002_, lean_object* v_e_2003_, lean_object* v_i_2004_, lean_object* v_xs_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1996_, v_inst_1997_, v_inst_1998_, v_inst_1999_, v_info_2000_, v_fixed_2001_, v_used_2002_, v_e_2003_, v_i_2004_, v_xs_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_2007_){
_start:
{
switch(v_x_2007_)
{
case 0:
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_unsigned_to_nat(0u);
return v___x_2008_;
}
case 1:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_unsigned_to_nat(1u);
return v___x_2009_;
}
default: 
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_unsigned_to_nat(2u);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2011_){
_start:
{
uint8_t v_x_boxed_2012_; lean_object* v_res_2013_; 
v_x_boxed_2012_ = lean_unbox(v_x_2011_);
v_res_2013_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t v_x_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object* v_x_2016_){
_start:
{
uint8_t v_x_4__boxed_2017_; lean_object* v_res_2018_; 
v_x_4__boxed_2017_ = lean_unbox(v_x_2016_);
v_res_2018_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_2017_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2019_){
_start:
{
lean_inc(v_k_2019_);
return v_k_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2020_);
lean_dec(v_k_2020_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2022_, lean_object* v_ctorIdx_2023_, uint8_t v_t_2024_, lean_object* v_h_2025_, lean_object* v_k_2026_){
_start:
{
lean_inc(v_k_2026_);
return v_k_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2027_, lean_object* v_ctorIdx_2028_, lean_object* v_t_2029_, lean_object* v_h_2030_, lean_object* v_k_2031_){
_start:
{
uint8_t v_t_boxed_2032_; lean_object* v_res_2033_; 
v_t_boxed_2032_ = lean_unbox(v_t_2029_);
v_res_2033_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2027_, v_ctorIdx_2028_, v_t_boxed_2032_, v_h_2030_, v_k_2031_);
lean_dec(v_k_2031_);
lean_dec(v_ctorIdx_2028_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2034_){
_start:
{
lean_inc(v_no_2034_);
return v_no_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2035_);
lean_dec(v_no_2035_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2037_, uint8_t v_t_2038_, lean_object* v_h_2039_, lean_object* v_no_2040_){
_start:
{
lean_inc(v_no_2040_);
return v_no_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2041_, lean_object* v_t_2042_, lean_object* v_h_2043_, lean_object* v_no_2044_){
_start:
{
uint8_t v_t_boxed_2045_; lean_object* v_res_2046_; 
v_t_boxed_2045_ = lean_unbox(v_t_2042_);
v_res_2046_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2041_, v_t_boxed_2045_, v_h_2043_, v_no_2044_);
lean_dec(v_no_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2047_){
_start:
{
lean_inc(v_singlePass_2047_);
return v_singlePass_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2048_);
lean_dec(v_singlePass_2048_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2050_, uint8_t v_t_2051_, lean_object* v_h_2052_, lean_object* v_singlePass_2053_){
_start:
{
lean_inc(v_singlePass_2053_);
return v_singlePass_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2054_, lean_object* v_t_2055_, lean_object* v_h_2056_, lean_object* v_singlePass_2057_){
_start:
{
uint8_t v_t_boxed_2058_; lean_object* v_res_2059_; 
v_t_boxed_2058_ = lean_unbox(v_t_2055_);
v_res_2059_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2054_, v_t_boxed_2058_, v_h_2056_, v_singlePass_2057_);
lean_dec(v_singlePass_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2060_){
_start:
{
lean_inc(v_twoPasses_2060_);
return v_twoPasses_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2061_);
lean_dec(v_twoPasses_2061_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2063_, uint8_t v_t_2064_, lean_object* v_h_2065_, lean_object* v_twoPasses_2066_){
_start:
{
lean_inc(v_twoPasses_2066_);
return v_twoPasses_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2067_, lean_object* v_t_2068_, lean_object* v_h_2069_, lean_object* v_twoPasses_2070_){
_start:
{
uint8_t v_t_boxed_2071_; lean_object* v_res_2072_; 
v_t_boxed_2071_ = lean_unbox(v_t_2068_);
v_res_2072_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2067_, v_t_boxed_2071_, v_h_2069_, v_twoPasses_2070_);
lean_dec(v_twoPasses_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2073_, lean_object* v_b_2074_, lean_object* v_c_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; 
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
v___x_2081_ = lean_apply_7(v_k_2073_, v_b_2074_, v_c_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, lean_box(0));
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2082_, lean_object* v_b_2083_, lean_object* v_c_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2082_, v_b_2083_, v_c_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2091_, lean_object* v_k_2092_, uint8_t v_cleanupAnnotations_2093_, uint8_t v_preserveNondepLet_2094_, uint8_t v_nondepLetOnly_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___f_2101_; uint8_t v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___f_2101_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2101_, 0, v_k_2092_);
v___x_2102_ = 0;
v___x_2103_ = 1;
v___x_2104_ = lean_box(0);
v___x_2105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2091_, v___x_2102_, v___x_2103_, v_preserveNondepLet_2094_, v_nondepLetOnly_2095_, v___x_2104_, v___f_2101_, v_cleanupAnnotations_2093_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2105_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2105_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2122_, lean_object* v_k_2123_, lean_object* v_cleanupAnnotations_2124_, lean_object* v_preserveNondepLet_2125_, lean_object* v_nondepLetOnly_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2132_; uint8_t v_preserveNondepLet_boxed_2133_; uint8_t v_nondepLetOnly_boxed_2134_; lean_object* v_res_2135_; 
v_cleanupAnnotations_boxed_2132_ = lean_unbox(v_cleanupAnnotations_2124_);
v_preserveNondepLet_boxed_2133_ = lean_unbox(v_preserveNondepLet_2125_);
v_nondepLetOnly_boxed_2134_ = lean_unbox(v_nondepLetOnly_2126_);
v_res_2135_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2122_, v_k_2123_, v_cleanupAnnotations_boxed_2132_, v_preserveNondepLet_boxed_2133_, v_nondepLetOnly_boxed_2134_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2136_, lean_object* v_e_2137_, lean_object* v_k_2138_, uint8_t v_cleanupAnnotations_2139_, uint8_t v_preserveNondepLet_2140_, uint8_t v_nondepLetOnly_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2137_, v_k_2138_, v_cleanupAnnotations_2139_, v_preserveNondepLet_2140_, v_nondepLetOnly_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_e_2149_, lean_object* v_k_2150_, lean_object* v_cleanupAnnotations_2151_, lean_object* v_preserveNondepLet_2152_, lean_object* v_nondepLetOnly_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2159_; uint8_t v_preserveNondepLet_boxed_2160_; uint8_t v_nondepLetOnly_boxed_2161_; lean_object* v_res_2162_; 
v_cleanupAnnotations_boxed_2159_ = lean_unbox(v_cleanupAnnotations_2151_);
v_preserveNondepLet_boxed_2160_ = lean_unbox(v_preserveNondepLet_2152_);
v_nondepLetOnly_boxed_2161_ = lean_unbox(v_nondepLetOnly_2153_);
v_res_2162_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2148_, v_e_2149_, v_k_2150_, v_cleanupAnnotations_boxed_2159_, v_preserveNondepLet_boxed_2160_, v_nondepLetOnly_boxed_2161_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_snd_2169_; lean_object* v_fst_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2225_; 
v_snd_2169_ = lean_ctor_get(v_b_2164_, 1);
v_fst_2170_ = lean_ctor_get(v_b_2164_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2172_ = v_b_2164_;
v_isShared_2173_ = v_isSharedCheck_2225_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_snd_2169_);
lean_inc(v_fst_2170_);
lean_dec(v_b_2164_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2225_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2224_; 
v_fst_2174_ = lean_ctor_get(v_snd_2169_, 0);
v_snd_2175_ = lean_ctor_get(v_snd_2169_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_snd_2169_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2177_ = v_snd_2169_;
v_isShared_2178_ = v_isSharedCheck_2224_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_inc(v_fst_2174_);
lean_dec(v_snd_2169_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2224_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_nat_dec_lt(v___x_2179_, v_snd_2175_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2182_; 
if (v_isShared_2178_ == 0)
{
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_fst_2174_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_snd_2175_);
v___x_2182_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2182_);
v___x_2184_ = v___x_2172_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_fst_2170_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
}
else
{
lean_object* v_fvarSet_2188_; lean_object* v___x_2189_; lean_object* v_i_2190_; lean_object* v___x_2191_; lean_object* v_x_2192_; lean_object* v_xFVarId_2193_; uint8_t v___x_2194_; 
v_fvarSet_2188_ = lean_ctor_get(v_fst_2170_, 1);
v___x_2189_ = lean_unsigned_to_nat(1u);
v_i_2190_ = lean_nat_sub(v_snd_2175_, v___x_2189_);
lean_dec(v_snd_2175_);
v___x_2191_ = l_Lean_instInhabitedExpr;
v_x_2192_ = lean_array_get_borrowed(v___x_2191_, v_xs_2163_, v_i_2190_);
v_xFVarId_2193_ = l_Lean_Expr_fvarId_x21(v_x_2192_);
v___x_2194_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_xFVarId_2193_, v_fvarSet_2188_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2196_; 
lean_dec(v_xFVarId_2193_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_i_2190_);
v___x_2196_ = v___x_2177_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_fst_2174_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_i_2190_);
v___x_2196_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2196_);
v___x_2198_ = v___x_2172_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_fst_2170_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
v_b_2164_ = v___x_2198_;
goto _start;
}
}
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_FVarId_getDecl___redArg(v_xFVarId_2193_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = l_Lean_LocalDecl_type(v_a_2203_);
v___x_2205_ = l_Lean_collectFVars(v_fst_2170_, v___x_2204_);
v___x_2206_ = l_Lean_LocalDecl_value(v_a_2203_, v___x_2194_);
lean_dec(v_a_2203_);
v___x_2207_ = l_Lean_collectFVars(v___x_2205_, v___x_2206_);
lean_inc(v_x_2192_);
v___x_2208_ = lean_array_push(v_fst_2174_, v_x_2192_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_i_2190_);
lean_ctor_set(v___x_2177_, 0, v___x_2208_);
v___x_2210_ = v___x_2177_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_i_2190_);
v___x_2210_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2210_);
lean_ctor_set(v___x_2172_, 0, v___x_2207_);
v___x_2212_ = v___x_2172_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
v_b_2164_ = v___x_2212_;
goto _start;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_i_2190_);
lean_del_object(v___x_2177_);
lean_dec(v_fst_2174_);
lean_del_object(v___x_2172_);
lean_dec(v_fst_2170_);
v_a_2216_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2202_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2202_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2226_, v_b_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_xs_2226_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2233_, lean_object* v_e_2234_, lean_object* v_xs_2235_, lean_object* v_body_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_s_2245_; lean_object* v_i_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2242_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2243_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2233_);
lean_ctor_set(v___x_2244_, 2, v___x_2243_);
lean_inc_ref(v_body_2236_);
v_s_2245_ = l_Lean_collectFVars(v___x_2244_, v_body_2236_);
v_i_2246_ = lean_array_get_size(v_xs_2235_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2243_);
lean_ctor_set(v___x_2247_, 1, v_i_2246_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_s_2245_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2235_, v___x_2248_, v___y_2237_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2265_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2265_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2265_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_snd_2254_; lean_object* v_fst_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_snd_2254_ = lean_ctor_get(v_a_2250_, 1);
lean_inc(v_snd_2254_);
lean_dec(v_a_2250_);
v_fst_2255_ = lean_ctor_get(v_snd_2254_, 0);
lean_inc(v_fst_2255_);
lean_dec(v_snd_2254_);
v___x_2256_ = lean_array_get_size(v_fst_2255_);
v___x_2257_ = lean_nat_dec_eq(v___x_2256_, v_i_2246_);
if (v___x_2257_ == 0)
{
uint8_t v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; 
lean_del_object(v___x_2252_);
lean_dec_ref(v_e_2234_);
v___x_2258_ = 1;
v___x_2259_ = l_Array_reverse___redArg(v_fst_2255_);
v___x_2260_ = 1;
v___x_2261_ = l_Lean_Meta_mkLetFVars(v___x_2259_, v_body_2236_, v___x_2258_, v___x_2257_, v___x_2260_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec_ref(v___x_2259_);
return v___x_2261_;
}
else
{
lean_object* v___x_2263_; 
lean_dec(v_fst_2255_);
lean_dec_ref(v_body_2236_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_e_2234_);
v___x_2263_ = v___x_2252_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_e_2234_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_body_2236_);
lean_dec_ref(v_e_2234_);
v_a_2266_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2249_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2249_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2274_, lean_object* v_e_2275_, lean_object* v_xs_2276_, lean_object* v_body_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2274_, v_e_2275_, v_xs_2276_, v_body_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_xs_2276_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; lean_object* v___f_2291_; uint8_t v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; 
v___x_2290_ = lean_box(1);
lean_inc_ref(v_e_2284_);
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2291_, 0, v___x_2290_);
lean_closure_set(v___f_2291_, 1, v_e_2284_);
v___x_2292_ = 0;
v___x_2293_ = 1;
v___x_2294_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2284_, v___f_2291_, v___x_2292_, v___x_2293_, v___x_2292_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Meta_zetaUnused(v_e_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2302_, lean_object* v_b_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2302_, v_b_2303_, v___y_2304_, v___y_2306_, v___y_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2310_, lean_object* v_b_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2310_, v_b_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v_xs_2310_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2322_, lean_object* v_source_2323_, lean_object* v_result_2324_, uint8_t v_keepUnused_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
uint8_t v_modified_2331_; 
v_modified_2331_ = lean_ctor_get_uint8(v_result_2324_, sizeof(void*)*5);
if (v_modified_2331_ == 0)
{
if (v_keepUnused_2325_ == 0)
{
lean_object* v_exprType_2332_; lean_object* v___x_2333_; 
v_exprType_2332_ = lean_ctor_get(v_result_2324_, 1);
lean_inc_ref(v_exprType_2332_);
lean_dec_ref(v_result_2324_);
lean_inc_ref(v_source_2323_);
v___x_2333_ = l_Lean_Meta_zetaUnused(v_source_2323_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2352_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2352_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2352_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_expr_eqv(v_a_2334_, v_source_2323_);
lean_dec_ref(v_source_2323_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_u_2322_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = l_Lean_mkConst(v___x_2339_, v___x_2341_);
lean_inc(v_a_2334_);
v___x_2343_ = l_Lean_mkAppB(v___x_2342_, v_exprType_2332_, v_a_2334_);
v___x_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2334_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2344_);
v___x_2346_ = v___x_2336_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v_a_2334_);
lean_dec_ref(v_exprType_2332_);
lean_dec(v_u_2322_);
v___x_2348_ = lean_box(0);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2348_);
v___x_2350_ = v___x_2336_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_exprType_2332_);
lean_dec_ref(v_source_2323_);
lean_dec(v_u_2322_);
v_a_2353_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2333_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2333_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref(v_result_2324_);
lean_dec_ref(v_source_2323_);
lean_dec(v_u_2322_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
else
{
lean_object* v_expr_2363_; lean_object* v_exprType_2364_; lean_object* v_exprInit_2365_; lean_object* v_exprResult_2366_; lean_object* v_proof_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_proof_2375_; 
v_expr_2363_ = lean_ctor_get(v_result_2324_, 0);
lean_inc_ref(v_expr_2363_);
v_exprType_2364_ = lean_ctor_get(v_result_2324_, 1);
lean_inc_ref_n(v_exprType_2364_, 3);
v_exprInit_2365_ = lean_ctor_get(v_result_2324_, 2);
lean_inc_ref(v_exprInit_2365_);
v_exprResult_2366_ = lean_ctor_get(v_result_2324_, 3);
lean_inc_ref_n(v_exprResult_2366_, 2);
v_proof_2367_ = lean_ctor_get(v_result_2324_, 4);
lean_inc_ref(v_proof_2367_);
lean_dec_ref(v_result_2324_);
v___x_2368_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_u_2322_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
lean_inc_ref(v___x_2370_);
v___x_2371_ = l_Lean_mkConst(v___x_2368_, v___x_2370_);
lean_inc_ref(v___x_2371_);
v___x_2372_ = l_Lean_mkApp3(v___x_2371_, v_exprType_2364_, v_exprInit_2365_, v_expr_2363_);
v___x_2373_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2367_, v___x_2372_);
lean_inc_ref(v_source_2323_);
v___x_2374_ = l_Lean_mkApp3(v___x_2371_, v_exprType_2364_, v_source_2323_, v_exprResult_2366_);
v_proof_2375_ = l_Lean_Meta_mkExpectedPropHint(v___x_2373_, v___x_2374_);
if (v_keepUnused_2325_ == 0)
{
lean_object* v___x_2376_; 
lean_inc_ref(v_exprResult_2366_);
v___x_2376_ = l_Lean_Meta_zetaUnused(v_exprResult_2366_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2396_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2396_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2396_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_expr_eqv(v_a_2377_, v_exprResult_2366_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2370_);
v___x_2383_ = l_Lean_mkConst(v___x_2382_, v___x_2370_);
v___x_2384_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2385_ = l_Lean_mkConst(v___x_2384_, v___x_2370_);
lean_inc_n(v_a_2377_, 2);
lean_inc_ref(v_exprType_2364_);
v___x_2386_ = l_Lean_mkAppB(v___x_2385_, v_exprType_2364_, v_a_2377_);
v___x_2387_ = l_Lean_mkApp6(v___x_2383_, v_exprType_2364_, v_source_2323_, v_exprResult_2366_, v_a_2377_, v_proof_2375_, v___x_2386_);
v___x_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_a_2377_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2388_);
v___x_2390_ = v___x_2379_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_dec(v_a_2377_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v_exprType_2364_);
lean_dec_ref(v_source_2323_);
v___x_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_exprResult_2366_);
lean_ctor_set(v___x_2392_, 1, v_proof_2375_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2392_);
v___x_2394_ = v___x_2379_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
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
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_proof_2375_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v_exprResult_2366_);
lean_dec_ref(v_exprType_2364_);
lean_dec_ref(v_source_2323_);
v_a_2397_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2376_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2376_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v___x_2370_);
lean_dec_ref(v_exprType_2364_);
lean_dec_ref(v_source_2323_);
v___x_2405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_exprResult_2366_);
lean_ctor_set(v___x_2405_, 1, v_proof_2375_);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2407_, lean_object* v_source_2408_, lean_object* v_result_2409_, lean_object* v_keepUnused_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
uint8_t v_keepUnused_boxed_2416_; lean_object* v_res_2417_; 
v_keepUnused_boxed_2416_ = lean_unbox(v_keepUnused_2410_);
v_res_2417_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2407_, v_source_2408_, v_result_2409_, v_keepUnused_boxed_2416_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2418_, lean_object* v_e_2419_, lean_object* v_inst_2420_, uint8_t v_zetaUnusedMode_2421_, uint8_t v___x_2422_, uint8_t v___x_2423_, lean_object* v_r_2424_){
_start:
{
uint8_t v___y_2426_; 
switch(v_zetaUnusedMode_2421_)
{
case 0:
{
v___y_2426_ = v___x_2422_;
goto v___jp_2425_;
}
case 1:
{
v___y_2426_ = v___x_2422_;
goto v___jp_2425_;
}
default: 
{
v___y_2426_ = v___x_2423_;
goto v___jp_2425_;
}
}
v___jp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_box(v___y_2426_);
v___x_2428_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2428_, 0, v_level_2418_);
lean_closure_set(v___x_2428_, 1, v_e_2419_);
lean_closure_set(v___x_2428_, 2, v_r_2424_);
lean_closure_set(v___x_2428_, 3, v___x_2427_);
v___x_2429_ = lean_apply_2(v_inst_2420_, lean_box(0), v___x_2428_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2430_, lean_object* v_e_2431_, lean_object* v_inst_2432_, lean_object* v_zetaUnusedMode_2433_, lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v_r_2436_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2437_; uint8_t v___x_363__boxed_2438_; uint8_t v___x_364__boxed_2439_; lean_object* v_res_2440_; 
v_zetaUnusedMode_boxed_2437_ = lean_unbox(v_zetaUnusedMode_2433_);
v___x_363__boxed_2438_ = lean_unbox(v___x_2434_);
v___x_364__boxed_2439_ = lean_unbox(v___x_2435_);
v_res_2440_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2430_, v_e_2431_, v_inst_2432_, v_zetaUnusedMode_boxed_2437_, v___x_363__boxed_2438_, v___x_364__boxed_2439_, v_r_2436_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_info_2446_, lean_object* v_e_2447_, lean_object* v___x_2448_, lean_object* v_toBind_2449_, lean_object* v___f_2450_, lean_object* v_____x_2451_){
_start:
{
lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_fst_2452_ = lean_ctor_get(v_____x_2451_, 0);
lean_inc(v_fst_2452_);
v_snd_2453_ = lean_ctor_get(v_____x_2451_, 1);
lean_inc(v_snd_2453_);
lean_dec_ref(v_____x_2451_);
v___x_2454_ = lean_mk_empty_array_with_capacity(v___x_2441_);
v___x_2455_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2442_, v_inst_2443_, v_inst_2444_, v_inst_2445_, v_info_2446_, v_fst_2452_, v_snd_2453_, v_e_2447_, v___x_2448_, v___x_2454_);
v___x_2456_ = lean_apply_4(v_toBind_2449_, lean_box(0), lean_box(0), v___x_2455_, v___f_2450_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_info_2462_, lean_object* v_e_2463_, lean_object* v___x_2464_, lean_object* v_toBind_2465_, lean_object* v___f_2466_, lean_object* v_____x_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2457_, v_inst_2458_, v_inst_2459_, v_inst_2460_, v_inst_2461_, v_info_2462_, v_e_2463_, v___x_2464_, v_toBind_2465_, v___f_2466_, v_____x_2467_);
lean_dec(v___x_2457_);
return v_res_2468_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2471_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2472_ = lean_unsigned_to_nat(2u);
v___x_2473_ = lean_unsigned_to_nat(456u);
v___x_2474_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2475_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2476_ = l_mkPanicMessageWithDecl(v___x_2475_, v___x_2474_, v___x_2473_, v___x_2472_, v___x_2471_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2477_, lean_object* v_inst_2478_, uint8_t v_zetaUnusedMode_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_toBind_2483_, lean_object* v_info_2484_){
_start:
{
lean_object* v_haveInfo_2485_; lean_object* v_level_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_haveInfo_2485_ = lean_ctor_get(v_info_2484_, 0);
v_level_2486_ = lean_ctor_get(v_info_2484_, 5);
v___x_2487_ = lean_array_get_size(v_haveInfo_2485_);
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_nat_dec_eq(v___x_2487_, v___x_2488_);
if (v___x_2489_ == 0)
{
uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___f_2495_; uint8_t v___y_2497_; 
v___x_2490_ = 1;
v___x_2491_ = lean_box(v_zetaUnusedMode_2479_);
v___x_2492_ = lean_box(v___x_2490_);
v___x_2493_ = lean_box(v___x_2489_);
lean_inc_n(v_inst_2478_, 2);
lean_inc_ref(v_e_2477_);
lean_inc(v_level_2486_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2494_, 0, v_level_2486_);
lean_closure_set(v___f_2494_, 1, v_e_2477_);
lean_closure_set(v___f_2494_, 2, v_inst_2478_);
lean_closure_set(v___f_2494_, 3, v___x_2491_);
lean_closure_set(v___f_2494_, 4, v___x_2492_);
lean_closure_set(v___f_2494_, 5, v___x_2493_);
lean_inc(v_toBind_2483_);
lean_inc_ref(v_info_2484_);
v___f_2495_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2495_, 0, v___x_2487_);
lean_closure_set(v___f_2495_, 1, v_inst_2480_);
lean_closure_set(v___f_2495_, 2, v_inst_2478_);
lean_closure_set(v___f_2495_, 3, v_inst_2481_);
lean_closure_set(v___f_2495_, 4, v_inst_2482_);
lean_closure_set(v___f_2495_, 5, v_info_2484_);
lean_closure_set(v___f_2495_, 6, v_e_2477_);
lean_closure_set(v___f_2495_, 7, v___x_2488_);
lean_closure_set(v___f_2495_, 8, v_toBind_2483_);
lean_closure_set(v___f_2495_, 9, v___f_2494_);
switch(v_zetaUnusedMode_2479_)
{
case 0:
{
v___y_2497_ = v___x_2490_;
goto v___jp_2496_;
}
case 2:
{
v___y_2497_ = v___x_2490_;
goto v___jp_2496_;
}
default: 
{
v___y_2497_ = v___x_2489_;
goto v___jp_2496_;
}
}
v___jp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2498_ = lean_box(v___y_2497_);
v___x_2499_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2499_, 0, v_info_2484_);
lean_closure_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_apply_2(v_inst_2478_, lean_box(0), v___x_2499_);
v___x_2501_ = lean_apply_4(v_toBind_2483_, lean_box(0), lean_box(0), v___x_2500_, v___f_2495_);
return v___x_2501_;
}
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec_ref(v_info_2484_);
lean_dec(v_toBind_2483_);
lean_dec_ref(v_inst_2482_);
lean_dec_ref(v_inst_2481_);
lean_dec(v_inst_2478_);
lean_dec_ref(v_e_2477_);
v___x_2502_ = lean_box(0);
v___x_2503_ = l_instInhabitedOfMonad___redArg(v_inst_2480_, v___x_2502_);
v___x_2504_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2505_ = l_panic___redArg(v___x_2503_, v___x_2504_);
lean_dec(v___x_2503_);
return v___x_2505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2506_, lean_object* v_inst_2507_, lean_object* v_zetaUnusedMode_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_toBind_2512_, lean_object* v_info_2513_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2514_; lean_object* v_res_2515_; 
v_zetaUnusedMode_boxed_2514_ = lean_unbox(v_zetaUnusedMode_2508_);
v_res_2515_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2506_, v_inst_2507_, v_zetaUnusedMode_boxed_2514_, v_inst_2509_, v_inst_2510_, v_inst_2511_, v_toBind_2512_, v_info_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_e_2520_, uint8_t v_zetaUnusedMode_2521_){
_start:
{
lean_object* v_toBind_2522_; lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_toBind_2522_ = lean_ctor_get(v_inst_2516_, 1);
lean_inc_n(v_toBind_2522_, 2);
v___x_2523_ = lean_box(v_zetaUnusedMode_2521_);
lean_inc(v_inst_2517_);
lean_inc_ref(v_e_2520_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2524_, 0, v_e_2520_);
lean_closure_set(v___f_2524_, 1, v_inst_2517_);
lean_closure_set(v___f_2524_, 2, v___x_2523_);
lean_closure_set(v___f_2524_, 3, v_inst_2516_);
lean_closure_set(v___f_2524_, 4, v_inst_2518_);
lean_closure_set(v___f_2524_, 5, v_inst_2519_);
lean_closure_set(v___f_2524_, 6, v_toBind_2522_);
v___x_2525_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2525_, 0, v_e_2520_);
v___x_2526_ = lean_apply_2(v_inst_2517_, lean_box(0), v___x_2525_);
v___x_2527_ = lean_apply_4(v_toBind_2522_, lean_box(0), lean_box(0), v___x_2526_, v___f_2524_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_e_2532_, lean_object* v_zetaUnusedMode_2533_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2534_; lean_object* v_res_2535_; 
v_zetaUnusedMode_boxed_2534_ = lean_unbox(v_zetaUnusedMode_2533_);
v_res_2535_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2528_, v_inst_2529_, v_inst_2530_, v_inst_2531_, v_e_2532_, v_zetaUnusedMode_boxed_2534_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_e_2541_, uint8_t v_zetaUnusedMode_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2537_, v_inst_2538_, v_inst_2539_, v_inst_2540_, v_e_2541_, v_zetaUnusedMode_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_e_2549_, lean_object* v_zetaUnusedMode_2550_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2551_; lean_object* v_res_2552_; 
v_zetaUnusedMode_boxed_2551_ = lean_unbox(v_zetaUnusedMode_2550_);
v_res_2552_ = l_Lean_Meta_simpHaveTelescope(v_m_2544_, v_inst_2545_, v_inst_2546_, v_inst_2547_, v_inst_2548_, v_e_2549_, v_zetaUnusedMode_boxed_2551_);
return v_res_2552_;
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
