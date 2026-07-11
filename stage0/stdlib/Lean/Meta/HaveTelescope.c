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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.HaveTelescope"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Meta.HaveTelescope.0.Lean.Meta.simpHaveTelescopeAux"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "assertion violation: !rb.exprType.hasLooseBVar 0\n        "};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(255, 213, 12, 50, 85, 170, 122, 222)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(238, 251, 30, 34, 208, 131, 54, 223)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(33, 35, 129, 148, 230, 9, 239, 46)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "_simp_let_unused_dummy"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 140, 102, 13, 80, 16, 156, 102)}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1_value;
static const lean_string_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.simpHaveTelescope"};
static const lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "assertion violation: !info.haveInfo.isEmpty\n  "};
static const lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_284_, 1);
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
lean_dec_ref_known(v_e_400_, 4);
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
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_haveInfo_431_; lean_object* v_bodyDeps_432_; lean_object* v_bodyTypeDeps_433_; lean_object* v_body_434_; lean_object* v_bodyType_435_; lean_object* v_level_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
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
lean_dec_ref_known(v___x_703_, 1);
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
lean_dec_ref_known(v___x_836_, 2);
if (lean_obj_tag(v_declName_837_) == 1)
{
lean_object* v_pre_838_; 
v_pre_838_ = lean_ctor_get(v_declName_837_, 0);
if (lean_obj_tag(v_pre_838_) == 0)
{
lean_object* v_str_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_str_839_ = lean_ctor_get(v_declName_837_, 1);
lean_inc_ref(v_str_839_);
lean_dec_ref_known(v_declName_837_, 2);
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
lean_dec_ref_known(v_declName_837_, 2);
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
uint8_t v___x_10956__boxed_859_; lean_object* v_res_860_; 
v___x_10956__boxed_859_ = lean_unbox(v___x_856_);
v_res_860_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_852_, v_level_853_, v_exprType_854_, v_e_855_, v___x_10956__boxed_859_, v_xs_857_, v_____do__lift_858_);
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
uint8_t v___x_11109__boxed_887_; lean_object* v_res_888_; 
v___x_11109__boxed_887_ = lean_unbox(v___x_883_);
v_res_888_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_877_, v_bodyType_878_, v_xs_879_, v_toApplicative_880_, v_level_881_, v_e_882_, v___x_11109__boxed_887_, v_body_884_, v_toBind_885_, v_____r_886_);
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
lean_object* v___f_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_toMonadRef_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_10515__overap_927_; lean_object* v___x_928_; 
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
v___x_10515__overap_927_ = l_Lean_addTrace___redArg(v___x_901_, v___x_902_, v_toMonadRef_922_, v___x_923_, v_cls_897_, v___x_926_);
v___x_928_ = lean_apply_5(v___x_10515__overap_927_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_943_, lean_object* v_type_944_, lean_object* v___y_945_, lean_object* v_value_946_, uint8_t v_nondep_947_, lean_object* v_toApplicative_948_, lean_object* v___x_949_, uint8_t v_vModified_950_, lean_object* v_us_951_, lean_object* v_rb_952_){
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
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*5, v_vModified_950_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_988_, lean_object* v_type_989_, lean_object* v___y_990_, lean_object* v_value_991_, lean_object* v_nondep_992_, lean_object* v_toApplicative_993_, lean_object* v___x_994_, lean_object* v_vModified_995_, lean_object* v_us_996_, lean_object* v_rb_997_){
_start:
{
uint8_t v_nondep_11225__boxed_998_; uint8_t v_vModified_boxed_999_; lean_object* v_res_1000_; 
v_nondep_11225__boxed_998_ = lean_unbox(v_nondep_992_);
v_vModified_boxed_999_ = lean_unbox(v_vModified_995_);
v_res_1000_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_988_, v_type_989_, v___y_990_, v_value_991_, v_nondep_11225__boxed_998_, v_toApplicative_993_, v___x_994_, v_vModified_boxed_999_, v_us_996_, v_rb_997_);
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
uint8_t v_nondep_11309__boxed_1062_; lean_object* v_res_1063_; 
v_nondep_11309__boxed_1062_ = lean_unbox(v_nondep_1060_);
v_res_1063_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1053_, v_declName_1054_, v_type_1055_, v_value_1056_, v_us_1057_, v___x_1058_, v_toApplicative_1059_, v_nondep_11309__boxed_1062_, v_rb_1061_);
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
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_toMonadRef_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_10922__overap_1105_; lean_object* v___x_1106_; 
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
v___x_10922__overap_1105_ = l_Lean_addTrace___redArg(v___x_1075_, v___x_1076_, v_toMonadRef_1096_, v___x_1097_, v_cls_1070_, v___x_1104_);
v___x_1106_ = lean_apply_5(v___x_10922__overap_1105_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, lean_box(0));
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
lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_toMonadRef_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_10604__overap_1166_; lean_object* v___x_1167_; 
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
v___x_10604__overap_1166_ = l_Lean_addTrace___redArg(v___x_1132_, v___x_1133_, v_toMonadRef_1153_, v___x_1154_, v_cls_1126_, v___x_1165_);
v___x_1167_ = lean_apply_5(v___x_10604__overap_1166_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, lean_box(0));
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
uint8_t v_nondep_11575__boxed_1206_; lean_object* v_res_1207_; 
v_nondep_11575__boxed_1206_ = lean_unbox(v_nondep_1202_);
v_res_1207_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1198_, v_e_1199_, v_xs_1200_, v_h_1201_, v_nondep_11575__boxed_1206_, v_toBind_1203_, v___f_1204_, v_____r_1205_);
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
lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_toMonadRef_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_10784__overap_1251_; lean_object* v___x_1252_; 
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
v___x_10784__overap_1251_ = l_Lean_addTrace___redArg(v___x_1217_, v___x_1218_, v_toMonadRef_1238_, v___x_1239_, v_cls_1211_, v___x_1250_);
v___x_1252_ = lean_apply_5(v___x_10784__overap_1251_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, lean_box(0));
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
uint8_t v___x_11762__boxed_1394_; uint8_t v_nondep_11764__boxed_1395_; lean_object* v_res_1396_; 
v___x_11762__boxed_1394_ = lean_unbox(v___x_1384_);
v_nondep_11764__boxed_1395_ = lean_unbox(v_nondep_1388_);
v_res_1396_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1379_, v_level_1380_, v___x_1381_, v_type_1382_, v_value_1383_, v___x_11762__boxed_1394_, v_toBind_1385_, v___f_1386_, v_xs_1387_, v_nondep_11764__boxed_1395_, v___f_1389_, v_declName_1390_, v_val_1391_, v_inst_1392_, v_____do__lift_1393_);
return v_res_1396_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1401_ = lean_unsigned_to_nat(8u);
v___x_1402_ = lean_unsigned_to_nat(287u);
v___x_1403_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1405_ = l_mkPanicMessageWithDecl(v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_inst_1412_, lean_object* v_declName_1413_, lean_object* v_type_1414_, lean_object* v_fst_1415_, lean_object* v___x_1416_, lean_object* v_value_1417_, uint8_t v_nondep_1418_, uint8_t v_fst_1419_, lean_object* v_toApplicative_1420_, lean_object* v___x_1421_, lean_object* v_us_1422_, lean_object* v_snd_1423_, lean_object* v_rb_1424_){
_start:
{
lean_object* v_expr_1425_; lean_object* v_exprType_1426_; lean_object* v_exprInit_1427_; lean_object* v_exprResult_1428_; lean_object* v_proof_1429_; uint8_t v_modified_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1482_; 
v_expr_1425_ = lean_ctor_get(v_rb_1424_, 0);
v_exprType_1426_ = lean_ctor_get(v_rb_1424_, 1);
v_exprInit_1427_ = lean_ctor_get(v_rb_1424_, 2);
v_exprResult_1428_ = lean_ctor_get(v_rb_1424_, 3);
v_proof_1429_ = lean_ctor_get(v_rb_1424_, 4);
v_modified_1430_ = lean_ctor_get_uint8(v_rb_1424_, sizeof(void*)*5);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_rb_1424_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1432_ = v_rb_1424_;
v_isShared_1433_ = v_isSharedCheck_1482_;
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
v_isShared_1433_ = v_isSharedCheck_1482_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_expr_has_loose_bvar(v_exprType_1426_, v___x_1434_);
v___x_1436_ = lean_bool_not(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_del_object(v___x_1432_);
lean_dec_ref(v_proof_1429_);
lean_dec_ref(v_exprResult_1428_);
lean_dec_ref(v_exprInit_1427_);
lean_dec_ref(v_exprType_1426_);
lean_dec_ref(v_expr_1425_);
lean_dec_ref(v_snd_1423_);
lean_dec(v_us_1422_);
lean_dec(v___x_1421_);
lean_dec_ref(v_toApplicative_1420_);
lean_dec_ref(v_value_1417_);
lean_dec_ref(v_fst_1415_);
lean_dec_ref(v_type_1414_);
lean_dec(v_declName_1413_);
v___x_1437_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1438_ = l_instInhabitedOfMonad___redArg(v_inst_1412_, v___x_1437_);
v___x_1439_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3);
v___x_1440_ = l_panic___redArg(v___x_1438_, v___x_1439_);
lean_dec(v___x_1438_);
return v___x_1440_;
}
else
{
uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v_expr_1443_; lean_object* v_exprType_1444_; lean_object* v___x_1445_; lean_object* v_exprInit_1446_; lean_object* v_exprResult_1447_; 
lean_dec_ref(v_inst_1412_);
v___x_1441_ = 0;
lean_inc_ref_n(v_type_1414_, 3);
lean_inc_n(v_declName_1413_, 3);
v___x_1442_ = l_Lean_mkLambda(v_declName_1413_, v___x_1441_, v_type_1414_, v_expr_1425_);
lean_inc_ref_n(v_fst_1415_, 2);
lean_inc_ref(v___x_1442_);
v_expr_1443_ = l_Lean_Expr_app___override(v___x_1442_, v_fst_1415_);
v_exprType_1444_ = lean_expr_lower_loose_bvars(v_exprType_1426_, v___x_1416_, v___x_1416_);
lean_dec_ref(v_exprType_1426_);
v___x_1445_ = l_Lean_mkLambda(v_declName_1413_, v___x_1441_, v_type_1414_, v_exprInit_1427_);
lean_inc_ref(v_value_1417_);
lean_inc_ref(v___x_1445_);
v_exprInit_1446_ = l_Lean_Expr_app___override(v___x_1445_, v_value_1417_);
v_exprResult_1447_ = l_Lean_Expr_letE___override(v_declName_1413_, v_type_1414_, v_fst_1415_, v_exprResult_1428_, v_nondep_1418_);
if (v_fst_1419_ == 0)
{
lean_dec_ref(v_snd_1423_);
lean_dec_ref(v_fst_1415_);
if (v_modified_1430_ == 0)
{
lean_object* v_toPure_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_proof_1451_; lean_object* v___x_1453_; 
lean_dec_ref(v___x_1445_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v_proof_1429_);
lean_dec(v_us_1422_);
lean_dec_ref(v_value_1417_);
lean_dec_ref(v_type_1414_);
lean_dec(v_declName_1413_);
v_toPure_1448_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1448_);
lean_dec_ref(v_toApplicative_1420_);
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1450_ = l_Lean_mkConst(v___x_1449_, v___x_1421_);
lean_inc_ref(v_expr_1443_);
lean_inc_ref(v_exprType_1444_);
v_proof_1451_ = l_Lean_mkAppB(v___x_1450_, v_exprType_1444_, v_expr_1443_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1451_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1447_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1446_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1444_);
lean_ctor_set(v___x_1432_, 0, v_expr_1443_);
v___x_1453_ = v___x_1432_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_expr_1443_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_exprType_1444_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_exprInit_1446_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_exprResult_1447_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_proof_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1455_, sizeof(void*)*5, v_modified_1430_);
v___x_1453_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_apply_2(v_toPure_1448_, lean_box(0), v___x_1453_);
return v___x_1454_;
}
}
else
{
lean_object* v_toPure_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_proof_1460_; lean_object* v___x_1462_; 
lean_dec(v___x_1421_);
v_toPure_1456_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1456_);
lean_dec_ref(v_toApplicative_1420_);
lean_inc_ref(v_type_1414_);
v___x_1457_ = l_Lean_mkLambda(v_declName_1413_, v___x_1441_, v_type_1414_, v_proof_1429_);
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1459_ = l_Lean_mkConst(v___x_1458_, v_us_1422_);
lean_inc_ref(v_exprType_1444_);
v_proof_1460_ = l_Lean_mkApp6(v___x_1459_, v_type_1414_, v_exprType_1444_, v_value_1417_, v___x_1445_, v___x_1442_, v___x_1457_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1460_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1447_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1446_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1444_);
lean_ctor_set(v___x_1432_, 0, v_expr_1443_);
v___x_1462_ = v___x_1432_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_expr_1443_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_exprType_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_exprInit_1446_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_exprResult_1447_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_proof_1460_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*5, v_nondep_1418_);
v___x_1463_ = lean_apply_2(v_toPure_1456_, lean_box(0), v___x_1462_);
return v___x_1463_;
}
}
}
else
{
lean_dec(v___x_1421_);
if (v_modified_1430_ == 0)
{
lean_object* v_toPure_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v_proof_1468_; lean_object* v___x_1470_; 
lean_dec_ref(v___x_1442_);
lean_dec_ref(v_proof_1429_);
lean_dec(v_declName_1413_);
v_toPure_1465_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1465_);
lean_dec_ref(v_toApplicative_1420_);
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1467_ = l_Lean_mkConst(v___x_1466_, v_us_1422_);
lean_inc_ref(v_exprType_1444_);
v_proof_1468_ = l_Lean_mkApp6(v___x_1467_, v_type_1414_, v_exprType_1444_, v_value_1417_, v_fst_1415_, v___x_1445_, v_snd_1423_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1468_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1447_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1446_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1444_);
lean_ctor_set(v___x_1432_, 0, v_expr_1443_);
v___x_1470_ = v___x_1432_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_expr_1443_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_exprType_1444_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_exprInit_1446_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_exprResult_1447_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_proof_1468_);
v___x_1470_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*5, v_nondep_1418_);
v___x_1471_ = lean_apply_2(v_toPure_1465_, lean_box(0), v___x_1470_);
return v___x_1471_;
}
}
else
{
lean_object* v_toPure_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_proof_1477_; lean_object* v___x_1479_; 
v_toPure_1473_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1473_);
lean_dec_ref(v_toApplicative_1420_);
lean_inc_ref(v_type_1414_);
v___x_1474_ = l_Lean_mkLambda(v_declName_1413_, v___x_1441_, v_type_1414_, v_proof_1429_);
v___x_1475_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6));
v___x_1476_ = l_Lean_mkConst(v___x_1475_, v_us_1422_);
lean_inc_ref(v_exprType_1444_);
v_proof_1477_ = l_Lean_mkApp8(v___x_1476_, v_type_1414_, v_exprType_1444_, v_value_1417_, v_fst_1415_, v___x_1445_, v___x_1442_, v_snd_1423_, v___x_1474_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_proof_1477_);
lean_ctor_set(v___x_1432_, 3, v_exprResult_1447_);
lean_ctor_set(v___x_1432_, 2, v_exprInit_1446_);
lean_ctor_set(v___x_1432_, 1, v_exprType_1444_);
lean_ctor_set(v___x_1432_, 0, v_expr_1443_);
v___x_1479_ = v___x_1432_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_expr_1443_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_exprType_1444_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_exprInit_1446_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_exprResult_1447_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_proof_1477_);
v___x_1479_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; 
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*5, v_nondep_1418_);
v___x_1480_ = lean_apply_2(v_toPure_1473_, lean_box(0), v___x_1479_);
return v___x_1480_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_inst_1483_, lean_object* v_declName_1484_, lean_object* v_type_1485_, lean_object* v_fst_1486_, lean_object* v___x_1487_, lean_object* v_value_1488_, lean_object* v_nondep_1489_, lean_object* v_fst_1490_, lean_object* v_toApplicative_1491_, lean_object* v___x_1492_, lean_object* v_us_1493_, lean_object* v_snd_1494_, lean_object* v_rb_1495_){
_start:
{
uint8_t v_nondep_11981__boxed_1496_; uint8_t v_fst_11982__boxed_1497_; lean_object* v_res_1498_; 
v_nondep_11981__boxed_1496_ = lean_unbox(v_nondep_1489_);
v_fst_11982__boxed_1497_ = lean_unbox(v_fst_1490_);
v_res_1498_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_inst_1483_, v_declName_1484_, v_type_1485_, v_fst_1486_, v___x_1487_, v_value_1488_, v_nondep_11981__boxed_1496_, v_fst_11982__boxed_1497_, v_toApplicative_1491_, v___x_1492_, v_us_1493_, v_snd_1494_, v_rb_1495_);
lean_dec(v___x_1487_);
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
v___x_1506_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1507_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1508_ = l_mkPanicMessageWithDecl(v___x_1507_, v___x_1506_, v___x_1505_, v___x_1504_, v___x_1503_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_val_1509_, lean_object* v_val_x27_1510_, lean_object* v_declName_1511_, lean_object* v_type_1512_, lean_object* v_value_1513_, uint8_t v_nondep_1514_, lean_object* v_toApplicative_1515_, lean_object* v___x_1516_, lean_object* v_us_1517_, lean_object* v_decl_1518_, lean_object* v_x_1519_, lean_object* v_i_1520_, lean_object* v_xs_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_info_1526_, lean_object* v_fixed_1527_, lean_object* v_used_1528_, lean_object* v_body_1529_, lean_object* v_toBind_1530_, lean_object* v_withNewLemmas_1531_, lean_object* v_____r_1532_){
_start:
{
uint8_t v___x_1533_; uint8_t v_vModified_1534_; lean_object* v___y_1536_; 
v___x_1533_ = lean_expr_eqv(v_val_1509_, v_val_x27_1510_);
v_vModified_1534_ = lean_bool_not(v___x_1533_);
if (v_vModified_1534_ == 0)
{
lean_inc_ref(v_value_1513_);
v___y_1536_ = v_value_1513_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_expr_abstract(v_val_x27_1510_, v_xs_1521_);
v___y_1536_ = v___x_1551_;
goto v___jp_1535_;
}
v___jp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1537_ = lean_box(v_nondep_1514_);
v___x_1538_ = lean_box(v_vModified_1534_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1539_, 0, v_declName_1511_);
lean_closure_set(v___f_1539_, 1, v_type_1512_);
lean_closure_set(v___f_1539_, 2, v___y_1536_);
lean_closure_set(v___f_1539_, 3, v_value_1513_);
lean_closure_set(v___f_1539_, 4, v___x_1537_);
lean_closure_set(v___f_1539_, 5, v_toApplicative_1515_);
lean_closure_set(v___f_1539_, 6, v___x_1516_);
lean_closure_set(v___f_1539_, 7, v___x_1538_);
lean_closure_set(v___f_1539_, 8, v_us_1517_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_decl_1518_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_mk_empty_array_with_capacity(v___x_1542_);
lean_inc_ref(v_x_1519_);
v___x_1544_ = lean_array_push(v___x_1543_, v_x_1519_);
v___x_1545_ = lean_nat_add(v_i_1520_, v___x_1542_);
v___x_1546_ = lean_array_push(v_xs_1521_, v_x_1519_);
lean_inc_ref(v_inst_1524_);
lean_inc_ref(v_inst_1522_);
v___x_1547_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_info_1526_, v_fixed_1527_, v_used_1528_, v_body_1529_, v___x_1545_, v___x_1546_);
v___x_1548_ = lean_apply_4(v_toBind_1530_, lean_box(0), lean_box(0), v___x_1547_, v___f_1539_);
v___x_1549_ = lean_apply_3(v_withNewLemmas_1531_, lean_box(0), v___x_1544_, v___x_1548_);
v___x_1550_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1524_, v_inst_1522_, v___x_1541_, v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_val_1552_ = _args[0];
lean_object* v_val_x27_1553_ = _args[1];
lean_object* v_declName_1554_ = _args[2];
lean_object* v_type_1555_ = _args[3];
lean_object* v_value_1556_ = _args[4];
lean_object* v_nondep_1557_ = _args[5];
lean_object* v_toApplicative_1558_ = _args[6];
lean_object* v___x_1559_ = _args[7];
lean_object* v_us_1560_ = _args[8];
lean_object* v_decl_1561_ = _args[9];
lean_object* v_x_1562_ = _args[10];
lean_object* v_i_1563_ = _args[11];
lean_object* v_xs_1564_ = _args[12];
lean_object* v_inst_1565_ = _args[13];
lean_object* v_inst_1566_ = _args[14];
lean_object* v_inst_1567_ = _args[15];
lean_object* v_inst_1568_ = _args[16];
lean_object* v_info_1569_ = _args[17];
lean_object* v_fixed_1570_ = _args[18];
lean_object* v_used_1571_ = _args[19];
lean_object* v_body_1572_ = _args[20];
lean_object* v_toBind_1573_ = _args[21];
lean_object* v_withNewLemmas_1574_ = _args[22];
lean_object* v_____r_1575_ = _args[23];
_start:
{
uint8_t v_nondep_12236__boxed_1576_; lean_object* v_res_1577_; 
v_nondep_12236__boxed_1576_ = lean_unbox(v_nondep_1557_);
v_res_1577_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_val_1552_, v_val_x27_1553_, v_declName_1554_, v_type_1555_, v_value_1556_, v_nondep_12236__boxed_1576_, v_toApplicative_1558_, v___x_1559_, v_us_1560_, v_decl_1561_, v_x_1562_, v_i_1563_, v_xs_1564_, v_inst_1565_, v_inst_1566_, v_inst_1567_, v_inst_1568_, v_info_1569_, v_fixed_1570_, v_used_1571_, v_body_1572_, v_toBind_1573_, v_withNewLemmas_1574_, v_____r_1575_);
lean_dec(v_i_1563_);
lean_dec_ref(v_val_x27_1553_);
lean_dec_ref(v_val_1552_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_val_1578_, lean_object* v_declName_1579_, lean_object* v_type_1580_, lean_object* v_value_1581_, uint8_t v_nondep_1582_, lean_object* v_toApplicative_1583_, lean_object* v___x_1584_, lean_object* v_us_1585_, lean_object* v_decl_1586_, lean_object* v_x_1587_, lean_object* v_i_1588_, lean_object* v_xs_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_info_1594_, lean_object* v_fixed_1595_, lean_object* v_used_1596_, lean_object* v_body_1597_, lean_object* v_toBind_1598_, lean_object* v_withNewLemmas_1599_, lean_object* v_val_x27_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v_toApplicative_1602_; lean_object* v_toFunctor_1603_; lean_object* v_toSeq_1604_; lean_object* v_toSeqLeft_1605_; lean_object* v_toSeqRight_1606_; lean_object* v___f_1607_; lean_object* v___f_1608_; lean_object* v___f_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___f_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_toApplicative_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1654_; 
v___x_1601_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1602_ = lean_ctor_get(v___x_1601_, 0);
v_toFunctor_1603_ = lean_ctor_get(v_toApplicative_1602_, 0);
v_toSeq_1604_ = lean_ctor_get(v_toApplicative_1602_, 2);
v_toSeqLeft_1605_ = lean_ctor_get(v_toApplicative_1602_, 3);
v_toSeqRight_1606_ = lean_ctor_get(v_toApplicative_1602_, 4);
v___f_1607_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1608_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1603_, 2);
v___f_1609_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1609_, 0, v_toFunctor_1603_);
v___f_1610_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1610_, 0, v_toFunctor_1603_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___f_1609_);
lean_ctor_set(v___x_1611_, 1, v___f_1610_);
lean_inc(v_toSeqRight_1606_);
v___f_1612_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1612_, 0, v_toSeqRight_1606_);
lean_inc(v_toSeqLeft_1605_);
v___f_1613_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1613_, 0, v_toSeqLeft_1605_);
lean_inc(v_toSeq_1604_);
v___f_1614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1614_, 0, v_toSeq_1604_);
v___x_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1611_);
lean_ctor_set(v___x_1615_, 1, v___f_1607_);
lean_ctor_set(v___x_1615_, 2, v___f_1614_);
lean_ctor_set(v___x_1615_, 3, v___f_1613_);
lean_ctor_set(v___x_1615_, 4, v___f_1612_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___f_1608_);
v___x_1617_ = l_StateRefT_x27_instMonad___redArg(v___x_1616_);
v_toApplicative_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v___x_1617_, 1);
lean_dec(v_unused_1655_);
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1654_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_toApplicative_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1654_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_toFunctor_1622_; lean_object* v_toSeq_1623_; lean_object* v_toSeqLeft_1624_; lean_object* v_toSeqRight_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1652_; 
v_toFunctor_1622_ = lean_ctor_get(v_toApplicative_1618_, 0);
v_toSeq_1623_ = lean_ctor_get(v_toApplicative_1618_, 2);
v_toSeqLeft_1624_ = lean_ctor_get(v_toApplicative_1618_, 3);
v_toSeqRight_1625_ = lean_ctor_get(v_toApplicative_1618_, 4);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_toApplicative_1618_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v_toApplicative_1618_, 1);
lean_dec(v_unused_1653_);
v___x_1627_ = v_toApplicative_1618_;
v_isShared_1628_ = v_isSharedCheck_1652_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_toSeqRight_1625_);
lean_inc(v_toSeqLeft_1624_);
lean_inc(v_toSeq_1623_);
lean_inc(v_toFunctor_1622_);
lean_dec(v_toApplicative_1618_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1652_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___f_1630_; lean_object* v_cls_1631_; lean_object* v___f_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___f_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___x_1641_; 
v___x_1629_ = lean_box(v_nondep_1582_);
lean_inc(v_toBind_1598_);
lean_inc(v_inst_1591_);
lean_inc(v_declName_1579_);
lean_inc_ref(v_val_x27_1600_);
lean_inc_ref(v_val_1578_);
v___f_1630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 24, 23);
lean_closure_set(v___f_1630_, 0, v_val_1578_);
lean_closure_set(v___f_1630_, 1, v_val_x27_1600_);
lean_closure_set(v___f_1630_, 2, v_declName_1579_);
lean_closure_set(v___f_1630_, 3, v_type_1580_);
lean_closure_set(v___f_1630_, 4, v_value_1581_);
lean_closure_set(v___f_1630_, 5, v___x_1629_);
lean_closure_set(v___f_1630_, 6, v_toApplicative_1583_);
lean_closure_set(v___f_1630_, 7, v___x_1584_);
lean_closure_set(v___f_1630_, 8, v_us_1585_);
lean_closure_set(v___f_1630_, 9, v_decl_1586_);
lean_closure_set(v___f_1630_, 10, v_x_1587_);
lean_closure_set(v___f_1630_, 11, v_i_1588_);
lean_closure_set(v___f_1630_, 12, v_xs_1589_);
lean_closure_set(v___f_1630_, 13, v_inst_1590_);
lean_closure_set(v___f_1630_, 14, v_inst_1591_);
lean_closure_set(v___f_1630_, 15, v_inst_1592_);
lean_closure_set(v___f_1630_, 16, v_inst_1593_);
lean_closure_set(v___f_1630_, 17, v_info_1594_);
lean_closure_set(v___f_1630_, 18, v_fixed_1595_);
lean_closure_set(v___f_1630_, 19, v_used_1596_);
lean_closure_set(v___f_1630_, 20, v_body_1597_);
lean_closure_set(v___f_1630_, 21, v_toBind_1598_);
lean_closure_set(v___f_1630_, 22, v_withNewLemmas_1599_);
v_cls_1631_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1632_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1633_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1622_);
v___f_1634_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1634_, 0, v_toFunctor_1622_);
v___f_1635_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1635_, 0, v_toFunctor_1622_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___f_1634_);
lean_ctor_set(v___x_1636_, 1, v___f_1635_);
v___f_1637_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1637_, 0, v_toSeqRight_1625_);
v___f_1638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1638_, 0, v_toSeqLeft_1624_);
v___f_1639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1639_, 0, v_toSeq_1623_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v___f_1637_);
lean_ctor_set(v___x_1627_, 3, v___f_1638_);
lean_ctor_set(v___x_1627_, 2, v___f_1639_);
lean_ctor_set(v___x_1627_, 1, v___f_1632_);
lean_ctor_set(v___x_1627_, 0, v___x_1636_);
v___x_1641_ = v___x_1627_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___f_1632_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v___f_1639_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v___f_1638_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v___f_1637_);
v___x_1641_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___f_1633_);
lean_ctor_set(v___x_1620_, 0, v___x_1641_);
v___x_1643_ = v___x_1620_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v___f_1633_);
v___x_1643_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___f_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___f_1644_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1646_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1647_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1647_, 0, v_cls_1631_);
lean_closure_set(v___f_1647_, 1, v___x_1645_);
lean_closure_set(v___f_1647_, 2, v___f_1644_);
lean_closure_set(v___f_1647_, 3, v_declName_1579_);
lean_closure_set(v___f_1647_, 4, v_val_1578_);
lean_closure_set(v___f_1647_, 5, v_val_x27_1600_);
lean_closure_set(v___f_1647_, 6, v___x_1643_);
lean_closure_set(v___f_1647_, 7, v___x_1646_);
v___x_1648_ = lean_apply_2(v_inst_1591_, lean_box(0), v___f_1647_);
v___x_1649_ = lean_apply_4(v_toBind_1598_, lean_box(0), lean_box(0), v___x_1648_, v___f_1630_);
return v___x_1649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_val_1656_ = _args[0];
lean_object* v_declName_1657_ = _args[1];
lean_object* v_type_1658_ = _args[2];
lean_object* v_value_1659_ = _args[3];
lean_object* v_nondep_1660_ = _args[4];
lean_object* v_toApplicative_1661_ = _args[5];
lean_object* v___x_1662_ = _args[6];
lean_object* v_us_1663_ = _args[7];
lean_object* v_decl_1664_ = _args[8];
lean_object* v_x_1665_ = _args[9];
lean_object* v_i_1666_ = _args[10];
lean_object* v_xs_1667_ = _args[11];
lean_object* v_inst_1668_ = _args[12];
lean_object* v_inst_1669_ = _args[13];
lean_object* v_inst_1670_ = _args[14];
lean_object* v_inst_1671_ = _args[15];
lean_object* v_info_1672_ = _args[16];
lean_object* v_fixed_1673_ = _args[17];
lean_object* v_used_1674_ = _args[18];
lean_object* v_body_1675_ = _args[19];
lean_object* v_toBind_1676_ = _args[20];
lean_object* v_withNewLemmas_1677_ = _args[21];
lean_object* v_val_x27_1678_ = _args[22];
_start:
{
uint8_t v_nondep_12263__boxed_1679_; lean_object* v_res_1680_; 
v_nondep_12263__boxed_1679_ = lean_unbox(v_nondep_1660_);
v_res_1680_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_val_1656_, v_declName_1657_, v_type_1658_, v_value_1659_, v_nondep_12263__boxed_1679_, v_toApplicative_1661_, v___x_1662_, v_us_1663_, v_decl_1664_, v_x_1665_, v_i_1666_, v_xs_1667_, v_inst_1668_, v_inst_1669_, v_inst_1670_, v_inst_1671_, v_info_1672_, v_fixed_1673_, v_used_1674_, v_body_1675_, v_toBind_1676_, v_withNewLemmas_1677_, v_val_x27_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1681_, lean_object* v_inst_1682_, lean_object* v_declName_1683_, lean_object* v_type_1684_, lean_object* v_value_1685_, uint8_t v_nondep_1686_, lean_object* v_toApplicative_1687_, lean_object* v___x_1688_, lean_object* v_us_1689_, lean_object* v_x_1690_, lean_object* v_i_1691_, lean_object* v_xs_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_info_1696_, lean_object* v_fixed_1697_, lean_object* v_used_1698_, lean_object* v_body_1699_, lean_object* v_toBind_1700_, lean_object* v_withNewLemmas_1701_, lean_object* v_____x_1702_){
_start:
{
lean_object* v_snd_1703_; lean_object* v_fst_1704_; lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1725_; 
v_snd_1703_ = lean_ctor_get(v_____x_1702_, 1);
lean_inc(v_snd_1703_);
v_fst_1704_ = lean_ctor_get(v_____x_1702_, 0);
lean_inc(v_fst_1704_);
lean_dec_ref(v_____x_1702_);
v_fst_1705_ = lean_ctor_get(v_snd_1703_, 0);
v_snd_1706_ = lean_ctor_get(v_snd_1703_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_snd_1703_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1708_ = v_snd_1703_;
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1706_);
lean_inc(v_fst_1705_);
lean_dec(v_snd_1703_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
lean_ctor_set(v___x_1708_, 1, v___x_1710_);
lean_ctor_set(v___x_1708_, 0, v_decl_1681_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_decl_1681_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___f_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_box(v_nondep_1686_);
lean_inc_ref_n(v_inst_1682_, 2);
v___f_1715_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1715_, 0, v_inst_1682_);
lean_closure_set(v___f_1715_, 1, v_declName_1683_);
lean_closure_set(v___f_1715_, 2, v_type_1684_);
lean_closure_set(v___f_1715_, 3, v_fst_1704_);
lean_closure_set(v___f_1715_, 4, v___x_1713_);
lean_closure_set(v___f_1715_, 5, v_value_1685_);
lean_closure_set(v___f_1715_, 6, v___x_1714_);
lean_closure_set(v___f_1715_, 7, v_fst_1705_);
lean_closure_set(v___f_1715_, 8, v_toApplicative_1687_);
lean_closure_set(v___f_1715_, 9, v___x_1688_);
lean_closure_set(v___f_1715_, 10, v_us_1689_);
lean_closure_set(v___f_1715_, 11, v_snd_1706_);
v___x_1716_ = lean_mk_empty_array_with_capacity(v___x_1713_);
lean_inc_ref(v_x_1690_);
v___x_1717_ = lean_array_push(v___x_1716_, v_x_1690_);
v___x_1718_ = lean_nat_add(v_i_1691_, v___x_1713_);
v___x_1719_ = lean_array_push(v_xs_1692_, v_x_1690_);
lean_inc_ref(v_inst_1694_);
v___x_1720_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1682_, v_inst_1693_, v_inst_1694_, v_inst_1695_, v_info_1696_, v_fixed_1697_, v_used_1698_, v_body_1699_, v___x_1718_, v___x_1719_);
v___x_1721_ = lean_apply_4(v_toBind_1700_, lean_box(0), lean_box(0), v___x_1720_, v___f_1715_);
v___x_1722_ = lean_apply_3(v_withNewLemmas_1701_, lean_box(0), v___x_1717_, v___x_1721_);
v___x_1723_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1694_, v_inst_1682_, v___x_1712_, v___x_1722_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1726_ = _args[0];
lean_object* v_inst_1727_ = _args[1];
lean_object* v_declName_1728_ = _args[2];
lean_object* v_type_1729_ = _args[3];
lean_object* v_value_1730_ = _args[4];
lean_object* v_nondep_1731_ = _args[5];
lean_object* v_toApplicative_1732_ = _args[6];
lean_object* v___x_1733_ = _args[7];
lean_object* v_us_1734_ = _args[8];
lean_object* v_x_1735_ = _args[9];
lean_object* v_i_1736_ = _args[10];
lean_object* v_xs_1737_ = _args[11];
lean_object* v_inst_1738_ = _args[12];
lean_object* v_inst_1739_ = _args[13];
lean_object* v_inst_1740_ = _args[14];
lean_object* v_info_1741_ = _args[15];
lean_object* v_fixed_1742_ = _args[16];
lean_object* v_used_1743_ = _args[17];
lean_object* v_body_1744_ = _args[18];
lean_object* v_toBind_1745_ = _args[19];
lean_object* v_withNewLemmas_1746_ = _args[20];
lean_object* v_____x_1747_ = _args[21];
_start:
{
uint8_t v_nondep_12210__boxed_1748_; lean_object* v_res_1749_; 
v_nondep_12210__boxed_1748_ = lean_unbox(v_nondep_1731_);
v_res_1749_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1726_, v_inst_1727_, v_declName_1728_, v_type_1729_, v_value_1730_, v_nondep_12210__boxed_1748_, v_toApplicative_1732_, v___x_1733_, v_us_1734_, v_x_1735_, v_i_1736_, v_xs_1737_, v_inst_1738_, v_inst_1739_, v_inst_1740_, v_info_1741_, v_fixed_1742_, v_used_1743_, v_body_1744_, v_toBind_1745_, v_withNewLemmas_1746_, v_____x_1747_);
lean_dec(v_i_1736_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1750_ = _args[0];
lean_object* v_declName_1751_ = _args[1];
lean_object* v_type_1752_ = _args[2];
lean_object* v_value_1753_ = _args[3];
lean_object* v_us_1754_ = _args[4];
lean_object* v___x_1755_ = _args[5];
lean_object* v_toApplicative_1756_ = _args[6];
lean_object* v_nondep_1757_ = _args[7];
lean_object* v_i_1758_ = _args[8];
lean_object* v_xs_1759_ = _args[9];
lean_object* v_inst_1760_ = _args[10];
lean_object* v_inst_1761_ = _args[11];
lean_object* v_inst_1762_ = _args[12];
lean_object* v_inst_1763_ = _args[13];
lean_object* v_info_1764_ = _args[14];
lean_object* v_fixed_1765_ = _args[15];
lean_object* v_used_1766_ = _args[16];
lean_object* v_body_1767_ = _args[17];
lean_object* v_toBind_1768_ = _args[18];
lean_object* v_____r_1769_ = _args[19];
_start:
{
uint8_t v_nondep_12192__boxed_1770_; lean_object* v_res_1771_; 
v_nondep_12192__boxed_1770_ = lean_unbox(v_nondep_1757_);
v_res_1771_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1750_, v_declName_1751_, v_type_1752_, v_value_1753_, v_us_1754_, v___x_1755_, v_toApplicative_1756_, v_nondep_12192__boxed_1770_, v_i_1758_, v_xs_1759_, v_inst_1760_, v_inst_1761_, v_inst_1762_, v_inst_1763_, v_info_1764_, v_fixed_1765_, v_used_1766_, v_body_1767_, v_toBind_1768_, v_____r_1769_);
lean_dec(v_i_1758_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_info_1776_, lean_object* v_fixed_1777_, lean_object* v_used_1778_, lean_object* v_e_1779_, lean_object* v_i_1780_, lean_object* v_xs_1781_){
_start:
{
lean_object* v_haveInfo_1787_; lean_object* v_body_1788_; lean_object* v_bodyType_1789_; lean_object* v_level_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_haveInfo_1787_ = lean_ctor_get(v_info_1776_, 0);
v_body_1788_ = lean_ctor_get(v_info_1776_, 3);
v_bodyType_1789_ = lean_ctor_get(v_info_1776_, 4);
v_level_1790_ = lean_ctor_get(v_info_1776_, 5);
v___x_1791_ = lean_array_get_size(v_haveInfo_1787_);
v___x_1792_ = lean_nat_dec_lt(v_i_1780_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v_toApplicative_1793_; lean_object* v_toBind_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1855_; 
lean_inc(v_level_1790_);
lean_inc_ref(v_bodyType_1789_);
lean_inc_ref(v_body_1788_);
lean_dec(v_i_1780_);
lean_dec_ref(v_used_1778_);
lean_dec_ref(v_fixed_1777_);
lean_dec_ref(v_info_1776_);
lean_dec_ref(v_inst_1774_);
v_toApplicative_1793_ = lean_ctor_get(v_inst_1772_, 0);
v_toBind_1794_ = lean_ctor_get(v_inst_1772_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_inst_1772_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1796_ = v_inst_1772_;
v_isShared_1797_ = v_isSharedCheck_1855_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_toBind_1794_);
lean_inc(v_toApplicative_1793_);
lean_dec(v_inst_1772_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1855_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v_toApplicative_1799_; lean_object* v_toFunctor_1800_; lean_object* v_toSeq_1801_; lean_object* v_toSeqLeft_1802_; lean_object* v_toSeqRight_1803_; lean_object* v___f_1804_; lean_object* v___f_1805_; lean_object* v___f_1806_; lean_object* v___f_1807_; lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___f_1810_; lean_object* v___f_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1798_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1799_ = lean_ctor_get(v___x_1798_, 0);
v_toFunctor_1800_ = lean_ctor_get(v_toApplicative_1799_, 0);
v_toSeq_1801_ = lean_ctor_get(v_toApplicative_1799_, 2);
v_toSeqLeft_1802_ = lean_ctor_get(v_toApplicative_1799_, 3);
v_toSeqRight_1803_ = lean_ctor_get(v_toApplicative_1799_, 4);
v___f_1804_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1805_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1800_, 2);
v___f_1806_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1806_, 0, v_toFunctor_1800_);
v___f_1807_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1807_, 0, v_toFunctor_1800_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___f_1806_);
lean_ctor_set(v___x_1808_, 1, v___f_1807_);
lean_inc(v_toSeqRight_1803_);
v___f_1809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1809_, 0, v_toSeqRight_1803_);
lean_inc(v_toSeqLeft_1802_);
v___f_1810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1810_, 0, v_toSeqLeft_1802_);
lean_inc(v_toSeq_1801_);
v___f_1811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1811_, 0, v_toSeq_1801_);
v___x_1812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1808_);
lean_ctor_set(v___x_1812_, 1, v___f_1804_);
lean_ctor_set(v___x_1812_, 2, v___f_1811_);
lean_ctor_set(v___x_1812_, 3, v___f_1810_);
lean_ctor_set(v___x_1812_, 4, v___f_1809_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___f_1805_);
lean_ctor_set(v___x_1796_, 0, v___x_1812_);
v___x_1814_ = v___x_1796_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___f_1805_);
v___x_1814_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v_toApplicative_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1852_; 
v___x_1815_ = l_StateRefT_x27_instMonad___redArg(v___x_1814_);
v_toApplicative_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v___x_1815_, 1);
lean_dec(v_unused_1853_);
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1852_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_toApplicative_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1852_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_toFunctor_1820_; lean_object* v_toSeq_1821_; lean_object* v_toSeqLeft_1822_; lean_object* v_toSeqRight_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1850_; 
v_toFunctor_1820_ = lean_ctor_get(v_toApplicative_1816_, 0);
v_toSeq_1821_ = lean_ctor_get(v_toApplicative_1816_, 2);
v_toSeqLeft_1822_ = lean_ctor_get(v_toApplicative_1816_, 3);
v_toSeqRight_1823_ = lean_ctor_get(v_toApplicative_1816_, 4);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_toApplicative_1816_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_toApplicative_1816_, 1);
lean_dec(v_unused_1851_);
v___x_1825_ = v_toApplicative_1816_;
v_isShared_1826_ = v_isSharedCheck_1850_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_toSeqRight_1823_);
lean_inc(v_toSeqLeft_1822_);
lean_inc(v_toSeq_1821_);
lean_inc(v_toFunctor_1820_);
lean_dec(v_toApplicative_1816_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1850_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v_cls_1829_; lean_object* v___f_1830_; lean_object* v___f_1831_; lean_object* v___f_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___x_1839_; 
v___x_1827_ = lean_box(v___x_1792_);
lean_inc(v_toBind_1794_);
lean_inc_ref(v_body_1788_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1828_, 0, v_inst_1775_);
lean_closure_set(v___f_1828_, 1, v_bodyType_1789_);
lean_closure_set(v___f_1828_, 2, v_xs_1781_);
lean_closure_set(v___f_1828_, 3, v_toApplicative_1793_);
lean_closure_set(v___f_1828_, 4, v_level_1790_);
lean_closure_set(v___f_1828_, 5, v_e_1779_);
lean_closure_set(v___f_1828_, 6, v___x_1827_);
lean_closure_set(v___f_1828_, 7, v_body_1788_);
lean_closure_set(v___f_1828_, 8, v_toBind_1794_);
v_cls_1829_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1830_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1831_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1820_);
v___f_1832_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1832_, 0, v_toFunctor_1820_);
v___f_1833_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1833_, 0, v_toFunctor_1820_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___f_1832_);
lean_ctor_set(v___x_1834_, 1, v___f_1833_);
v___f_1835_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1835_, 0, v_toSeqRight_1823_);
v___f_1836_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1836_, 0, v_toSeqLeft_1822_);
v___f_1837_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1837_, 0, v_toSeq_1821_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 4, v___f_1835_);
lean_ctor_set(v___x_1825_, 3, v___f_1836_);
lean_ctor_set(v___x_1825_, 2, v___f_1837_);
lean_ctor_set(v___x_1825_, 1, v___f_1830_);
lean_ctor_set(v___x_1825_, 0, v___x_1834_);
v___x_1839_ = v___x_1825_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___f_1830_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v___f_1837_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v___f_1836_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v___f_1835_);
v___x_1839_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___f_1831_);
lean_ctor_set(v___x_1818_, 0, v___x_1839_);
v___x_1841_ = v___x_1818_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___f_1831_);
v___x_1841_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___f_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___f_1842_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1844_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1845_, 0, v_cls_1829_);
lean_closure_set(v___f_1845_, 1, v___x_1843_);
lean_closure_set(v___f_1845_, 2, v___f_1842_);
lean_closure_set(v___f_1845_, 3, v_body_1788_);
lean_closure_set(v___f_1845_, 4, v___x_1841_);
lean_closure_set(v___f_1845_, 5, v___x_1844_);
v___x_1846_ = lean_apply_2(v_inst_1773_, lean_box(0), v___f_1845_);
v___x_1847_ = lean_apply_4(v_toBind_1794_, lean_box(0), lean_box(0), v___x_1846_, v___f_1828_);
return v___x_1847_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_e_1779_) == 8)
{
uint8_t v_nondep_1856_; 
v_nondep_1856_ = lean_ctor_get_uint8(v_e_1779_, sizeof(void*)*4 + 8);
if (v_nondep_1856_ == 1)
{
lean_object* v_declName_1857_; lean_object* v_type_1858_; lean_object* v_value_1859_; lean_object* v_body_1860_; lean_object* v_hinfo_1861_; lean_object* v_decl_1862_; lean_object* v_level_1863_; lean_object* v_x_1864_; lean_object* v_val_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_us_1868_; uint8_t v___y_1879_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_declName_1857_ = lean_ctor_get(v_e_1779_, 0);
lean_inc(v_declName_1857_);
v_type_1858_ = lean_ctor_get(v_e_1779_, 1);
lean_inc_ref(v_type_1858_);
v_value_1859_ = lean_ctor_get(v_e_1779_, 2);
lean_inc_ref(v_value_1859_);
v_body_1860_ = lean_ctor_get(v_e_1779_, 3);
lean_inc_ref(v_body_1860_);
lean_dec_ref_known(v_e_1779_, 4);
v_hinfo_1861_ = lean_array_fget_borrowed(v_haveInfo_1787_, v_i_1780_);
v_decl_1862_ = lean_ctor_get(v_hinfo_1861_, 2);
v_level_1863_ = lean_ctor_get(v_hinfo_1861_, 3);
lean_inc_ref(v_decl_1862_);
v_x_1864_ = l_Lean_LocalDecl_toExpr(v_decl_1862_);
v_val_1865_ = l_Lean_LocalDecl_value(v_decl_1862_, v_nondep_1856_);
v___x_1866_ = lean_box(0);
lean_inc(v_level_1790_);
v___x_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_level_1790_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
lean_inc_ref(v___x_1867_);
lean_inc(v_level_1863_);
v_us_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1868_, 0, v_level_1863_);
lean_ctor_set(v_us_1868_, 1, v___x_1867_);
v___x_1953_ = lean_array_get_size(v_used_1778_);
v___x_1954_ = lean_nat_dec_lt(v_i_1780_, v___x_1953_);
if (v___x_1954_ == 0)
{
v___y_1879_ = v_nondep_1856_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1955_ = lean_array_fget_borrowed(v_used_1778_, v_i_1780_);
v___x_1956_ = lean_unbox(v___x_1955_);
v___y_1879_ = v___x_1956_;
goto v___jp_1878_;
}
v___jp_1869_:
{
lean_object* v_toApplicative_1870_; lean_object* v_toBind_1871_; lean_object* v_withNewLemmas_1872_; lean_object* v_dsimp_1873_; lean_object* v___x_1874_; lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_toApplicative_1870_ = lean_ctor_get(v_inst_1772_, 0);
lean_inc_ref(v_toApplicative_1870_);
v_toBind_1871_ = lean_ctor_get(v_inst_1772_, 1);
lean_inc_n(v_toBind_1871_, 2);
v_withNewLemmas_1872_ = lean_ctor_get(v_inst_1775_, 0);
lean_inc(v_withNewLemmas_1872_);
v_dsimp_1873_ = lean_ctor_get(v_inst_1775_, 1);
lean_inc(v_dsimp_1873_);
v___x_1874_ = lean_box(v_nondep_1856_);
lean_inc_ref(v_val_1865_);
v___f_1875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 23, 22);
lean_closure_set(v___f_1875_, 0, v_val_1865_);
lean_closure_set(v___f_1875_, 1, v_declName_1857_);
lean_closure_set(v___f_1875_, 2, v_type_1858_);
lean_closure_set(v___f_1875_, 3, v_value_1859_);
lean_closure_set(v___f_1875_, 4, v___x_1874_);
lean_closure_set(v___f_1875_, 5, v_toApplicative_1870_);
lean_closure_set(v___f_1875_, 6, v___x_1867_);
lean_closure_set(v___f_1875_, 7, v_us_1868_);
lean_closure_set(v___f_1875_, 8, v_decl_1862_);
lean_closure_set(v___f_1875_, 9, v_x_1864_);
lean_closure_set(v___f_1875_, 10, v_i_1780_);
lean_closure_set(v___f_1875_, 11, v_xs_1781_);
lean_closure_set(v___f_1875_, 12, v_inst_1772_);
lean_closure_set(v___f_1875_, 13, v_inst_1773_);
lean_closure_set(v___f_1875_, 14, v_inst_1774_);
lean_closure_set(v___f_1875_, 15, v_inst_1775_);
lean_closure_set(v___f_1875_, 16, v_info_1776_);
lean_closure_set(v___f_1875_, 17, v_fixed_1777_);
lean_closure_set(v___f_1875_, 18, v_used_1778_);
lean_closure_set(v___f_1875_, 19, v_body_1860_);
lean_closure_set(v___f_1875_, 20, v_toBind_1871_);
lean_closure_set(v___f_1875_, 21, v_withNewLemmas_1872_);
v___x_1876_ = lean_apply_1(v_dsimp_1873_, v_val_1865_);
v___x_1877_ = lean_apply_4(v_toBind_1871_, lean_box(0), lean_box(0), v___x_1876_, v___f_1875_);
return v___x_1877_;
}
v___jp_1878_:
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_bool_not(v___y_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
lean_inc_ref(v_decl_1862_);
v___x_1881_ = lean_array_get_size(v_fixed_1777_);
v___x_1882_ = lean_nat_dec_lt(v_i_1780_, v___x_1881_);
if (v___x_1882_ == 0)
{
goto v___jp_1869_;
}
else
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = lean_array_fget_borrowed(v_fixed_1777_, v_i_1780_);
v___x_1884_ = lean_unbox(v___x_1883_);
if (v___x_1884_ == 0)
{
lean_object* v_toApplicative_1885_; lean_object* v_toBind_1886_; lean_object* v_withNewLemmas_1887_; lean_object* v_simp_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_inc(v___x_1883_);
lean_inc(v_level_1863_);
v_toApplicative_1885_ = lean_ctor_get(v_inst_1772_, 0);
lean_inc_ref_n(v_toApplicative_1885_, 2);
v_toBind_1886_ = lean_ctor_get(v_inst_1772_, 1);
lean_inc_n(v_toBind_1886_, 3);
v_withNewLemmas_1887_ = lean_ctor_get(v_inst_1775_, 0);
lean_inc(v_withNewLemmas_1887_);
v_simp_1888_ = lean_ctor_get(v_inst_1775_, 2);
lean_inc(v_simp_1888_);
v___x_1889_ = lean_box(v_nondep_1856_);
lean_inc(v_inst_1773_);
lean_inc_ref(v_xs_1781_);
lean_inc_ref(v_value_1859_);
lean_inc_ref(v_type_1858_);
lean_inc(v_declName_1857_);
v___f_1890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_1890_, 0, v_decl_1862_);
lean_closure_set(v___f_1890_, 1, v_inst_1772_);
lean_closure_set(v___f_1890_, 2, v_declName_1857_);
lean_closure_set(v___f_1890_, 3, v_type_1858_);
lean_closure_set(v___f_1890_, 4, v_value_1859_);
lean_closure_set(v___f_1890_, 5, v___x_1889_);
lean_closure_set(v___f_1890_, 6, v_toApplicative_1885_);
lean_closure_set(v___f_1890_, 7, v___x_1867_);
lean_closure_set(v___f_1890_, 8, v_us_1868_);
lean_closure_set(v___f_1890_, 9, v_x_1864_);
lean_closure_set(v___f_1890_, 10, v_i_1780_);
lean_closure_set(v___f_1890_, 11, v_xs_1781_);
lean_closure_set(v___f_1890_, 12, v_inst_1773_);
lean_closure_set(v___f_1890_, 13, v_inst_1774_);
lean_closure_set(v___f_1890_, 14, v_inst_1775_);
lean_closure_set(v___f_1890_, 15, v_info_1776_);
lean_closure_set(v___f_1890_, 16, v_fixed_1777_);
lean_closure_set(v___f_1890_, 17, v_used_1778_);
lean_closure_set(v___f_1890_, 18, v_body_1860_);
lean_closure_set(v___f_1890_, 19, v_toBind_1886_);
lean_closure_set(v___f_1890_, 20, v_withNewLemmas_1887_);
v___f_1891_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1891_, 0, v___f_1890_);
v___x_1892_ = lean_box(v_nondep_1856_);
lean_inc_ref(v_val_1865_);
lean_inc_ref(v___f_1891_);
v___f_1893_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_1893_, 0, v_toApplicative_1885_);
lean_closure_set(v___f_1893_, 1, v_level_1863_);
lean_closure_set(v___f_1893_, 2, v___x_1866_);
lean_closure_set(v___f_1893_, 3, v_type_1858_);
lean_closure_set(v___f_1893_, 4, v_value_1859_);
lean_closure_set(v___f_1893_, 5, v___x_1883_);
lean_closure_set(v___f_1893_, 6, v_toBind_1886_);
lean_closure_set(v___f_1893_, 7, v___f_1891_);
lean_closure_set(v___f_1893_, 8, v_xs_1781_);
lean_closure_set(v___f_1893_, 9, v___x_1892_);
lean_closure_set(v___f_1893_, 10, v___f_1891_);
lean_closure_set(v___f_1893_, 11, v_declName_1857_);
lean_closure_set(v___f_1893_, 12, v_val_1865_);
lean_closure_set(v___f_1893_, 13, v_inst_1773_);
v___x_1894_ = lean_apply_1(v_simp_1888_, v_val_1865_);
v___x_1895_ = lean_apply_4(v_toBind_1886_, lean_box(0), lean_box(0), v___x_1894_, v___f_1893_);
return v___x_1895_;
}
else
{
goto v___jp_1869_;
}
}
}
else
{
lean_object* v_toApplicative_1896_; lean_object* v_toBind_1897_; lean_object* v___x_1898_; lean_object* v_toApplicative_1899_; lean_object* v_toFunctor_1900_; lean_object* v_toSeq_1901_; lean_object* v_toSeqLeft_1902_; lean_object* v_toSeqRight_1903_; lean_object* v___f_1904_; lean_object* v___f_1905_; lean_object* v___f_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_toApplicative_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_x_1864_);
v_toApplicative_1896_ = lean_ctor_get(v_inst_1772_, 0);
lean_inc_ref(v_toApplicative_1896_);
v_toBind_1897_ = lean_ctor_get(v_inst_1772_, 1);
lean_inc(v_toBind_1897_);
v___x_1898_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1899_ = lean_ctor_get(v___x_1898_, 0);
v_toFunctor_1900_ = lean_ctor_get(v_toApplicative_1899_, 0);
v_toSeq_1901_ = lean_ctor_get(v_toApplicative_1899_, 2);
v_toSeqLeft_1902_ = lean_ctor_get(v_toApplicative_1899_, 3);
v_toSeqRight_1903_ = lean_ctor_get(v_toApplicative_1899_, 4);
v___f_1904_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1905_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1900_, 2);
v___f_1906_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1906_, 0, v_toFunctor_1900_);
v___f_1907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1907_, 0, v_toFunctor_1900_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___f_1906_);
lean_ctor_set(v___x_1908_, 1, v___f_1907_);
lean_inc(v_toSeqRight_1903_);
v___f_1909_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1909_, 0, v_toSeqRight_1903_);
lean_inc(v_toSeqLeft_1902_);
v___f_1910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1910_, 0, v_toSeqLeft_1902_);
lean_inc(v_toSeq_1901_);
v___f_1911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1911_, 0, v_toSeq_1901_);
v___x_1912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1908_);
lean_ctor_set(v___x_1912_, 1, v___f_1904_);
lean_ctor_set(v___x_1912_, 2, v___f_1911_);
lean_ctor_set(v___x_1912_, 3, v___f_1910_);
lean_ctor_set(v___x_1912_, 4, v___f_1909_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v___f_1905_);
v___x_1914_ = l_StateRefT_x27_instMonad___redArg(v___x_1913_);
v_toApplicative_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1914_, 1);
lean_dec(v_unused_1952_);
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1951_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_toApplicative_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1951_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_toFunctor_1919_; lean_object* v_toSeq_1920_; lean_object* v_toSeqLeft_1921_; lean_object* v_toSeqRight_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1949_; 
v_toFunctor_1919_ = lean_ctor_get(v_toApplicative_1915_, 0);
v_toSeq_1920_ = lean_ctor_get(v_toApplicative_1915_, 2);
v_toSeqLeft_1921_ = lean_ctor_get(v_toApplicative_1915_, 3);
v_toSeqRight_1922_ = lean_ctor_get(v_toApplicative_1915_, 4);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_toApplicative_1915_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v_toApplicative_1915_, 1);
lean_dec(v_unused_1950_);
v___x_1924_ = v_toApplicative_1915_;
v_isShared_1925_ = v_isSharedCheck_1949_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_toSeqRight_1922_);
lean_inc(v_toSeqLeft_1921_);
lean_inc(v_toSeq_1920_);
lean_inc(v_toFunctor_1919_);
lean_dec(v_toApplicative_1915_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1949_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___f_1927_; lean_object* v_cls_1928_; lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___f_1935_; lean_object* v___f_1936_; lean_object* v___x_1938_; 
v___x_1926_ = lean_box(v_nondep_1856_);
lean_inc(v_toBind_1897_);
lean_inc(v_inst_1773_);
lean_inc(v_declName_1857_);
v___f_1927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1927_, 0, v___x_1866_);
lean_closure_set(v___f_1927_, 1, v_declName_1857_);
lean_closure_set(v___f_1927_, 2, v_type_1858_);
lean_closure_set(v___f_1927_, 3, v_value_1859_);
lean_closure_set(v___f_1927_, 4, v_us_1868_);
lean_closure_set(v___f_1927_, 5, v___x_1867_);
lean_closure_set(v___f_1927_, 6, v_toApplicative_1896_);
lean_closure_set(v___f_1927_, 7, v___x_1926_);
lean_closure_set(v___f_1927_, 8, v_i_1780_);
lean_closure_set(v___f_1927_, 9, v_xs_1781_);
lean_closure_set(v___f_1927_, 10, v_inst_1772_);
lean_closure_set(v___f_1927_, 11, v_inst_1773_);
lean_closure_set(v___f_1927_, 12, v_inst_1774_);
lean_closure_set(v___f_1927_, 13, v_inst_1775_);
lean_closure_set(v___f_1927_, 14, v_info_1776_);
lean_closure_set(v___f_1927_, 15, v_fixed_1777_);
lean_closure_set(v___f_1927_, 16, v_used_1778_);
lean_closure_set(v___f_1927_, 17, v_body_1860_);
lean_closure_set(v___f_1927_, 18, v_toBind_1897_);
v_cls_1928_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1929_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1930_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1919_);
v___f_1931_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1931_, 0, v_toFunctor_1919_);
v___f_1932_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1932_, 0, v_toFunctor_1919_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___f_1931_);
lean_ctor_set(v___x_1933_, 1, v___f_1932_);
v___f_1934_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1934_, 0, v_toSeqRight_1922_);
v___f_1935_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1935_, 0, v_toSeqLeft_1921_);
v___f_1936_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1936_, 0, v_toSeq_1920_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 4, v___f_1934_);
lean_ctor_set(v___x_1924_, 3, v___f_1935_);
lean_ctor_set(v___x_1924_, 2, v___f_1936_);
lean_ctor_set(v___x_1924_, 1, v___f_1929_);
lean_ctor_set(v___x_1924_, 0, v___x_1933_);
v___x_1938_ = v___x_1924_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___f_1929_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v___f_1936_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v___f_1935_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v___f_1934_);
v___x_1938_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v___f_1930_);
lean_ctor_set(v___x_1917_, 0, v___x_1938_);
v___x_1940_ = v___x_1917_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___f_1930_);
v___x_1940_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___f_1941_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1942_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1943_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1944_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1944_, 0, v_cls_1928_);
lean_closure_set(v___f_1944_, 1, v___x_1942_);
lean_closure_set(v___f_1944_, 2, v___f_1941_);
lean_closure_set(v___f_1944_, 3, v_declName_1857_);
lean_closure_set(v___f_1944_, 4, v_val_1865_);
lean_closure_set(v___f_1944_, 5, v___x_1940_);
lean_closure_set(v___f_1944_, 6, v___x_1943_);
v___x_1945_ = lean_apply_2(v_inst_1773_, lean_box(0), v___f_1944_);
v___x_1946_ = lean_apply_4(v_toBind_1897_, lean_box(0), lean_box(0), v___x_1945_, v___f_1927_);
return v___x_1946_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1779_, 4);
lean_dec_ref(v_xs_1781_);
lean_dec(v_i_1780_);
lean_dec_ref(v_used_1778_);
lean_dec_ref(v_fixed_1777_);
lean_dec_ref(v_info_1776_);
lean_dec_ref(v_inst_1775_);
lean_dec_ref(v_inst_1774_);
lean_dec(v_inst_1773_);
goto v___jp_1782_;
}
}
else
{
lean_dec_ref(v_xs_1781_);
lean_dec(v_i_1780_);
lean_dec_ref(v_e_1779_);
lean_dec_ref(v_used_1778_);
lean_dec_ref(v_fixed_1777_);
lean_dec_ref(v_info_1776_);
lean_dec_ref(v_inst_1775_);
lean_dec_ref(v_inst_1774_);
lean_dec(v_inst_1773_);
goto v___jp_1782_;
}
}
v___jp_1782_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1783_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1784_ = l_instInhabitedOfMonad___redArg(v_inst_1772_, v___x_1783_);
v___x_1785_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1786_ = l_panic___redArg(v___x_1784_, v___x_1785_);
lean_dec(v___x_1784_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1957_, lean_object* v_declName_1958_, lean_object* v_type_1959_, lean_object* v_value_1960_, lean_object* v_us_1961_, lean_object* v___x_1962_, lean_object* v_toApplicative_1963_, uint8_t v_nondep_1964_, lean_object* v_i_1965_, lean_object* v_xs_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_info_1971_, lean_object* v_fixed_1972_, lean_object* v_used_1973_, lean_object* v_body_1974_, lean_object* v_toBind_1975_, lean_object* v_____r_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v_x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1978_ = l_Lean_mkConst(v___x_1977_, v___x_1957_);
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_box(v_nondep_1964_);
v___f_1981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1981_, 0, v___x_1979_);
lean_closure_set(v___f_1981_, 1, v_declName_1958_);
lean_closure_set(v___f_1981_, 2, v_type_1959_);
lean_closure_set(v___f_1981_, 3, v_value_1960_);
lean_closure_set(v___f_1981_, 4, v_us_1961_);
lean_closure_set(v___f_1981_, 5, v___x_1962_);
lean_closure_set(v___f_1981_, 6, v_toApplicative_1963_);
lean_closure_set(v___f_1981_, 7, v___x_1980_);
v___x_1982_ = lean_nat_add(v_i_1965_, v___x_1979_);
v___x_1983_ = lean_array_push(v_xs_1966_, v_x_1978_);
v___x_1984_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1967_, v_inst_1968_, v_inst_1969_, v_inst_1970_, v_info_1971_, v_fixed_1972_, v_used_1973_, v_body_1974_, v___x_1982_, v___x_1983_);
v___x_1985_ = lean_apply_4(v_toBind_1975_, lean_box(0), lean_box(0), v___x_1984_, v___f_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_info_1991_, lean_object* v_fixed_1992_, lean_object* v_used_1993_, lean_object* v_e_1994_, lean_object* v_i_1995_, lean_object* v_xs_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1987_, v_inst_1988_, v_inst_1989_, v_inst_1990_, v_info_1991_, v_fixed_1992_, v_used_1993_, v_e_1994_, v_i_1995_, v_xs_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_1998_){
_start:
{
switch(v_x_1998_)
{
case 0:
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
return v___x_1999_;
}
case 1:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_unsigned_to_nat(1u);
return v___x_2000_;
}
default: 
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_unsigned_to_nat(2u);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2002_){
_start:
{
uint8_t v_x_boxed_2003_; lean_object* v_res_2004_; 
v_x_boxed_2003_ = lean_unbox(v_x_2002_);
v_res_2004_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2003_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t v_x_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object* v_x_2007_){
_start:
{
uint8_t v_x_4__boxed_2008_; lean_object* v_res_2009_; 
v_x_4__boxed_2008_ = lean_unbox(v_x_2007_);
v_res_2009_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_2008_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2010_){
_start:
{
lean_inc(v_k_2010_);
return v_k_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2011_);
lean_dec(v_k_2011_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2013_, lean_object* v_ctorIdx_2014_, uint8_t v_t_2015_, lean_object* v_h_2016_, lean_object* v_k_2017_){
_start:
{
lean_inc(v_k_2017_);
return v_k_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2018_, lean_object* v_ctorIdx_2019_, lean_object* v_t_2020_, lean_object* v_h_2021_, lean_object* v_k_2022_){
_start:
{
uint8_t v_t_boxed_2023_; lean_object* v_res_2024_; 
v_t_boxed_2023_ = lean_unbox(v_t_2020_);
v_res_2024_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2018_, v_ctorIdx_2019_, v_t_boxed_2023_, v_h_2021_, v_k_2022_);
lean_dec(v_k_2022_);
lean_dec(v_ctorIdx_2019_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2025_){
_start:
{
lean_inc(v_no_2025_);
return v_no_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2026_);
lean_dec(v_no_2026_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2028_, uint8_t v_t_2029_, lean_object* v_h_2030_, lean_object* v_no_2031_){
_start:
{
lean_inc(v_no_2031_);
return v_no_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2032_, lean_object* v_t_2033_, lean_object* v_h_2034_, lean_object* v_no_2035_){
_start:
{
uint8_t v_t_boxed_2036_; lean_object* v_res_2037_; 
v_t_boxed_2036_ = lean_unbox(v_t_2033_);
v_res_2037_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2032_, v_t_boxed_2036_, v_h_2034_, v_no_2035_);
lean_dec(v_no_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2038_){
_start:
{
lean_inc(v_singlePass_2038_);
return v_singlePass_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2039_);
lean_dec(v_singlePass_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2041_, uint8_t v_t_2042_, lean_object* v_h_2043_, lean_object* v_singlePass_2044_){
_start:
{
lean_inc(v_singlePass_2044_);
return v_singlePass_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2045_, lean_object* v_t_2046_, lean_object* v_h_2047_, lean_object* v_singlePass_2048_){
_start:
{
uint8_t v_t_boxed_2049_; lean_object* v_res_2050_; 
v_t_boxed_2049_ = lean_unbox(v_t_2046_);
v_res_2050_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2045_, v_t_boxed_2049_, v_h_2047_, v_singlePass_2048_);
lean_dec(v_singlePass_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2051_){
_start:
{
lean_inc(v_twoPasses_2051_);
return v_twoPasses_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2052_);
lean_dec(v_twoPasses_2052_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2054_, uint8_t v_t_2055_, lean_object* v_h_2056_, lean_object* v_twoPasses_2057_){
_start:
{
lean_inc(v_twoPasses_2057_);
return v_twoPasses_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2058_, lean_object* v_t_2059_, lean_object* v_h_2060_, lean_object* v_twoPasses_2061_){
_start:
{
uint8_t v_t_boxed_2062_; lean_object* v_res_2063_; 
v_t_boxed_2062_ = lean_unbox(v_t_2059_);
v_res_2063_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2058_, v_t_boxed_2062_, v_h_2060_, v_twoPasses_2061_);
lean_dec(v_twoPasses_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2064_, lean_object* v_b_2065_, lean_object* v_c_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2072_; 
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
v___x_2072_ = lean_apply_7(v_k_2064_, v_b_2065_, v_c_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, lean_box(0));
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2073_, lean_object* v_b_2074_, lean_object* v_c_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2073_, v_b_2074_, v_c_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2082_, lean_object* v_k_2083_, uint8_t v_cleanupAnnotations_2084_, uint8_t v_preserveNondepLet_2085_, uint8_t v_nondepLetOnly_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___f_2092_; uint8_t v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2092_, 0, v_k_2083_);
v___x_2093_ = 0;
v___x_2094_ = 1;
v___x_2095_ = lean_box(0);
v___x_2096_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2082_, v___x_2093_, v___x_2094_, v_preserveNondepLet_2085_, v_nondepLetOnly_2086_, v___x_2095_, v___f_2092_, v_cleanupAnnotations_2084_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2096_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2096_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2113_, lean_object* v_k_2114_, lean_object* v_cleanupAnnotations_2115_, lean_object* v_preserveNondepLet_2116_, lean_object* v_nondepLetOnly_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2123_; uint8_t v_preserveNondepLet_boxed_2124_; uint8_t v_nondepLetOnly_boxed_2125_; lean_object* v_res_2126_; 
v_cleanupAnnotations_boxed_2123_ = lean_unbox(v_cleanupAnnotations_2115_);
v_preserveNondepLet_boxed_2124_ = lean_unbox(v_preserveNondepLet_2116_);
v_nondepLetOnly_boxed_2125_ = lean_unbox(v_nondepLetOnly_2117_);
v_res_2126_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2113_, v_k_2114_, v_cleanupAnnotations_boxed_2123_, v_preserveNondepLet_boxed_2124_, v_nondepLetOnly_boxed_2125_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2127_, lean_object* v_e_2128_, lean_object* v_k_2129_, uint8_t v_cleanupAnnotations_2130_, uint8_t v_preserveNondepLet_2131_, uint8_t v_nondepLetOnly_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2128_, v_k_2129_, v_cleanupAnnotations_2130_, v_preserveNondepLet_2131_, v_nondepLetOnly_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_e_2140_, lean_object* v_k_2141_, lean_object* v_cleanupAnnotations_2142_, lean_object* v_preserveNondepLet_2143_, lean_object* v_nondepLetOnly_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2150_; uint8_t v_preserveNondepLet_boxed_2151_; uint8_t v_nondepLetOnly_boxed_2152_; lean_object* v_res_2153_; 
v_cleanupAnnotations_boxed_2150_ = lean_unbox(v_cleanupAnnotations_2142_);
v_preserveNondepLet_boxed_2151_ = lean_unbox(v_preserveNondepLet_2143_);
v_nondepLetOnly_boxed_2152_ = lean_unbox(v_nondepLetOnly_2144_);
v_res_2153_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2139_, v_e_2140_, v_k_2141_, v_cleanupAnnotations_boxed_2150_, v_preserveNondepLet_boxed_2151_, v_nondepLetOnly_boxed_2152_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2154_, lean_object* v_a_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_snd_2160_; lean_object* v_fst_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2216_; 
v_snd_2160_ = lean_ctor_get(v_a_2155_, 1);
v_fst_2161_ = lean_ctor_get(v_a_2155_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2163_ = v_a_2155_;
v_isShared_2164_ = v_isSharedCheck_2216_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_snd_2160_);
lean_inc(v_fst_2161_);
lean_dec(v_a_2155_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2216_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_fst_2165_; lean_object* v_snd_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2215_; 
v_fst_2165_ = lean_ctor_get(v_snd_2160_, 0);
v_snd_2166_ = lean_ctor_get(v_snd_2160_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_snd_2160_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2168_ = v_snd_2160_;
v_isShared_2169_ = v_isSharedCheck_2215_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_snd_2166_);
lean_inc(v_fst_2165_);
lean_dec(v_snd_2160_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2215_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_nat_dec_lt(v___x_2170_, v_snd_2166_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2173_; 
if (v_isShared_2169_ == 0)
{
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_fst_2165_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_snd_2166_);
v___x_2173_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2173_);
v___x_2175_ = v___x_2163_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_fst_2161_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
}
}
else
{
lean_object* v_fvarSet_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v_fvarSet_2179_ = lean_ctor_get(v_fst_2161_, 1);
v___x_2180_ = lean_unsigned_to_nat(1u);
v___x_2181_ = lean_nat_sub(v_snd_2166_, v___x_2180_);
lean_dec(v_snd_2166_);
v___x_2182_ = l_Lean_instInhabitedExpr;
v___x_2183_ = lean_array_get_borrowed(v___x_2182_, v_xs_2154_, v___x_2181_);
v___x_2184_ = l_Lean_Expr_fvarId_x21(v___x_2183_);
v___x_2185_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2184_, v_fvarSet_2179_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v___x_2184_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2181_);
v___x_2187_ = v___x_2168_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_fst_2165_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v___x_2181_);
v___x_2187_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2187_);
v___x_2189_ = v___x_2163_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_fst_2161_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
v_a_2155_ = v___x_2189_;
goto _start;
}
}
}
else
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_FVarId_getDecl___redArg(v___x_2184_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v___x_2195_ = l_Lean_LocalDecl_type(v_a_2194_);
v___x_2196_ = l_Lean_collectFVars(v_fst_2161_, v___x_2195_);
v___x_2197_ = l_Lean_LocalDecl_value(v_a_2194_, v___x_2185_);
lean_dec(v_a_2194_);
v___x_2198_ = l_Lean_collectFVars(v___x_2196_, v___x_2197_);
lean_inc(v___x_2183_);
v___x_2199_ = lean_array_push(v_fst_2165_, v___x_2183_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2181_);
lean_ctor_set(v___x_2168_, 0, v___x_2199_);
v___x_2201_ = v___x_2168_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2181_);
v___x_2201_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2201_);
lean_ctor_set(v___x_2163_, 0, v___x_2198_);
v___x_2203_ = v___x_2163_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
v_a_2155_ = v___x_2203_;
goto _start;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v___x_2181_);
lean_del_object(v___x_2168_);
lean_dec(v_fst_2165_);
lean_del_object(v___x_2163_);
lean_dec(v_fst_2161_);
v_a_2207_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2193_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2193_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2217_, lean_object* v_a_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2217_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec_ref(v_xs_2217_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2224_, lean_object* v_e_2225_, lean_object* v_xs_2226_, lean_object* v_body_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_s_2236_; lean_object* v_i_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2234_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2224_);
lean_ctor_set(v___x_2235_, 2, v___x_2234_);
lean_inc_ref(v_body_2227_);
v_s_2236_ = l_Lean_collectFVars(v___x_2235_, v_body_2227_);
v_i_2237_ = lean_array_get_size(v_xs_2226_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2234_);
lean_ctor_set(v___x_2238_, 1, v_i_2237_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_s_2236_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2226_, v___x_2239_, v___y_2228_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2256_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2256_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2256_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_snd_2245_; lean_object* v_fst_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_snd_2245_ = lean_ctor_get(v_a_2241_, 1);
lean_inc(v_snd_2245_);
lean_dec(v_a_2241_);
v_fst_2246_ = lean_ctor_get(v_snd_2245_, 0);
lean_inc(v_fst_2246_);
lean_dec(v_snd_2245_);
v___x_2247_ = lean_array_get_size(v_fst_2246_);
v___x_2248_ = lean_nat_dec_eq(v___x_2247_, v_i_2237_);
if (v___x_2248_ == 0)
{
uint8_t v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
lean_del_object(v___x_2243_);
lean_dec_ref(v_e_2225_);
v___x_2249_ = 1;
v___x_2250_ = l_Array_reverse___redArg(v_fst_2246_);
v___x_2251_ = 1;
v___x_2252_ = l_Lean_Meta_mkLetFVars(v___x_2250_, v_body_2227_, v___x_2249_, v___x_2248_, v___x_2251_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec_ref(v___x_2250_);
return v___x_2252_;
}
else
{
lean_object* v___x_2254_; 
lean_dec(v_fst_2246_);
lean_dec_ref(v_body_2227_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v_e_2225_);
v___x_2254_ = v___x_2243_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_e_2225_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_body_2227_);
lean_dec_ref(v_e_2225_);
v_a_2257_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2240_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2240_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2265_, lean_object* v_e_2266_, lean_object* v_xs_2267_, lean_object* v_body_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2265_, v_e_2266_, v_xs_2267_, v_body_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_xs_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v___f_2282_; uint8_t v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2281_ = lean_box(1);
lean_inc_ref(v_e_2275_);
v___f_2282_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2282_, 0, v___x_2281_);
lean_closure_set(v___f_2282_, 1, v_e_2275_);
v___x_2283_ = 0;
v___x_2284_ = 1;
v___x_2285_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2275_, v___f_2282_, v___x_2283_, v___x_2284_, v___x_2283_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Meta_zetaUnused(v_e_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2293_, lean_object* v_inst_2294_, lean_object* v_a_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2293_, v_a_2295_, v___y_2296_, v___y_2298_, v___y_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2302_, lean_object* v_inst_2303_, lean_object* v_a_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2302_, v_inst_2303_, v_a_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v_xs_2302_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2315_, lean_object* v_source_2316_, lean_object* v_result_2317_, uint8_t v_keepUnused_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
uint8_t v_modified_2324_; 
v_modified_2324_ = lean_ctor_get_uint8(v_result_2317_, sizeof(void*)*5);
if (v_modified_2324_ == 0)
{
if (v_keepUnused_2318_ == 0)
{
lean_object* v_exprType_2325_; lean_object* v___x_2326_; 
v_exprType_2325_ = lean_ctor_get(v_result_2317_, 1);
lean_inc_ref(v_exprType_2325_);
lean_dec_ref(v_result_2317_);
lean_inc_ref(v_source_2316_);
v___x_2326_ = l_Lean_Meta_zetaUnused(v_source_2316_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2345_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_expr_eqv(v_a_2327_, v_source_2316_);
lean_dec_ref(v_source_2316_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_u_2315_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_mkConst(v___x_2332_, v___x_2334_);
lean_inc(v_a_2327_);
v___x_2336_ = l_Lean_mkAppB(v___x_2335_, v_exprType_2325_, v_a_2327_);
v___x_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_a_2327_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2337_);
v___x_2339_ = v___x_2329_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
lean_dec(v_a_2327_);
lean_dec_ref(v_exprType_2325_);
lean_dec(v_u_2315_);
v___x_2341_ = lean_box(0);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2341_);
v___x_2343_ = v___x_2329_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v_exprType_2325_);
lean_dec_ref(v_source_2316_);
lean_dec(v_u_2315_);
v_a_2346_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2326_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2326_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec_ref(v_result_2317_);
lean_dec_ref(v_source_2316_);
lean_dec(v_u_2315_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
else
{
lean_object* v_expr_2356_; lean_object* v_exprType_2357_; lean_object* v_exprInit_2358_; lean_object* v_exprResult_2359_; lean_object* v_proof_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_proof_2368_; 
v_expr_2356_ = lean_ctor_get(v_result_2317_, 0);
lean_inc_ref(v_expr_2356_);
v_exprType_2357_ = lean_ctor_get(v_result_2317_, 1);
lean_inc_ref_n(v_exprType_2357_, 3);
v_exprInit_2358_ = lean_ctor_get(v_result_2317_, 2);
lean_inc_ref(v_exprInit_2358_);
v_exprResult_2359_ = lean_ctor_get(v_result_2317_, 3);
lean_inc_ref_n(v_exprResult_2359_, 2);
v_proof_2360_ = lean_ctor_get(v_result_2317_, 4);
lean_inc_ref(v_proof_2360_);
lean_dec_ref(v_result_2317_);
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2363_, 0, v_u_2315_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
lean_inc_ref(v___x_2363_);
v___x_2364_ = l_Lean_mkConst(v___x_2361_, v___x_2363_);
lean_inc_ref(v___x_2364_);
v___x_2365_ = l_Lean_mkApp3(v___x_2364_, v_exprType_2357_, v_exprInit_2358_, v_expr_2356_);
v___x_2366_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2360_, v___x_2365_);
lean_inc_ref(v_source_2316_);
v___x_2367_ = l_Lean_mkApp3(v___x_2364_, v_exprType_2357_, v_source_2316_, v_exprResult_2359_);
v_proof_2368_ = l_Lean_Meta_mkExpectedPropHint(v___x_2366_, v___x_2367_);
if (v_keepUnused_2318_ == 0)
{
lean_object* v___x_2369_; 
lean_inc_ref(v_exprResult_2359_);
v___x_2369_ = l_Lean_Meta_zetaUnused(v_exprResult_2359_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2389_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2389_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2389_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_expr_eqv(v_a_2370_, v_exprResult_2359_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2363_);
v___x_2376_ = l_Lean_mkConst(v___x_2375_, v___x_2363_);
v___x_2377_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2378_ = l_Lean_mkConst(v___x_2377_, v___x_2363_);
lean_inc_n(v_a_2370_, 2);
lean_inc_ref(v_exprType_2357_);
v___x_2379_ = l_Lean_mkAppB(v___x_2378_, v_exprType_2357_, v_a_2370_);
v___x_2380_ = l_Lean_mkApp6(v___x_2376_, v_exprType_2357_, v_source_2316_, v_exprResult_2359_, v_a_2370_, v_proof_2368_, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2370_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2381_);
v___x_2383_ = v___x_2372_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec(v_a_2370_);
lean_dec_ref_known(v___x_2363_, 2);
lean_dec_ref(v_exprType_2357_);
lean_dec_ref(v_source_2316_);
v___x_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_exprResult_2359_);
lean_ctor_set(v___x_2385_, 1, v_proof_2368_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2385_);
v___x_2387_ = v___x_2372_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_proof_2368_);
lean_dec_ref_known(v___x_2363_, 2);
lean_dec_ref(v_exprResult_2359_);
lean_dec_ref(v_exprType_2357_);
lean_dec_ref(v_source_2316_);
v_a_2390_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2369_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2369_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec_ref_known(v___x_2363_, 2);
lean_dec_ref(v_exprType_2357_);
lean_dec_ref(v_source_2316_);
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_exprResult_2359_);
lean_ctor_set(v___x_2398_, 1, v_proof_2368_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2400_, lean_object* v_source_2401_, lean_object* v_result_2402_, lean_object* v_keepUnused_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
uint8_t v_keepUnused_boxed_2409_; lean_object* v_res_2410_; 
v_keepUnused_boxed_2409_ = lean_unbox(v_keepUnused_2403_);
v_res_2410_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2400_, v_source_2401_, v_result_2402_, v_keepUnused_boxed_2409_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2411_, lean_object* v_e_2412_, lean_object* v_inst_2413_, uint8_t v_zetaUnusedMode_2414_, uint8_t v___x_2415_, lean_object* v_r_2416_){
_start:
{
uint8_t v___y_2418_; 
switch(v_zetaUnusedMode_2414_)
{
case 0:
{
v___y_2418_ = v___x_2415_;
goto v___jp_2417_;
}
case 1:
{
v___y_2418_ = v___x_2415_;
goto v___jp_2417_;
}
default: 
{
uint8_t v___x_2422_; 
v___x_2422_ = 0;
v___y_2418_ = v___x_2422_;
goto v___jp_2417_;
}
}
v___jp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = lean_box(v___y_2418_);
v___x_2420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2420_, 0, v_level_2411_);
lean_closure_set(v___x_2420_, 1, v_e_2412_);
lean_closure_set(v___x_2420_, 2, v_r_2416_);
lean_closure_set(v___x_2420_, 3, v___x_2419_);
v___x_2421_ = lean_apply_2(v_inst_2413_, lean_box(0), v___x_2420_);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2423_, lean_object* v_e_2424_, lean_object* v_inst_2425_, lean_object* v_zetaUnusedMode_2426_, lean_object* v___x_2427_, lean_object* v_r_2428_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2429_; uint8_t v___x_289__boxed_2430_; lean_object* v_res_2431_; 
v_zetaUnusedMode_boxed_2429_ = lean_unbox(v_zetaUnusedMode_2426_);
v___x_289__boxed_2430_ = lean_unbox(v___x_2427_);
v_res_2431_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2423_, v_e_2424_, v_inst_2425_, v_zetaUnusedMode_boxed_2429_, v___x_289__boxed_2430_, v_r_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_info_2437_, lean_object* v_e_2438_, lean_object* v___x_2439_, lean_object* v_toBind_2440_, lean_object* v___f_2441_, lean_object* v_____x_2442_){
_start:
{
lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_fst_2443_ = lean_ctor_get(v_____x_2442_, 0);
lean_inc(v_fst_2443_);
v_snd_2444_ = lean_ctor_get(v_____x_2442_, 1);
lean_inc(v_snd_2444_);
lean_dec_ref(v_____x_2442_);
v___x_2445_ = lean_mk_empty_array_with_capacity(v___x_2432_);
v___x_2446_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_, v_info_2437_, v_fst_2443_, v_snd_2444_, v_e_2438_, v___x_2439_, v___x_2445_);
v___x_2447_ = lean_apply_4(v_toBind_2440_, lean_box(0), lean_box(0), v___x_2446_, v___f_2441_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_info_2453_, lean_object* v_e_2454_, lean_object* v___x_2455_, lean_object* v_toBind_2456_, lean_object* v___f_2457_, lean_object* v_____x_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2448_, v_inst_2449_, v_inst_2450_, v_inst_2451_, v_inst_2452_, v_info_2453_, v_e_2454_, v___x_2455_, v_toBind_2456_, v___f_2457_, v_____x_2458_);
lean_dec(v___x_2448_);
return v_res_2459_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2462_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2463_ = lean_unsigned_to_nat(2u);
v___x_2464_ = lean_unsigned_to_nat(456u);
v___x_2465_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_2467_ = l_mkPanicMessageWithDecl(v___x_2466_, v___x_2465_, v___x_2464_, v___x_2463_, v___x_2462_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_inst_2468_, lean_object* v_e_2469_, lean_object* v_inst_2470_, uint8_t v_zetaUnusedMode_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_toBind_2474_, lean_object* v_info_2475_){
_start:
{
lean_object* v_haveInfo_2476_; lean_object* v_level_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; uint8_t v___x_2481_; 
v_haveInfo_2476_ = lean_ctor_get(v_info_2475_, 0);
v_level_2477_ = lean_ctor_get(v_info_2475_, 5);
v___x_2478_ = lean_array_get_size(v_haveInfo_2476_);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = lean_nat_dec_eq(v___x_2478_, v___x_2479_);
v___x_2481_ = lean_bool_not(v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref(v_info_2475_);
lean_dec(v_toBind_2474_);
lean_dec_ref(v_inst_2473_);
lean_dec_ref(v_inst_2472_);
lean_dec(v_inst_2470_);
lean_dec_ref(v_e_2469_);
v___x_2482_ = lean_box(0);
v___x_2483_ = l_instInhabitedOfMonad___redArg(v_inst_2468_, v___x_2482_);
v___x_2484_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2485_ = l_panic___redArg(v___x_2483_, v___x_2484_);
lean_dec(v___x_2483_);
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; uint8_t v___y_2491_; 
v___x_2486_ = lean_box(v_zetaUnusedMode_2471_);
v___x_2487_ = lean_box(v___x_2481_);
lean_inc_n(v_inst_2470_, 2);
lean_inc_ref(v_e_2469_);
lean_inc(v_level_2477_);
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2488_, 0, v_level_2477_);
lean_closure_set(v___f_2488_, 1, v_e_2469_);
lean_closure_set(v___f_2488_, 2, v_inst_2470_);
lean_closure_set(v___f_2488_, 3, v___x_2486_);
lean_closure_set(v___f_2488_, 4, v___x_2487_);
lean_inc(v_toBind_2474_);
lean_inc_ref(v_info_2475_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2489_, 0, v___x_2478_);
lean_closure_set(v___f_2489_, 1, v_inst_2468_);
lean_closure_set(v___f_2489_, 2, v_inst_2470_);
lean_closure_set(v___f_2489_, 3, v_inst_2472_);
lean_closure_set(v___f_2489_, 4, v_inst_2473_);
lean_closure_set(v___f_2489_, 5, v_info_2475_);
lean_closure_set(v___f_2489_, 6, v_e_2469_);
lean_closure_set(v___f_2489_, 7, v___x_2479_);
lean_closure_set(v___f_2489_, 8, v_toBind_2474_);
lean_closure_set(v___f_2489_, 9, v___f_2488_);
switch(v_zetaUnusedMode_2471_)
{
case 0:
{
v___y_2491_ = v___x_2481_;
goto v___jp_2490_;
}
case 2:
{
v___y_2491_ = v___x_2481_;
goto v___jp_2490_;
}
default: 
{
uint8_t v___x_2496_; 
v___x_2496_ = 0;
v___y_2491_ = v___x_2496_;
goto v___jp_2490_;
}
}
v___jp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2492_ = lean_box(v___y_2491_);
v___x_2493_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2493_, 0, v_info_2475_);
lean_closure_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_apply_2(v_inst_2470_, lean_box(0), v___x_2493_);
v___x_2495_ = lean_apply_4(v_toBind_2474_, lean_box(0), lean_box(0), v___x_2494_, v___f_2489_);
return v___x_2495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_inst_2497_, lean_object* v_e_2498_, lean_object* v_inst_2499_, lean_object* v_zetaUnusedMode_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_toBind_2503_, lean_object* v_info_2504_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2505_; lean_object* v_res_2506_; 
v_zetaUnusedMode_boxed_2505_ = lean_unbox(v_zetaUnusedMode_2500_);
v_res_2506_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_inst_2497_, v_e_2498_, v_inst_2499_, v_zetaUnusedMode_boxed_2505_, v_inst_2501_, v_inst_2502_, v_toBind_2503_, v_info_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_e_2511_, uint8_t v_zetaUnusedMode_2512_){
_start:
{
lean_object* v_toBind_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_toBind_2513_ = lean_ctor_get(v_inst_2507_, 1);
lean_inc_n(v_toBind_2513_, 2);
v___x_2514_ = lean_box(v_zetaUnusedMode_2512_);
lean_inc(v_inst_2508_);
lean_inc_ref(v_e_2511_);
v___f_2515_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2515_, 0, v_inst_2507_);
lean_closure_set(v___f_2515_, 1, v_e_2511_);
lean_closure_set(v___f_2515_, 2, v_inst_2508_);
lean_closure_set(v___f_2515_, 3, v___x_2514_);
lean_closure_set(v___f_2515_, 4, v_inst_2509_);
lean_closure_set(v___f_2515_, 5, v_inst_2510_);
lean_closure_set(v___f_2515_, 6, v_toBind_2513_);
v___x_2516_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2516_, 0, v_e_2511_);
v___x_2517_ = lean_apply_2(v_inst_2508_, lean_box(0), v___x_2516_);
v___x_2518_ = lean_apply_4(v_toBind_2513_, lean_box(0), lean_box(0), v___x_2517_, v___f_2515_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_e_2523_, lean_object* v_zetaUnusedMode_2524_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2525_; lean_object* v_res_2526_; 
v_zetaUnusedMode_boxed_2525_ = lean_unbox(v_zetaUnusedMode_2524_);
v_res_2526_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2519_, v_inst_2520_, v_inst_2521_, v_inst_2522_, v_e_2523_, v_zetaUnusedMode_boxed_2525_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2527_, lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_e_2532_, uint8_t v_zetaUnusedMode_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2528_, v_inst_2529_, v_inst_2530_, v_inst_2531_, v_e_2532_, v_zetaUnusedMode_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2535_, lean_object* v_inst_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_e_2540_, lean_object* v_zetaUnusedMode_2541_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2542_; lean_object* v_res_2543_; 
v_zetaUnusedMode_boxed_2542_ = lean_unbox(v_zetaUnusedMode_2541_);
v_res_2543_ = l_Lean_Meta_simpHaveTelescope(v_m_2535_, v_inst_2536_, v_inst_2537_, v_inst_2538_, v_inst_2539_, v_e_2540_, v_zetaUnusedMode_boxed_2542_);
return v_res_2543_;
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
