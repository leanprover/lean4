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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12;
static const lean_closure_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_nbuckets_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_116_ = lean_array_get_size(v_data_115_);
v___x_117_ = lean_unsigned_to_nat(2u);
v_nbuckets_118_ = lean_nat_mul(v___x_116_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_box(0);
v___x_121_ = lean_mk_array(v_nbuckets_118_, v___x_120_);
v___x_122_ = lean_array_propagate_mark(v_data_115_, v___x_121_);
v___x_123_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v___x_119_, v_data_115_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object* v_a_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
else
{
lean_object* v_key_127_; lean_object* v_tail_128_; uint8_t v___x_129_; 
v_key_127_ = lean_ctor_get(v_x_125_, 0);
v_tail_128_ = lean_ctor_get(v_x_125_, 2);
v___x_129_ = lean_nat_dec_eq(v_key_127_, v_a_124_);
if (v___x_129_ == 0)
{
v_x_125_ = v_tail_128_;
goto _start;
}
else
{
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object* v_a_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_131_, v_x_132_);
lean_dec(v_x_132_);
lean_dec(v_a_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object* v_m_135_, lean_object* v_a_136_, lean_object* v_b_137_){
_start:
{
lean_object* v_size_138_; lean_object* v_buckets_139_; lean_object* v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v_fold_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; lean_object* v_bkt_153_; uint8_t v___x_154_; 
v_size_138_ = lean_ctor_get(v_m_135_, 0);
v_buckets_139_ = lean_ctor_get(v_m_135_, 1);
v___x_140_ = lean_array_get_size(v_buckets_139_);
v___x_141_ = lean_uint64_of_nat(v_a_136_);
v___x_142_ = 32ULL;
v___x_143_ = lean_uint64_shift_right(v___x_141_, v___x_142_);
v_fold_144_ = lean_uint64_xor(v___x_141_, v___x_143_);
v___x_145_ = 16ULL;
v___x_146_ = lean_uint64_shift_right(v_fold_144_, v___x_145_);
v___x_147_ = lean_uint64_xor(v_fold_144_, v___x_146_);
v___x_148_ = lean_uint64_to_usize(v___x_147_);
v___x_149_ = lean_usize_of_nat(v___x_140_);
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_sub(v___x_149_, v___x_150_);
v___x_152_ = lean_usize_land(v___x_148_, v___x_151_);
v_bkt_153_ = lean_array_uget_borrowed(v_buckets_139_, v___x_152_);
v___x_154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_136_, v_bkt_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_175_; 
lean_inc_ref(v_buckets_139_);
lean_inc(v_size_138_);
v_isSharedCheck_175_ = !lean_is_exclusive(v_m_135_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; lean_object* v_unused_177_; 
v_unused_176_ = lean_ctor_get(v_m_135_, 1);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_m_135_, 0);
lean_dec(v_unused_177_);
v___x_156_ = v_m_135_;
v_isShared_157_ = v_isSharedCheck_175_;
goto v_resetjp_155_;
}
else
{
lean_dec(v_m_135_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_175_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_size_x27_159_; lean_object* v___x_160_; lean_object* v_buckets_x27_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v_size_x27_159_ = lean_nat_add(v_size_138_, v___x_158_);
lean_dec(v_size_138_);
lean_inc(v_bkt_153_);
v___x_160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_160_, 0, v_a_136_);
lean_ctor_set(v___x_160_, 1, v_b_137_);
lean_ctor_set(v___x_160_, 2, v_bkt_153_);
v_buckets_x27_161_ = lean_array_uset(v_buckets_139_, v___x_152_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_mul(v_size_x27_159_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(3u);
v___x_165_ = lean_nat_div(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_array_get_size(v_buckets_x27_161_);
v___x_167_ = lean_nat_dec_le(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
if (v___x_167_ == 0)
{
lean_object* v_val_168_; lean_object* v___x_170_; 
v_val_168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_buckets_x27_161_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_val_168_);
lean_ctor_set(v___x_156_, 0, v_size_x27_159_);
v___x_170_ = v___x_156_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_159_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_val_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_173_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_buckets_x27_161_);
lean_ctor_set(v___x_156_, 0, v_size_x27_159_);
v___x_173_ = v___x_156_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_size_x27_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_buckets_x27_161_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_dec(v_b_137_);
lean_dec(v_a_136_);
return v_m_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object* v_numHaves_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
return v_x_179_;
}
else
{
lean_object* v_key_181_; lean_object* v_tail_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_key_181_ = lean_ctor_get(v_x_180_, 0);
v_tail_182_ = lean_ctor_get(v_x_180_, 2);
v___x_183_ = lean_nat_sub(v_numHaves_178_, v_key_181_);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_sub(v___x_183_, v___x_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_x_179_, v___x_185_, v___x_186_);
v_x_179_ = v___x_187_;
v_x_180_ = v_tail_182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object* v_numHaves_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_189_, v_x_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec(v_numHaves_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object* v_numHaves_193_, lean_object* v_as_194_, size_t v_i_195_, size_t v_stop_196_, lean_object* v_b_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = lean_usize_dec_eq(v_i_195_, v_stop_196_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; size_t v___x_201_; size_t v___x_202_; 
v___x_199_ = lean_array_uget_borrowed(v_as_194_, v_i_195_);
v___x_200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_193_, v_b_197_, v___x_199_);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_add(v_i_195_, v___x_201_);
v_i_195_ = v___x_202_;
v_b_197_ = v___x_200_;
goto _start;
}
else
{
return v_b_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2___boxed(lean_object* v_numHaves_204_, lean_object* v_as_205_, lean_object* v_i_206_, lean_object* v_stop_207_, lean_object* v_b_208_){
_start:
{
size_t v_i_boxed_209_; size_t v_stop_boxed_210_; lean_object* v_res_211_; 
v_i_boxed_209_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_stop_boxed_210_ = lean_unbox_usize(v_stop_207_);
lean_dec(v_stop_207_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_204_, v_as_205_, v_i_boxed_209_, v_stop_boxed_210_, v_b_208_);
lean_dec_ref(v_as_205_);
lean_dec(v_numHaves_204_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(lean_object* v_numHaves_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_buckets_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_216_ = l_Lean_Expr_collectLooseBVars(v_a_213_, v___x_214_);
v_buckets_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_buckets_217_);
lean_dec_ref(v___x_216_);
v___x_218_ = lean_array_get_size(v_buckets_217_);
v___x_219_ = lean_nat_dec_lt(v___x_214_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_buckets_217_);
return v___x_215_;
}
else
{
size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((size_t)0ULL);
v___x_221_ = lean_usize_of_nat(v___x_218_);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_212_, v_buckets_217_, v___x_220_, v___x_221_, v___x_215_);
lean_dec_ref(v_buckets_217_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_223_, v_a_224_);
lean_dec(v_numHaves_223_);
return v_res_225_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_226_, lean_object* v_t_227_){
_start:
{
if (lean_obj_tag(v_t_227_) == 0)
{
lean_object* v_k_228_; lean_object* v_l_229_; lean_object* v_r_230_; uint8_t v___x_231_; 
v_k_228_ = lean_ctor_get(v_t_227_, 1);
v_l_229_ = lean_ctor_get(v_t_227_, 3);
v_r_230_ = lean_ctor_get(v_t_227_, 4);
v___x_231_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_226_, v_k_228_);
switch(v___x_231_)
{
case 0:
{
v_t_227_ = v_l_229_;
goto _start;
}
case 1:
{
uint8_t v___x_233_; 
v___x_233_ = 1;
return v___x_233_;
}
default: 
{
v_t_227_ = v_r_230_;
goto _start;
}
}
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_236_, lean_object* v_t_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_236_, v_t_237_);
lean_dec(v_t_237_);
lean_dec(v_k_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_240_, lean_object* v___x_241_, lean_object* v_n_242_, lean_object* v_j_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_zero_245_; uint8_t v_isZero_246_; 
v_zero_245_ = lean_unsigned_to_nat(0u);
v_isZero_246_ = lean_nat_dec_eq(v_j_243_, v_zero_245_);
if (v_isZero_246_ == 1)
{
lean_dec(v_j_243_);
return v_a_244_;
}
else
{
lean_object* v_one_247_; lean_object* v_n_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_one_247_ = lean_unsigned_to_nat(1u);
v_n_248_ = lean_nat_sub(v_j_243_, v_one_247_);
v___x_249_ = lean_nat_sub(v_n_242_, v_j_243_);
lean_dec(v_j_243_);
v___x_250_ = lean_array_fget_borrowed(v_fvars_240_, v___x_249_);
v___x_251_ = l_Lean_Expr_fvarId_x21(v___x_250_);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_251_, v___x_241_);
lean_dec(v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v___x_249_);
v_j_243_ = v_n_248_;
goto _start;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(0);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_244_, v___x_249_, v___x_254_);
v_j_243_ = v_n_248_;
v_a_244_ = v___x_255_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_257_, lean_object* v___x_258_, lean_object* v_n_259_, lean_object* v_j_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_257_, v___x_258_, v_n_259_, v_j_260_, v_a_261_);
lean_dec(v_n_259_);
lean_dec(v___x_258_);
lean_dec_ref(v_fvars_257_);
return v_res_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_unsigned_to_nat(16u);
v___x_265_ = lean_mk_array(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_271_, lean_object* v___x_272_, lean_object* v_fvars_273_, lean_object* v_info_274_, lean_object* v_bodyDeps_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc_ref(v_body_271_);
v___x_281_ = lean_infer_type(v_body_271_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_283_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_n(v_a_282_, 2);
lean_dec_ref_known(v___x_281_, 1);
v___x_283_ = l_Lean_Meta_getLevel(v_a_282_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_311_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_311_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_311_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_311_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_fvarSet_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_haveInfo_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_305_; 
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_272_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
lean_inc(v_a_282_);
v___x_291_ = l_Lean_collectFVars(v___x_290_, v_a_282_);
v_fvarSet_292_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_fvarSet_292_);
lean_dec_ref(v___x_291_);
v___x_293_ = lean_array_get_size(v_fvars_273_);
v___x_294_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_273_, v_fvarSet_292_, v___x_293_, v___x_293_, v___x_288_);
lean_dec(v_fvarSet_292_);
v_haveInfo_295_ = lean_ctor_get(v_info_274_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_info_274_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; 
v_unused_306_ = lean_ctor_get(v_info_274_, 5);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_info_274_, 4);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_info_274_, 3);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_info_274_, 2);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_info_274_, 1);
lean_dec(v_unused_310_);
v___x_297_ = v_info_274_;
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_haveInfo_295_);
lean_dec(v_info_274_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 5, v_a_284_);
lean_ctor_set(v___x_297_, 4, v_a_282_);
lean_ctor_set(v___x_297_, 3, v_body_271_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
lean_ctor_set(v___x_297_, 1, v_bodyDeps_275_);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_haveInfo_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_bodyDeps_275_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_body_271_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_a_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_a_284_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_300_);
v___x_302_ = v___x_286_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_a_282_);
lean_dec_ref(v_bodyDeps_275_);
lean_dec_ref(v_info_274_);
lean_dec(v___x_272_);
lean_dec_ref(v_body_271_);
v_a_312_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_283_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_283_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_bodyDeps_275_);
lean_dec_ref(v_info_274_);
lean_dec(v___x_272_);
lean_dec_ref(v_body_271_);
v_a_320_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_281_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_281_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_328_, lean_object* v___x_329_, lean_object* v_fvars_330_, lean_object* v_info_331_, lean_object* v_bodyDeps_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_328_, v___x_329_, v_fvars_330_, v_info_331_, v_bodyDeps_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec_ref(v_fvars_330_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_ngen_342_; lean_object* v_namePrefix_343_; lean_object* v_idx_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_374_; 
v___x_341_ = lean_st_ref_get(v___y_339_);
v_ngen_342_ = lean_ctor_get(v___x_341_, 2);
lean_inc_ref(v_ngen_342_);
lean_dec(v___x_341_);
v_namePrefix_343_ = lean_ctor_get(v_ngen_342_, 0);
v_idx_344_ = lean_ctor_get(v_ngen_342_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_ngen_342_);
if (v_isSharedCheck_374_ == 0)
{
v___x_346_ = v_ngen_342_;
v_isShared_347_ = v_isSharedCheck_374_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_idx_344_);
lean_inc(v_namePrefix_343_);
lean_dec(v_ngen_342_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_374_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_r_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_inc(v_idx_344_);
lean_inc(v_namePrefix_343_);
v_r_348_ = l_Lean_Name_num___override(v_namePrefix_343_, v_idx_344_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_idx_344_, v___x_349_);
lean_dec(v_idx_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_350_);
v___x_352_ = v___x_346_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_namePrefix_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_373_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v_env_354_; lean_object* v_nextMacroScope_355_; lean_object* v_auxDeclNGen_356_; lean_object* v_traceState_357_; lean_object* v_cache_358_; lean_object* v_recordedDeps_359_; lean_object* v_messages_360_; lean_object* v_infoState_361_; lean_object* v_snapshotTasks_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_371_; 
v___x_353_ = lean_st_ref_take(v___y_339_);
v_env_354_ = lean_ctor_get(v___x_353_, 0);
v_nextMacroScope_355_ = lean_ctor_get(v___x_353_, 1);
v_auxDeclNGen_356_ = lean_ctor_get(v___x_353_, 3);
v_traceState_357_ = lean_ctor_get(v___x_353_, 4);
v_cache_358_ = lean_ctor_get(v___x_353_, 5);
v_recordedDeps_359_ = lean_ctor_get(v___x_353_, 6);
v_messages_360_ = lean_ctor_get(v___x_353_, 7);
v_infoState_361_ = lean_ctor_get(v___x_353_, 8);
v_snapshotTasks_362_ = lean_ctor_get(v___x_353_, 9);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_353_, 2);
lean_dec(v_unused_372_);
v___x_364_ = v___x_353_;
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snapshotTasks_362_);
lean_inc(v_infoState_361_);
lean_inc(v_messages_360_);
lean_inc(v_recordedDeps_359_);
lean_inc(v_cache_358_);
lean_inc(v_traceState_357_);
lean_inc(v_auxDeclNGen_356_);
lean_inc(v_nextMacroScope_355_);
lean_inc(v_env_354_);
lean_dec(v___x_353_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v___x_352_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_env_354_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_nextMacroScope_355_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_auxDeclNGen_356_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_traceState_357_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v_cache_358_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_recordedDeps_359_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_messages_360_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_infoState_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 9, v_snapshotTasks_362_);
v___x_367_ = v_reuseFailAlloc_370_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_st_ref_put(v___y_339_, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v_r_348_);
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
lean_object* v_declName_419_; lean_object* v_type_420_; lean_object* v_value_421_; lean_object* v_body_422_; lean_object* v_typeBackDeps_423_; lean_object* v_valueBackDeps_424_; lean_object* v_t_425_; lean_object* v_v_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_declName_419_ = lean_ctor_get(v_e_398_, 0);
lean_inc(v_declName_419_);
v_type_420_ = lean_ctor_get(v_e_398_, 1);
lean_inc_ref_n(v_type_420_, 2);
v_value_421_ = lean_ctor_get(v_e_398_, 2);
lean_inc_ref_n(v_value_421_, 2);
v_body_422_ = lean_ctor_get(v_e_398_, 3);
lean_inc_ref(v_body_422_);
lean_dec_ref_known(v_e_398_, 4);
v_typeBackDeps_423_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_399_, v_type_420_);
v_valueBackDeps_424_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_399_, v_value_421_);
v_t_425_ = lean_expr_instantiate_rev(v_type_420_, v_fvars_402_);
lean_dec_ref(v_type_420_);
v_v_426_ = lean_expr_instantiate_rev(v_value_421_, v_fvars_402_);
lean_dec_ref(v_value_421_);
lean_inc_ref(v_t_425_);
v___x_427_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_427_, 0, v_t_425_);
lean_inc_ref(v_lctx_401_);
v___x_428_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_401_, v___x_427_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_haveInfo_432_; lean_object* v_bodyDeps_433_; lean_object* v_bodyTypeDeps_434_; lean_object* v_body_435_; lean_object* v_bodyType_436_; lean_object* v_level_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_455_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v_haveInfo_432_ = lean_ctor_get(v_info_400_, 0);
v_bodyDeps_433_ = lean_ctor_get(v_info_400_, 1);
v_bodyTypeDeps_434_ = lean_ctor_get(v_info_400_, 2);
v_body_435_ = lean_ctor_get(v_info_400_, 3);
v_bodyType_436_ = lean_ctor_get(v_info_400_, 4);
v_level_437_ = lean_ctor_get(v_info_400_, 5);
v_isSharedCheck_455_ = !lean_is_exclusive(v_info_400_);
if (v_isSharedCheck_455_ == 0)
{
v___x_439_ = v_info_400_;
v_isShared_440_ = v_isSharedCheck_455_;
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
lean_dec(v_info_400_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_455_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = 0;
lean_inc(v_a_431_);
v___x_443_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v_a_431_);
lean_ctor_set(v___x_443_, 2, v_declName_419_);
lean_ctor_set(v___x_443_, 3, v_t_425_);
lean_ctor_set(v___x_443_, 4, v_v_426_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*5, v_nondep_418_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*5 + 1, v___x_442_);
lean_inc_ref(v___x_443_);
v___x_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_444_, 0, v_typeBackDeps_423_);
lean_ctor_set(v___x_444_, 1, v_valueBackDeps_424_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set(v___x_444_, 3, v_a_429_);
v___x_445_ = lean_array_push(v_haveInfo_432_, v___x_444_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_445_);
v___x_447_ = v___x_439_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_bodyDeps_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_bodyTypeDeps_434_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_body_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_bodyType_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_level_437_);
v___x_447_ = v_reuseFailAlloc_454_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = l_Lean_LocalContext_addDecl(v_lctx_401_, v___x_443_);
v___x_449_ = l_Lean_mkFVar(v_a_431_);
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
lean_dec(v_a_429_);
lean_dec_ref(v_v_426_);
lean_dec_ref(v_t_425_);
lean_dec_ref(v_valueBackDeps_424_);
lean_dec_ref(v_typeBackDeps_423_);
lean_dec_ref(v_body_422_);
lean_dec(v_declName_419_);
lean_dec_ref(v_fvars_402_);
lean_dec_ref(v_lctx_401_);
lean_dec_ref(v_info_400_);
lean_dec(v_numHaves_399_);
v_a_456_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_430_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_430_);
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
lean_dec_ref(v_v_426_);
lean_dec_ref(v_t_425_);
lean_dec_ref(v_valueBackDeps_424_);
lean_dec_ref(v_typeBackDeps_423_);
lean_dec_ref(v_body_422_);
lean_dec(v_declName_419_);
lean_dec_ref(v_fvars_402_);
lean_dec_ref(v_lctx_401_);
lean_dec_ref(v_info_400_);
lean_dec(v_numHaves_399_);
v_a_464_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_428_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_428_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_lctx_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_lctx_550_ = lean_ctor_get(v_a_545_, 2);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_553_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_550_);
v___x_554_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_544_, v___x_551_, v___x_553_, v_lctx_550_, v___x_552_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
return v_x_562_;
}
else
{
lean_object* v_key_564_; lean_object* v_tail_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_key_564_ = lean_ctor_get(v_x_563_, 0);
v_tail_565_ = lean_ctor_get(v_x_563_, 2);
v___x_566_ = 1;
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_array_set(v_x_562_, v_key_564_, v___x_567_);
v_x_562_ = v___x_568_;
v_x_563_ = v_tail_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_570_, v_x_571_);
lean_dec(v_x_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_573_, size_t v_i_574_, size_t v_stop_575_, lean_object* v_b_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_eq(v_i_574_, v_stop_575_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; size_t v___x_580_; size_t v___x_581_; 
v___x_578_ = lean_array_uget_borrowed(v_as_573_, v_i_574_);
v___x_579_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_576_, v___x_578_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_574_, v___x_580_);
v_i_574_ = v___x_581_;
v_b_576_ = v___x_579_;
goto _start;
}
else
{
return v_b_576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_583_, lean_object* v_i_584_, lean_object* v_stop_585_, lean_object* v_b_586_){
_start:
{
size_t v_i_boxed_587_; size_t v_stop_boxed_588_; lean_object* v_res_589_; 
v_i_boxed_587_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_stop_boxed_588_ = lean_unbox_usize(v_stop_585_);
lean_dec(v_stop_585_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_583_, v_i_boxed_587_, v_stop_boxed_588_, v_b_586_);
lean_dec_ref(v_as_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_590_, lean_object* v_s_591_){
_start:
{
lean_object* v_buckets_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_buckets_592_ = lean_ctor_get(v_s_591_, 1);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_array_get_size(v_buckets_592_);
v___x_595_ = lean_nat_dec_lt(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
return v_arr_590_;
}
else
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_596_ = ((size_t)0ULL);
v___x_597_ = lean_usize_of_nat(v___x_594_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_592_, v___x_596_, v___x_597_, v_arr_590_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_599_, lean_object* v_s_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_599_, v_s_600_);
lean_dec_ref(v_s_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_602_, lean_object* v_numHaves_603_, lean_object* v___x_604_, lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
lean_object* v_a_609_; uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_lt(v_a_605_, v_upperBound_602_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v_a_605_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_b_606_);
return v___x_614_;
}
else
{
uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_615_ = 0;
v___x_616_ = lean_nat_sub(v_numHaves_603_, v_a_605_);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_sub(v___x_616_, v___x_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(v___x_615_);
v___x_620_ = lean_array_get(v___x_619_, v_b_606_, v___x_618_);
lean_dec(v___x_619_);
v___x_621_ = lean_unbox(v___x_620_);
lean_dec(v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v___x_618_);
v_a_609_ = v_b_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_typeBackDeps_624_; lean_object* v_valueBackDeps_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_622_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_623_ = lean_array_get_borrowed(v___x_622_, v___x_604_, v___x_618_);
lean_dec(v___x_618_);
v_typeBackDeps_624_ = lean_ctor_get(v___x_623_, 0);
v_valueBackDeps_625_ = lean_ctor_get(v___x_623_, 1);
v___x_626_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_606_, v_typeBackDeps_624_);
v___x_627_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_626_, v_valueBackDeps_625_);
v_a_609_ = v___x_627_;
goto v___jp_608_;
}
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_add(v_a_605_, v___x_610_);
lean_dec(v_a_605_);
v_a_605_ = v___x_611_;
v_b_606_ = v_a_609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_628_, lean_object* v_numHaves_629_, lean_object* v___x_630_, lean_object* v_a_631_, lean_object* v_b_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_628_, v_numHaves_629_, v___x_630_, v_a_631_, v_b_632_);
lean_dec_ref(v___x_630_);
lean_dec(v_numHaves_629_);
lean_dec(v_upperBound_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_635_, lean_object* v_init_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_haveInfo_642_; lean_object* v_numHaves_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v_used_646_; lean_object* v___x_647_; lean_object* v_used_648_; lean_object* v___x_649_; 
v_haveInfo_642_ = lean_ctor_get(v_info_635_, 0);
v_numHaves_643_ = lean_array_get_size(v_haveInfo_642_);
v___x_644_ = 0;
v___x_645_ = lean_box(v___x_644_);
v_used_646_ = lean_mk_array(v_numHaves_643_, v___x_645_);
v___x_647_ = lean_unsigned_to_nat(0u);
v_used_648_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_646_, v_init_636_);
v___x_649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_643_, v_numHaves_643_, v_haveInfo_642_, v___x_647_, v_used_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_650_, lean_object* v_init_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_650_, v_init_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec_ref(v_init_651_);
lean_dec_ref(v_info_650_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_658_, lean_object* v_numHaves_659_, lean_object* v___x_660_, lean_object* v_inst_661_, lean_object* v_R_662_, lean_object* v_a_663_, lean_object* v_b_664_, lean_object* v_c_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_658_, v_numHaves_659_, v___x_660_, v_a_663_, v_b_664_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_672_, lean_object* v_numHaves_673_, lean_object* v___x_674_, lean_object* v_inst_675_, lean_object* v_R_676_, lean_object* v_a_677_, lean_object* v_b_678_, lean_object* v_c_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_672_, v_numHaves_673_, v___x_674_, v_inst_675_, v_R_676_, v_a_677_, v_b_678_, v_c_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v___x_674_);
lean_dec(v_numHaves_673_);
lean_dec(v_upperBound_672_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_688_, uint8_t v_keepUnused_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_bodyDeps_695_; lean_object* v_bodyTypeDeps_696_; lean_object* v___x_697_; 
v_bodyDeps_695_ = lean_ctor_get(v_info_688_, 1);
v_bodyTypeDeps_696_ = lean_ctor_get(v_info_688_, 2);
v___x_697_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_688_, v_bodyTypeDeps_696_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_697_) == 0)
{
if (v_keepUnused_689_ == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_688_, v_bodyDeps_695_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_a_698_);
lean_ctor_set(v___x_704_, 1, v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_a_698_);
v_a_709_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_699_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_699_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_a_717_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v___x_697_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_697_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_a_717_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_697_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_697_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_735_, lean_object* v_keepUnused_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_keepUnused_boxed_742_; lean_object* v_res_743_; 
v_keepUnused_boxed_742_ = lean_unbox(v_keepUnused_736_);
v_res_743_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_735_, v_keepUnused_boxed_742_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_info_735_);
return v_res_743_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_box(0);
v___x_748_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_749_ = l_Lean_Expr_const___override(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = 0;
v___x_751_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_752_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
lean_ctor_set(v___x_752_, 2, v___x_751_);
lean_ctor_set(v___x_752_, 3, v___x_751_);
lean_ctor_set(v___x_752_, 4, v___x_751_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*5, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_753_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_level_771_, lean_object* v_exprType_772_, lean_object* v_e_773_, uint8_t v___x_774_, lean_object* v_toPure_775_, lean_object* v_xs_776_, lean_object* v_____do__lift_777_){
_start:
{
if (lean_obj_tag(v_____do__lift_777_) == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_proof_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v_level_771_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_mkConst(v___x_778_, v___x_780_);
lean_inc_ref_n(v_e_773_, 3);
lean_inc_ref(v_exprType_772_);
v_proof_782_ = l_Lean_mkAppB(v___x_781_, v_exprType_772_, v_e_773_);
v___x_783_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_783_, 0, v_e_773_);
lean_ctor_set(v___x_783_, 1, v_exprType_772_);
lean_ctor_set(v___x_783_, 2, v_e_773_);
lean_ctor_set(v___x_783_, 3, v_e_773_);
lean_ctor_set(v___x_783_, 4, v_proof_782_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*5, v___x_774_);
v___x_784_ = lean_apply_2(v_toPure_775_, lean_box(0), v___x_783_);
return v___x_784_;
}
else
{
lean_object* v_e_785_; lean_object* v_h_786_; lean_object* v_expr_787_; lean_object* v_proof_788_; lean_object* v___x_793_; uint8_t v___x_794_; 
lean_dec(v_level_771_);
v_e_785_ = lean_ctor_get(v_____do__lift_777_, 0);
v_h_786_ = lean_ctor_get(v_____do__lift_777_, 1);
v_expr_787_ = lean_expr_abstract(v_e_785_, v_xs_776_);
v_proof_788_ = lean_expr_abstract(v_h_786_, v_xs_776_);
lean_inc_ref(v_proof_788_);
v___x_793_ = l_Lean_Expr_cleanupAnnotations(v_proof_788_);
v___x_794_ = l_Lean_Expr_isApp(v___x_793_);
if (v___x_794_ == 0)
{
lean_dec_ref(v___x_793_);
goto v___jp_789_;
}
else
{
lean_object* v_arg_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_arg_795_ = lean_ctor_get(v___x_793_, 1);
lean_inc_ref(v_arg_795_);
v___x_796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_793_);
v___x_797_ = l_Lean_Expr_isApp(v___x_796_);
if (v___x_797_ == 0)
{
lean_dec_ref(v___x_796_);
lean_dec_ref(v_arg_795_);
goto v___jp_789_;
}
else
{
lean_object* v_arg_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_arg_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc_ref(v_arg_798_);
v___x_799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_796_);
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_801_ = l_Lean_Expr_isConstOf(v___x_799_, v___x_800_);
lean_dec_ref(v___x_799_);
if (v___x_801_ == 0)
{
lean_dec_ref(v_arg_798_);
lean_dec_ref(v_arg_795_);
goto v___jp_789_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_803_ = lean_unsigned_to_nat(3u);
v___x_804_ = l_Lean_Expr_isAppOfArity(v_arg_798_, v___x_802_, v___x_803_);
lean_dec_ref(v_arg_798_);
if (v___x_804_ == 0)
{
lean_dec_ref(v_arg_795_);
goto v___jp_789_;
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = l_Lean_Expr_cleanupAnnotations(v_arg_795_);
v___x_806_ = l_Lean_Expr_isApp(v___x_805_);
if (v___x_806_ == 0)
{
lean_dec_ref(v___x_805_);
goto v___jp_789_;
}
else
{
lean_object* v_arg_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_arg_807_ = lean_ctor_get(v___x_805_, 1);
lean_inc_ref(v_arg_807_);
v___x_808_ = l_Lean_Expr_appFnCleanup___redArg(v___x_805_);
v___x_809_ = l_Lean_Expr_isApp(v___x_808_);
if (v___x_809_ == 0)
{
lean_dec_ref(v___x_808_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
lean_object* v_arg_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_arg_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc_ref(v_arg_810_);
v___x_811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_808_);
v___x_812_ = l_Lean_Expr_isConstOf(v___x_811_, v___x_800_);
lean_dec_ref(v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v_arg_810_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = l_Lean_Expr_cleanupAnnotations(v_arg_810_);
v___x_814_ = l_Lean_Expr_isApp(v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v___x_813_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
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
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
lean_object* v_arg_818_; uint8_t v___y_820_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_arg_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc_ref(v_arg_818_);
v___x_823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_816_);
v___x_824_ = l_Lean_Expr_isApp(v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v___x_823_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_823_);
v___x_826_ = l_Lean_Expr_isConstOf(v___x_825_, v___x_802_);
lean_dec_ref(v___x_825_);
if (v___x_826_ == 0)
{
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Expr_getAppFn(v_arg_807_);
if (lean_obj_tag(v___x_827_) == 4)
{
lean_object* v_declName_828_; 
v_declName_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_declName_828_);
lean_dec_ref_known(v___x_827_, 2);
if (lean_obj_tag(v_declName_828_) == 1)
{
lean_object* v_pre_829_; 
v_pre_829_ = lean_ctor_get(v_declName_828_, 0);
if (lean_obj_tag(v_pre_829_) == 0)
{
lean_object* v_str_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_str_830_ = lean_ctor_get(v_declName_828_, 1);
lean_inc_ref(v_str_830_);
lean_dec_ref_known(v_declName_828_, 2);
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_832_ = lean_string_dec_eq(v_str_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_834_ = lean_string_dec_eq(v_str_830_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_836_ = lean_string_dec_eq(v_str_830_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_838_ = lean_string_dec_eq(v_str_830_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_840_ = lean_string_dec_eq(v_str_830_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_842_ = lean_string_dec_eq(v_str_830_, v___x_841_);
lean_dec_ref(v_str_830_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
v___y_820_ = v___x_801_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref(v_str_830_);
v___y_820_ = v___x_801_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref(v_str_830_);
v___y_820_ = v___x_801_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref(v_str_830_);
v___y_820_ = v___x_801_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref(v_str_830_);
v___y_820_ = v___x_801_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref(v_str_830_);
v___y_820_ = v___x_801_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref_known(v_declName_828_, 2);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
}
else
{
lean_dec(v_declName_828_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
}
else
{
lean_dec_ref(v___x_827_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
}
}
v___jp_819_:
{
if (v___y_820_ == 0)
{
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_807_);
goto v___jp_789_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v_proof_788_);
lean_dec_ref(v_e_773_);
v___x_821_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_821_, 0, v_arg_815_);
lean_ctor_set(v___x_821_, 1, v_exprType_772_);
lean_ctor_set(v___x_821_, 2, v_arg_818_);
lean_ctor_set(v___x_821_, 3, v_expr_787_);
lean_ctor_set(v___x_821_, 4, v_arg_807_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*5, v___x_801_);
v___x_822_ = lean_apply_2(v_toPure_775_, lean_box(0), v___x_821_);
return v___x_822_;
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
v___jp_789_:
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = 1;
lean_inc_ref(v_expr_787_);
v___x_791_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_791_, 0, v_expr_787_);
lean_ctor_set(v___x_791_, 1, v_exprType_772_);
lean_ctor_set(v___x_791_, 2, v_e_773_);
lean_ctor_set(v___x_791_, 3, v_expr_787_);
lean_ctor_set(v___x_791_, 4, v_proof_788_);
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*5, v___x_790_);
v___x_792_ = lean_apply_2(v_toPure_775_, lean_box(0), v___x_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_level_843_, lean_object* v_exprType_844_, lean_object* v_e_845_, lean_object* v___x_846_, lean_object* v_toPure_847_, lean_object* v_xs_848_, lean_object* v_____do__lift_849_){
_start:
{
uint8_t v___x_7917__boxed_850_; lean_object* v_res_851_; 
v___x_7917__boxed_850_ = lean_unbox(v___x_846_);
v_res_851_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_level_843_, v_exprType_844_, v_e_845_, v___x_7917__boxed_850_, v_toPure_847_, v_xs_848_, v_____do__lift_849_);
lean_dec(v_____do__lift_849_);
lean_dec_ref(v_xs_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_852_, lean_object* v_bodyType_853_, lean_object* v_xs_854_, lean_object* v_level_855_, lean_object* v_e_856_, uint8_t v___x_857_, lean_object* v_toPure_858_, lean_object* v_body_859_, lean_object* v_toBind_860_, lean_object* v_____r_861_){
_start:
{
lean_object* v_simp_862_; lean_object* v_exprType_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_simp_862_ = lean_ctor_get(v_inst_852_, 2);
lean_inc(v_simp_862_);
lean_dec_ref(v_inst_852_);
v_exprType_863_ = lean_expr_abstract(v_bodyType_853_, v_xs_854_);
v___x_864_ = lean_box(v___x_857_);
v___f_865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_865_, 0, v_level_855_);
lean_closure_set(v___f_865_, 1, v_exprType_863_);
lean_closure_set(v___f_865_, 2, v_e_856_);
lean_closure_set(v___f_865_, 3, v___x_864_);
lean_closure_set(v___f_865_, 4, v_toPure_858_);
lean_closure_set(v___f_865_, 5, v_xs_854_);
v___x_866_ = lean_apply_1(v_simp_862_, v_body_859_);
v___x_867_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_866_, v___f_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_868_, lean_object* v_bodyType_869_, lean_object* v_xs_870_, lean_object* v_level_871_, lean_object* v_e_872_, lean_object* v___x_873_, lean_object* v_toPure_874_, lean_object* v_body_875_, lean_object* v_toBind_876_, lean_object* v_____r_877_){
_start:
{
uint8_t v___x_8070__boxed_878_; lean_object* v_res_879_; 
v___x_8070__boxed_878_ = lean_unbox(v___x_873_);
v_res_879_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_868_, v_bodyType_869_, v_xs_870_, v_level_871_, v_e_872_, v___x_8070__boxed_878_, v_toPure_874_, v_body_875_, v_toBind_876_, v_____r_877_);
lean_dec_ref(v_bodyType_869_);
return v_res_879_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_886_, lean_object* v_body_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_toMonadRef_890_, lean_object* v___x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_toCold_900_; lean_object* v_options_901_; uint8_t v_hasTrace_902_; 
v_toCold_900_ = lean_ctor_get(v___y_894_, 0);
v_options_901_ = lean_ctor_get(v_toCold_900_, 2);
v_hasTrace_902_ = lean_ctor_get_uint8(v_options_901_, sizeof(void*)*1);
if (v_hasTrace_902_ == 0)
{
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___x_891_);
lean_dec_ref(v_toMonadRef_890_);
lean_dec_ref(v___x_889_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v_body_887_);
lean_dec(v_cls_886_);
goto v___jp_897_;
}
else
{
lean_object* v_inheritedTraceOptions_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_inheritedTraceOptions_903_ = lean_ctor_get(v_toCold_900_, 11);
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_886_);
v___x_905_ = l_Lean_Name_append(v___x_904_, v_cls_886_);
v___x_906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_903_, v_options_901_, v___x_905_);
lean_dec(v___x_905_);
if (v___x_906_ == 0)
{
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___x_891_);
lean_dec_ref(v_toMonadRef_890_);
lean_dec_ref(v___x_889_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v_body_887_);
lean_dec(v_cls_886_);
goto v___jp_897_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_7539__overap_910_; lean_object* v___x_911_; 
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3);
v___x_908_ = l_Lean_MessageData_ofExpr(v_body_887_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_7539__overap_910_ = l_Lean_addTrace___redArg(v___x_888_, v___x_889_, v_toMonadRef_890_, v___x_891_, v_cls_886_, v___x_909_);
v___x_911_ = lean_apply_5(v___x_7539__overap_910_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, lean_box(0));
return v___x_911_;
}
}
v___jp_897_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_912_, lean_object* v_body_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_toMonadRef_916_, lean_object* v___x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_912_, v_body_913_, v___x_914_, v___x_915_, v_toMonadRef_916_, v___x_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_926_, lean_object* v_type_927_, lean_object* v___y_928_, lean_object* v_value_929_, uint8_t v___y_930_, lean_object* v___x_931_, uint8_t v___y_932_, lean_object* v_toPure_933_, lean_object* v_us_934_, uint8_t v___x_935_, lean_object* v_rb_936_){
_start:
{
lean_object* v_expr_937_; lean_object* v_exprType_938_; lean_object* v_exprInit_939_; lean_object* v_exprResult_940_; lean_object* v_proof_941_; uint8_t v_modified_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_969_; 
v_expr_937_ = lean_ctor_get(v_rb_936_, 0);
v_exprType_938_ = lean_ctor_get(v_rb_936_, 1);
v_exprInit_939_ = lean_ctor_get(v_rb_936_, 2);
v_exprResult_940_ = lean_ctor_get(v_rb_936_, 3);
v_proof_941_ = lean_ctor_get(v_rb_936_, 4);
v_modified_942_ = lean_ctor_get_uint8(v_rb_936_, sizeof(void*)*5);
v_isSharedCheck_969_ = !lean_is_exclusive(v_rb_936_);
if (v_isSharedCheck_969_ == 0)
{
v___x_944_ = v_rb_936_;
v_isShared_945_ = v_isSharedCheck_969_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_proof_941_);
lean_inc(v_exprResult_940_);
lean_inc(v_exprInit_939_);
lean_inc(v_exprType_938_);
lean_inc(v_expr_937_);
lean_dec(v_rb_936_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_969_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v_expr_948_; lean_object* v___x_949_; lean_object* v_exprType_950_; lean_object* v___x_951_; lean_object* v_exprInit_952_; lean_object* v_exprResult_953_; 
v___x_946_ = 0;
lean_inc_ref_n(v_type_927_, 4);
lean_inc_n(v_declName_926_, 4);
v___x_947_ = l_Lean_mkLambda(v_declName_926_, v___x_946_, v_type_927_, v_expr_937_);
lean_inc_ref_n(v___y_928_, 3);
lean_inc_ref(v___x_947_);
v_expr_948_ = l_Lean_Expr_app___override(v___x_947_, v___y_928_);
v___x_949_ = l_Lean_mkLambda(v_declName_926_, v___x_946_, v_type_927_, v_exprType_938_);
lean_inc_ref(v___x_949_);
v_exprType_950_ = l_Lean_Expr_app___override(v___x_949_, v___y_928_);
v___x_951_ = l_Lean_mkLambda(v_declName_926_, v___x_946_, v_type_927_, v_exprInit_939_);
lean_inc_ref(v___x_951_);
v_exprInit_952_ = l_Lean_Expr_app___override(v___x_951_, v_value_929_);
v_exprResult_953_ = l_Lean_Expr_letE___override(v_declName_926_, v_type_927_, v___y_928_, v_exprResult_940_, v___y_930_);
if (v_modified_942_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_proof_956_; lean_object* v___x_958_; 
lean_dec_ref(v___x_951_);
lean_dec_ref(v___x_949_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v_proof_941_);
lean_dec(v_us_934_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v_type_927_);
lean_dec(v_declName_926_);
v___x_954_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_955_ = l_Lean_mkConst(v___x_954_, v___x_931_);
lean_inc_ref(v_expr_948_);
lean_inc_ref(v_exprType_950_);
v_proof_956_ = l_Lean_mkAppB(v___x_955_, v_exprType_950_, v_expr_948_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_proof_956_);
lean_ctor_set(v___x_944_, 3, v_exprResult_953_);
lean_ctor_set(v___x_944_, 2, v_exprInit_952_);
lean_ctor_set(v___x_944_, 1, v_exprType_950_);
lean_ctor_set(v___x_944_, 0, v_expr_948_);
v___x_958_ = v___x_944_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_expr_948_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_exprType_950_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_exprInit_952_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_exprResult_953_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_proof_956_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*5, v___y_932_);
v___x_959_ = lean_apply_2(v_toPure_933_, lean_box(0), v___x_958_);
return v___x_959_;
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_proof_964_; lean_object* v___x_966_; 
lean_dec(v___x_931_);
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_962_ = l_Lean_mkConst(v___x_961_, v_us_934_);
lean_inc_ref(v_type_927_);
v___x_963_ = l_Lean_mkLambda(v_declName_926_, v___x_946_, v_type_927_, v_proof_941_);
v_proof_964_ = l_Lean_mkApp6(v___x_962_, v_type_927_, v___x_949_, v___y_928_, v___x_951_, v___x_947_, v___x_963_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_proof_964_);
lean_ctor_set(v___x_944_, 3, v_exprResult_953_);
lean_ctor_set(v___x_944_, 2, v_exprInit_952_);
lean_ctor_set(v___x_944_, 1, v_exprType_950_);
lean_ctor_set(v___x_944_, 0, v_expr_948_);
v___x_966_ = v___x_944_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_expr_948_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_exprType_950_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_exprInit_952_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_exprResult_953_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_proof_964_);
v___x_966_ = v_reuseFailAlloc_968_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; 
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*5, v___x_935_);
v___x_967_ = lean_apply_2(v_toPure_933_, lean_box(0), v___x_966_);
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_970_, lean_object* v_type_971_, lean_object* v___y_972_, lean_object* v_value_973_, lean_object* v___y_974_, lean_object* v___x_975_, lean_object* v___y_976_, lean_object* v_toPure_977_, lean_object* v_us_978_, lean_object* v___x_979_, lean_object* v_rb_980_){
_start:
{
uint8_t v___y_8165__boxed_981_; uint8_t v___y_8167__boxed_982_; uint8_t v___x_8168__boxed_983_; lean_object* v_res_984_; 
v___y_8165__boxed_981_ = lean_unbox(v___y_974_);
v___y_8167__boxed_982_ = lean_unbox(v___y_976_);
v___x_8168__boxed_983_ = lean_unbox(v___x_979_);
v_res_984_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_970_, v_type_971_, v___y_972_, v_value_973_, v___y_8165__boxed_981_, v___x_975_, v___y_8167__boxed_982_, v_toPure_977_, v_us_978_, v___x_8168__boxed_983_, v_rb_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_985_, lean_object* v_____x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_apply_1(v___f_985_, v_____x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_992_, lean_object* v_declName_993_, lean_object* v_type_994_, lean_object* v_value_995_, lean_object* v_us_996_, lean_object* v___x_997_, uint8_t v___x_998_, lean_object* v_toPure_999_, lean_object* v_rb_1000_){
_start:
{
lean_object* v_expr_1001_; lean_object* v_exprType_1002_; lean_object* v_exprInit_1003_; lean_object* v_exprResult_1004_; lean_object* v_proof_1005_; uint8_t v_modified_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1034_; 
v_expr_1001_ = lean_ctor_get(v_rb_1000_, 0);
v_exprType_1002_ = lean_ctor_get(v_rb_1000_, 1);
v_exprInit_1003_ = lean_ctor_get(v_rb_1000_, 2);
v_exprResult_1004_ = lean_ctor_get(v_rb_1000_, 3);
v_proof_1005_ = lean_ctor_get(v_rb_1000_, 4);
v_modified_1006_ = lean_ctor_get_uint8(v_rb_1000_, sizeof(void*)*5);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_rb_1000_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1008_ = v_rb_1000_;
v_isShared_1009_ = v_isSharedCheck_1034_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_proof_1005_);
lean_inc(v_exprResult_1004_);
lean_inc(v_exprInit_1003_);
lean_inc(v_exprType_1002_);
lean_inc(v_expr_1001_);
lean_dec(v_rb_1000_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1034_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_expr_1010_; lean_object* v_exprType_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v_exprInit_1014_; lean_object* v_exprResult_1015_; 
v_expr_1010_ = lean_expr_lower_loose_bvars(v_expr_1001_, v___x_992_, v___x_992_);
lean_dec_ref(v_expr_1001_);
v_exprType_1011_ = lean_expr_lower_loose_bvars(v_exprType_1002_, v___x_992_, v___x_992_);
lean_dec_ref(v_exprType_1002_);
v___x_1012_ = 0;
lean_inc_ref(v_type_994_);
lean_inc(v_declName_993_);
v___x_1013_ = l_Lean_mkLambda(v_declName_993_, v___x_1012_, v_type_994_, v_exprInit_1003_);
lean_inc_ref(v_value_995_);
lean_inc_ref(v___x_1013_);
v_exprInit_1014_ = l_Lean_Expr_app___override(v___x_1013_, v_value_995_);
v_exprResult_1015_ = lean_expr_lower_loose_bvars(v_exprResult_1004_, v___x_992_, v___x_992_);
lean_dec_ref(v_exprResult_1004_);
if (v_modified_1006_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_proof_1021_; lean_object* v___x_1023_; 
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_proof_1005_);
lean_dec(v_declName_993_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1017_ = l_Lean_mkConst(v___x_1016_, v_us_996_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1019_ = l_Lean_mkConst(v___x_1018_, v___x_997_);
lean_inc_ref_n(v_expr_1010_, 3);
lean_inc_ref_n(v_exprType_1011_, 2);
v___x_1020_ = l_Lean_mkAppB(v___x_1019_, v_exprType_1011_, v_expr_1010_);
v_proof_1021_ = l_Lean_mkApp6(v___x_1017_, v_type_994_, v_exprType_1011_, v_value_995_, v_expr_1010_, v_expr_1010_, v___x_1020_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v_proof_1021_);
lean_ctor_set(v___x_1008_, 3, v_exprResult_1015_);
lean_ctor_set(v___x_1008_, 2, v_exprInit_1014_);
lean_ctor_set(v___x_1008_, 1, v_exprType_1011_);
lean_ctor_set(v___x_1008_, 0, v_expr_1010_);
v___x_1023_ = v___x_1008_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_expr_1010_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_exprType_1011_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_exprInit_1014_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_exprResult_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_proof_1021_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*5, v___x_998_);
v___x_1024_ = lean_apply_2(v_toPure_999_, lean_box(0), v___x_1023_);
return v___x_1024_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_proof_1029_; lean_object* v___x_1031_; 
lean_dec(v___x_997_);
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1027_ = l_Lean_mkConst(v___x_1026_, v_us_996_);
lean_inc_ref(v_type_994_);
v___x_1028_ = l_Lean_mkLambda(v_declName_993_, v___x_1012_, v_type_994_, v_proof_1005_);
lean_inc_ref(v_expr_1010_);
lean_inc_ref(v_exprType_1011_);
v_proof_1029_ = l_Lean_mkApp6(v___x_1027_, v_type_994_, v_exprType_1011_, v_value_995_, v___x_1013_, v_expr_1010_, v___x_1028_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v_proof_1029_);
lean_ctor_set(v___x_1008_, 3, v_exprResult_1015_);
lean_ctor_set(v___x_1008_, 2, v_exprInit_1014_);
lean_ctor_set(v___x_1008_, 1, v_exprType_1011_);
lean_ctor_set(v___x_1008_, 0, v_expr_1010_);
v___x_1031_ = v___x_1008_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_expr_1010_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_exprType_1011_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_exprInit_1014_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_exprResult_1015_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_proof_1029_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*5, v___x_998_);
v___x_1032_ = lean_apply_2(v_toPure_999_, lean_box(0), v___x_1031_);
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1035_, lean_object* v_declName_1036_, lean_object* v_type_1037_, lean_object* v_value_1038_, lean_object* v_us_1039_, lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v_toPure_1042_, lean_object* v_rb_1043_){
_start:
{
uint8_t v___x_8255__boxed_1044_; lean_object* v_res_1045_; 
v___x_8255__boxed_1044_ = lean_unbox(v___x_1041_);
v_res_1045_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1035_, v_declName_1036_, v_type_1037_, v_value_1038_, v_us_1039_, v___x_1040_, v___x_8255__boxed_1044_, v_toPure_1042_, v_rb_1043_);
lean_dec(v___x_1035_);
return v_res_1045_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1052_, lean_object* v_declName_1053_, lean_object* v_val_1054_, lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v_toMonadRef_1057_, lean_object* v___x_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_toCold_1067_; lean_object* v_options_1068_; uint8_t v_hasTrace_1069_; 
v_toCold_1067_ = lean_ctor_get(v___y_1061_, 0);
v_options_1068_ = lean_ctor_get(v_toCold_1067_, 2);
v_hasTrace_1069_ = lean_ctor_get_uint8(v_options_1068_, sizeof(void*)*1);
if (v_hasTrace_1069_ == 0)
{
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_val_1054_);
lean_dec(v_declName_1053_);
lean_dec(v_cls_1052_);
goto v___jp_1064_;
}
else
{
lean_object* v_inheritedTraceOptions_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_inheritedTraceOptions_1070_ = lean_ctor_get(v_toCold_1067_, 11);
v___x_1071_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1052_);
v___x_1072_ = l_Lean_Name_append(v___x_1071_, v_cls_1052_);
v___x_1073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1070_, v_options_1068_, v___x_1072_);
lean_dec(v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_val_1054_);
lean_dec(v_declName_1053_);
lean_dec(v_cls_1052_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_7883__overap_1081_; lean_object* v___x_1082_; 
v___x_1074_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1075_ = l_Lean_MessageData_ofName(v_declName_1053_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_MessageData_ofExpr(v_val_1054_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_7883__overap_1081_ = l_Lean_addTrace___redArg(v___x_1055_, v___x_1056_, v_toMonadRef_1057_, v___x_1058_, v_cls_1052_, v___x_1080_);
v___x_1082_ = lean_apply_5(v___x_7883__overap_1081_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
return v___x_1082_;
}
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1083_, lean_object* v_declName_1084_, lean_object* v_val_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_toMonadRef_1088_, lean_object* v___x_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1083_, v_declName_1084_, v_val_1085_, v___x_1086_, v___x_1087_, v_toMonadRef_1088_, v___x_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
return v_res_1095_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1102_, lean_object* v_declName_1103_, lean_object* v_val_1104_, lean_object* v_val_x27_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v_toMonadRef_1108_, lean_object* v___x_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_toCold_1118_; lean_object* v_options_1119_; uint8_t v_hasTrace_1120_; 
v_toCold_1118_ = lean_ctor_get(v___y_1112_, 0);
v_options_1119_ = lean_ctor_get(v_toCold_1118_, 2);
v_hasTrace_1120_ = lean_ctor_get_uint8(v_options_1119_, sizeof(void*)*1);
if (v_hasTrace_1120_ == 0)
{
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_toMonadRef_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_val_x27_1105_);
lean_dec_ref(v_val_1104_);
lean_dec(v_declName_1103_);
lean_dec(v_cls_1102_);
goto v___jp_1115_;
}
else
{
lean_object* v_inheritedTraceOptions_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_inheritedTraceOptions_1121_ = lean_ctor_get(v_toCold_1118_, 11);
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1102_);
v___x_1123_ = l_Lean_Name_append(v___x_1122_, v_cls_1102_);
v___x_1124_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1121_, v_options_1119_, v___x_1123_);
lean_dec(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_toMonadRef_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_val_x27_1105_);
lean_dec_ref(v_val_1104_);
lean_dec(v_declName_1103_);
lean_dec(v_cls_1102_);
goto v___jp_1115_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_7627__overap_1136_; lean_object* v___x_1137_; 
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1126_ = l_Lean_MessageData_ofName(v_declName_1103_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_ofExpr(v_val_1104_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = l_Lean_MessageData_ofExpr(v_val_x27_1105_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_7627__overap_1136_ = l_Lean_addTrace___redArg(v___x_1106_, v___x_1107_, v_toMonadRef_1108_, v___x_1109_, v_cls_1102_, v___x_1135_);
v___x_1137_ = lean_apply_5(v___x_7627__overap_1136_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, lean_box(0));
return v___x_1137_;
}
}
v___jp_1115_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1138_, lean_object* v_declName_1139_, lean_object* v_val_1140_, lean_object* v_val_x27_1141_, lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v_toMonadRef_1144_, lean_object* v___x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1138_, v_declName_1139_, v_val_1140_, v_val_x27_1141_, v___x_1142_, v___x_1143_, v_toMonadRef_1144_, v___x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_e_1152_, lean_object* v_xs_1153_, lean_object* v_h_1154_, uint8_t v___x_1155_, lean_object* v_toPure_1156_, lean_object* v_toBind_1157_, lean_object* v___f_1158_, lean_object* v_____r_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1160_ = lean_expr_abstract(v_e_1152_, v_xs_1153_);
v___x_1161_ = lean_expr_abstract(v_h_1154_, v_xs_1153_);
v___x_1162_ = lean_box(v___x_1155_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1161_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1160_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_apply_2(v_toPure_1156_, lean_box(0), v___x_1164_);
v___x_1166_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1165_, v___f_1158_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_e_1167_, lean_object* v_xs_1168_, lean_object* v_h_1169_, lean_object* v___x_1170_, lean_object* v_toPure_1171_, lean_object* v_toBind_1172_, lean_object* v___f_1173_, lean_object* v_____r_1174_){
_start:
{
uint8_t v___x_8487__boxed_1175_; lean_object* v_res_1176_; 
v___x_8487__boxed_1175_ = lean_unbox(v___x_1170_);
v_res_1176_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_e_1167_, v_xs_1168_, v_h_1169_, v___x_8487__boxed_1175_, v_toPure_1171_, v_toBind_1172_, v___f_1173_, v_____r_1174_);
lean_dec_ref(v_h_1169_);
lean_dec_ref(v_xs_1168_);
lean_dec_ref(v_e_1167_);
return v_res_1176_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1180_, lean_object* v_declName_1181_, lean_object* v_val_1182_, lean_object* v_e_1183_, lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v_toMonadRef_1186_, lean_object* v___x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_toCold_1196_; lean_object* v_options_1197_; uint8_t v_hasTrace_1198_; 
v_toCold_1196_ = lean_ctor_get(v___y_1190_, 0);
v_options_1197_ = lean_ctor_get(v_toCold_1196_, 2);
v_hasTrace_1198_ = lean_ctor_get_uint8(v_options_1197_, sizeof(void*)*1);
if (v_hasTrace_1198_ == 0)
{
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_toMonadRef_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_val_1182_);
lean_dec(v_declName_1181_);
lean_dec(v_cls_1180_);
goto v___jp_1193_;
}
else
{
lean_object* v_inheritedTraceOptions_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_inheritedTraceOptions_1199_ = lean_ctor_get(v_toCold_1196_, 11);
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1180_);
v___x_1201_ = l_Lean_Name_append(v___x_1200_, v_cls_1180_);
v___x_1202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1199_, v_options_1197_, v___x_1201_);
lean_dec(v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_toMonadRef_1186_);
lean_dec_ref(v___x_1185_);
lean_dec_ref(v___x_1184_);
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_val_1182_);
lean_dec(v_declName_1181_);
lean_dec(v_cls_1180_);
goto v___jp_1193_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_7777__overap_1214_; lean_object* v___x_1215_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1204_ = l_Lean_MessageData_ofName(v_declName_1181_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_MessageData_ofExpr(v_val_1182_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = l_Lean_MessageData_ofExpr(v_e_1183_);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_7777__overap_1214_ = l_Lean_addTrace___redArg(v___x_1184_, v___x_1185_, v_toMonadRef_1186_, v___x_1187_, v_cls_1180_, v___x_1213_);
v___x_1215_ = lean_apply_5(v___x_7777__overap_1214_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, lean_box(0));
return v___x_1215_;
}
}
v___jp_1193_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1216_, lean_object* v_declName_1217_, lean_object* v_val_1218_, lean_object* v_e_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v_toMonadRef_1222_, lean_object* v___x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1216_, v_declName_1217_, v_val_1218_, v_e_1219_, v___x_1220_, v___x_1221_, v_toMonadRef_1222_, v___x_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_level_1239_, lean_object* v___x_1240_, lean_object* v_type_1241_, lean_object* v_value_1242_, uint8_t v___x_1243_, lean_object* v_toPure_1244_, lean_object* v_toBind_1245_, lean_object* v___f_1246_, lean_object* v_xs_1247_, uint8_t v___x_1248_, lean_object* v___f_1249_, lean_object* v_declName_1250_, lean_object* v_val_1251_, lean_object* v___x_1252_, lean_object* v___x_1253_, lean_object* v_toMonadRef_1254_, lean_object* v___x_1255_, lean_object* v_inst_1256_, lean_object* v_____do__lift_1257_){
_start:
{
if (lean_obj_tag(v_____do__lift_1257_) == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_inst_1256_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v_toMonadRef_1254_);
lean_dec_ref(v___x_1253_);
lean_dec_ref(v___x_1252_);
lean_dec_ref(v_val_1251_);
lean_dec(v_declName_1250_);
lean_dec(v___f_1249_);
lean_dec_ref(v_xs_1247_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_level_1239_);
lean_ctor_set(v___x_1259_, 1, v___x_1240_);
v___x_1260_ = l_Lean_mkConst(v___x_1258_, v___x_1259_);
lean_inc_ref(v_value_1242_);
v___x_1261_ = l_Lean_mkAppB(v___x_1260_, v_type_1241_, v_value_1242_);
v___x_1262_ = lean_box(v___x_1243_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_value_1242_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_apply_2(v_toPure_1244_, lean_box(0), v___x_1264_);
v___x_1266_ = lean_apply_4(v_toBind_1245_, lean_box(0), lean_box(0), v___x_1265_, v___f_1246_);
return v___x_1266_;
}
else
{
lean_object* v_e_1267_; lean_object* v_h_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v_cls_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec(v___f_1246_);
lean_dec_ref(v_value_1242_);
lean_dec_ref(v_type_1241_);
lean_dec(v___x_1240_);
lean_dec(v_level_1239_);
v_e_1267_ = lean_ctor_get(v_____do__lift_1257_, 0);
lean_inc_ref_n(v_e_1267_, 2);
v_h_1268_ = lean_ctor_get(v_____do__lift_1257_, 1);
lean_inc_ref(v_h_1268_);
lean_dec_ref_known(v_____do__lift_1257_, 2);
v___x_1269_ = lean_box(v___x_1248_);
lean_inc(v_toBind_1245_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1270_, 0, v_e_1267_);
lean_closure_set(v___f_1270_, 1, v_xs_1247_);
lean_closure_set(v___f_1270_, 2, v_h_1268_);
lean_closure_set(v___f_1270_, 3, v___x_1269_);
lean_closure_set(v___f_1270_, 4, v_toPure_1244_);
lean_closure_set(v___f_1270_, 5, v_toBind_1245_);
lean_closure_set(v___f_1270_, 6, v___f_1249_);
v_cls_1271_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1272_, 0, v_cls_1271_);
lean_closure_set(v___f_1272_, 1, v_declName_1250_);
lean_closure_set(v___f_1272_, 2, v_val_1251_);
lean_closure_set(v___f_1272_, 3, v_e_1267_);
lean_closure_set(v___f_1272_, 4, v___x_1252_);
lean_closure_set(v___f_1272_, 5, v___x_1253_);
lean_closure_set(v___f_1272_, 6, v_toMonadRef_1254_);
lean_closure_set(v___f_1272_, 7, v___x_1255_);
v___x_1273_ = lean_apply_2(v_inst_1256_, lean_box(0), v___f_1272_);
v___x_1274_ = lean_apply_4(v_toBind_1245_, lean_box(0), lean_box(0), v___x_1273_, v___f_1270_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_level_1275_ = _args[0];
lean_object* v___x_1276_ = _args[1];
lean_object* v_type_1277_ = _args[2];
lean_object* v_value_1278_ = _args[3];
lean_object* v___x_1279_ = _args[4];
lean_object* v_toPure_1280_ = _args[5];
lean_object* v_toBind_1281_ = _args[6];
lean_object* v___f_1282_ = _args[7];
lean_object* v_xs_1283_ = _args[8];
lean_object* v___x_1284_ = _args[9];
lean_object* v___f_1285_ = _args[10];
lean_object* v_declName_1286_ = _args[11];
lean_object* v_val_1287_ = _args[12];
lean_object* v___x_1288_ = _args[13];
lean_object* v___x_1289_ = _args[14];
lean_object* v_toMonadRef_1290_ = _args[15];
lean_object* v___x_1291_ = _args[16];
lean_object* v_inst_1292_ = _args[17];
lean_object* v_____do__lift_1293_ = _args[18];
_start:
{
uint8_t v___x_8627__boxed_1294_; uint8_t v___x_8629__boxed_1295_; lean_object* v_res_1296_; 
v___x_8627__boxed_1294_ = lean_unbox(v___x_1279_);
v___x_8629__boxed_1295_ = lean_unbox(v___x_1284_);
v_res_1296_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_level_1275_, v___x_1276_, v_type_1277_, v_value_1278_, v___x_8627__boxed_1294_, v_toPure_1280_, v_toBind_1281_, v___f_1282_, v_xs_1283_, v___x_8629__boxed_1295_, v___f_1285_, v_declName_1286_, v_val_1287_, v___x_1288_, v___x_1289_, v_toMonadRef_1290_, v___x_1291_, v_inst_1292_, v_____do__lift_1293_);
return v_res_1296_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1307_ = lean_unsigned_to_nat(8u);
v___x_1308_ = lean_unsigned_to_nat(287u);
v___x_1309_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1310_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1311_ = l_mkPanicMessageWithDecl(v___x_1310_, v___x_1309_, v___x_1308_, v___x_1307_, v___x_1306_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1312_, lean_object* v_type_1313_, lean_object* v_fst_1314_, lean_object* v___x_1315_, lean_object* v_value_1316_, uint8_t v___x_1317_, uint8_t v_fst_1318_, lean_object* v___x_1319_, uint8_t v___x_1320_, lean_object* v_toPure_1321_, lean_object* v_us_1322_, lean_object* v_snd_1323_, lean_object* v___x_1324_, lean_object* v_rb_1325_){
_start:
{
lean_object* v_expr_1326_; lean_object* v_exprType_1327_; lean_object* v_exprInit_1328_; lean_object* v_exprResult_1329_; lean_object* v_proof_1330_; uint8_t v_modified_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1376_; 
v_expr_1326_ = lean_ctor_get(v_rb_1325_, 0);
v_exprType_1327_ = lean_ctor_get(v_rb_1325_, 1);
v_exprInit_1328_ = lean_ctor_get(v_rb_1325_, 2);
v_exprResult_1329_ = lean_ctor_get(v_rb_1325_, 3);
v_proof_1330_ = lean_ctor_get(v_rb_1325_, 4);
v_modified_1331_ = lean_ctor_get_uint8(v_rb_1325_, sizeof(void*)*5);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_rb_1325_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1333_ = v_rb_1325_;
v_isShared_1334_ = v_isSharedCheck_1376_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_proof_1330_);
lean_inc(v_exprResult_1329_);
lean_inc(v_exprInit_1328_);
lean_inc(v_exprType_1327_);
lean_inc(v_expr_1326_);
lean_dec(v_rb_1325_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1376_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_expr_has_loose_bvar(v_exprType_1327_, v___x_1335_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v_expr_1339_; lean_object* v_exprType_1340_; lean_object* v___x_1341_; lean_object* v_exprInit_1342_; lean_object* v_exprResult_1343_; 
v___x_1337_ = 0;
lean_inc_ref_n(v_type_1313_, 3);
lean_inc_n(v_declName_1312_, 3);
v___x_1338_ = l_Lean_mkLambda(v_declName_1312_, v___x_1337_, v_type_1313_, v_expr_1326_);
lean_inc_ref_n(v_fst_1314_, 2);
lean_inc_ref(v___x_1338_);
v_expr_1339_ = l_Lean_Expr_app___override(v___x_1338_, v_fst_1314_);
v_exprType_1340_ = lean_expr_lower_loose_bvars(v_exprType_1327_, v___x_1315_, v___x_1315_);
lean_dec_ref(v_exprType_1327_);
v___x_1341_ = l_Lean_mkLambda(v_declName_1312_, v___x_1337_, v_type_1313_, v_exprInit_1328_);
lean_inc_ref(v_value_1316_);
lean_inc_ref(v___x_1341_);
v_exprInit_1342_ = l_Lean_Expr_app___override(v___x_1341_, v_value_1316_);
v_exprResult_1343_ = l_Lean_Expr_letE___override(v_declName_1312_, v_type_1313_, v_fst_1314_, v_exprResult_1329_, v___x_1317_);
if (v_fst_1318_ == 0)
{
lean_dec_ref(v_snd_1323_);
lean_dec_ref(v_fst_1314_);
if (v_modified_1331_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_proof_1346_; lean_object* v___x_1348_; 
lean_dec_ref(v___x_1341_);
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_proof_1330_);
lean_dec(v_us_1322_);
lean_dec_ref(v_value_1316_);
lean_dec_ref(v_type_1313_);
lean_dec(v_declName_1312_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1345_ = l_Lean_mkConst(v___x_1344_, v___x_1319_);
lean_inc_ref(v_expr_1339_);
lean_inc_ref(v_exprType_1340_);
v_proof_1346_ = l_Lean_mkAppB(v___x_1345_, v_exprType_1340_, v_expr_1339_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 4, v_proof_1346_);
lean_ctor_set(v___x_1333_, 3, v_exprResult_1343_);
lean_ctor_set(v___x_1333_, 2, v_exprInit_1342_);
lean_ctor_set(v___x_1333_, 1, v_exprType_1340_);
lean_ctor_set(v___x_1333_, 0, v_expr_1339_);
v___x_1348_ = v___x_1333_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_expr_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_exprType_1340_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_exprInit_1342_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_exprResult_1343_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_proof_1346_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5, v___x_1320_);
v___x_1349_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1348_);
return v___x_1349_;
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_proof_1354_; lean_object* v___x_1356_; 
lean_dec(v___x_1319_);
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1352_ = l_Lean_mkConst(v___x_1351_, v_us_1322_);
lean_inc_ref(v_type_1313_);
v___x_1353_ = l_Lean_mkLambda(v_declName_1312_, v___x_1337_, v_type_1313_, v_proof_1330_);
lean_inc_ref(v_exprType_1340_);
v_proof_1354_ = l_Lean_mkApp6(v___x_1352_, v_type_1313_, v_exprType_1340_, v_value_1316_, v___x_1341_, v___x_1338_, v___x_1353_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 4, v_proof_1354_);
lean_ctor_set(v___x_1333_, 3, v_exprResult_1343_);
lean_ctor_set(v___x_1333_, 2, v_exprInit_1342_);
lean_ctor_set(v___x_1333_, 1, v_exprType_1340_);
lean_ctor_set(v___x_1333_, 0, v_expr_1339_);
v___x_1356_ = v___x_1333_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_expr_1339_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_exprType_1340_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_exprInit_1342_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_exprResult_1343_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_proof_1354_);
v___x_1356_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; 
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5, v___x_1317_);
v___x_1357_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1356_);
return v___x_1357_;
}
}
}
else
{
lean_dec(v___x_1319_);
if (v_modified_1331_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_proof_1361_; lean_object* v___x_1363_; 
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_proof_1330_);
lean_dec(v_declName_1312_);
v___x_1359_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1360_ = l_Lean_mkConst(v___x_1359_, v_us_1322_);
lean_inc_ref(v_exprType_1340_);
v_proof_1361_ = l_Lean_mkApp6(v___x_1360_, v_type_1313_, v_exprType_1340_, v_value_1316_, v_fst_1314_, v___x_1341_, v_snd_1323_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 4, v_proof_1361_);
lean_ctor_set(v___x_1333_, 3, v_exprResult_1343_);
lean_ctor_set(v___x_1333_, 2, v_exprInit_1342_);
lean_ctor_set(v___x_1333_, 1, v_exprType_1340_);
lean_ctor_set(v___x_1333_, 0, v_expr_1339_);
v___x_1363_ = v___x_1333_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_expr_1339_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_exprType_1340_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_exprInit_1342_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_exprResult_1343_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_proof_1361_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*5, v___x_1317_);
v___x_1364_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1363_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_proof_1369_; lean_object* v___x_1371_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1367_ = l_Lean_mkConst(v___x_1366_, v_us_1322_);
lean_inc_ref(v_type_1313_);
v___x_1368_ = l_Lean_mkLambda(v_declName_1312_, v___x_1337_, v_type_1313_, v_proof_1330_);
lean_inc_ref(v_exprType_1340_);
v_proof_1369_ = l_Lean_mkApp8(v___x_1367_, v_type_1313_, v_exprType_1340_, v_value_1316_, v_fst_1314_, v___x_1341_, v___x_1338_, v_snd_1323_, v___x_1368_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 4, v_proof_1369_);
lean_ctor_set(v___x_1333_, 3, v_exprResult_1343_);
lean_ctor_set(v___x_1333_, 2, v_exprInit_1342_);
lean_ctor_set(v___x_1333_, 1, v_exprType_1340_);
lean_ctor_set(v___x_1333_, 0, v_expr_1339_);
v___x_1371_ = v___x_1333_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_expr_1339_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_exprType_1340_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_exprInit_1342_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_exprResult_1343_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_proof_1369_);
v___x_1371_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; 
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5, v___x_1317_);
v___x_1372_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1371_);
return v___x_1372_;
}
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_del_object(v___x_1333_);
lean_dec_ref(v_proof_1330_);
lean_dec_ref(v_exprResult_1329_);
lean_dec_ref(v_exprInit_1328_);
lean_dec_ref(v_exprType_1327_);
lean_dec_ref(v_expr_1326_);
lean_dec_ref(v_snd_1323_);
lean_dec(v_us_1322_);
lean_dec(v_toPure_1321_);
lean_dec(v___x_1319_);
lean_dec_ref(v_value_1316_);
lean_dec_ref(v_fst_1314_);
lean_dec_ref(v_type_1313_);
lean_dec(v_declName_1312_);
v___x_1374_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1375_ = l_panic___redArg(v___x_1324_, v___x_1374_);
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1377_, lean_object* v_type_1378_, lean_object* v_fst_1379_, lean_object* v___x_1380_, lean_object* v_value_1381_, lean_object* v___x_1382_, lean_object* v_fst_1383_, lean_object* v___x_1384_, lean_object* v___x_1385_, lean_object* v_toPure_1386_, lean_object* v_us_1387_, lean_object* v_snd_1388_, lean_object* v___x_1389_, lean_object* v_rb_1390_){
_start:
{
uint8_t v___x_8749__boxed_1391_; uint8_t v_fst_8750__boxed_1392_; uint8_t v___x_8752__boxed_1393_; lean_object* v_res_1394_; 
v___x_8749__boxed_1391_ = lean_unbox(v___x_1382_);
v_fst_8750__boxed_1392_ = lean_unbox(v_fst_1383_);
v___x_8752__boxed_1393_ = lean_unbox(v___x_1385_);
v_res_1394_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1377_, v_type_1378_, v_fst_1379_, v___x_1380_, v_value_1381_, v___x_8749__boxed_1391_, v_fst_8750__boxed_1392_, v___x_1384_, v___x_8752__boxed_1393_, v_toPure_1386_, v_us_1387_, v_snd_1388_, v___x_1389_, v_rb_1390_);
lean_dec(v___x_1389_);
lean_dec(v___x_1380_);
return v_res_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_instMonadEIO___redArg();
return v___x_1398_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0);
v___x_1400_ = l_StateRefT_x27_instMonad___redArg(v___x_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1408_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8);
v___f_1411_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___x_1412_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1411_, v___x_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1415_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11));
v___x_1417_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1416_, v___x_1415_, v___x_1414_);
return v___x_1417_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12);
v___f_1420_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___f_1421_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10));
v___x_1422_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1421_, v___f_1420_, v___x_1419_);
return v___x_1422_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14));
v___x_1425_ = lean_unsigned_to_nat(34u);
v___x_1426_ = lean_unsigned_to_nat(217u);
v___x_1427_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1428_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1429_ = l_mkPanicMessageWithDecl(v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_, v___x_1424_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1430_, lean_object* v_type_1431_, lean_object* v_value_1432_, uint8_t v___y_1433_, lean_object* v___x_1434_, lean_object* v_toPure_1435_, lean_object* v_us_1436_, uint8_t v___x_1437_, lean_object* v_decl_1438_, lean_object* v_x_1439_, lean_object* v_i_1440_, lean_object* v_xs_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_info_1446_, lean_object* v_fixed_1447_, lean_object* v_used_1448_, lean_object* v_body_1449_, lean_object* v_toBind_1450_, lean_object* v_withNewLemmas_1451_, lean_object* v_val_x27_1452_, lean_object* v_val_1453_, uint8_t v___x_1454_, lean_object* v_____r_1455_){
_start:
{
uint8_t v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1475_; uint8_t v___x_1477_; 
v___x_1477_ = lean_expr_eqv(v_val_1453_, v_val_x27_1452_);
if (v___x_1477_ == 0)
{
v___y_1475_ = v___y_1433_;
goto v___jp_1474_;
}
else
{
v___y_1475_ = v___x_1454_;
goto v___jp_1474_;
}
v___jp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1459_ = lean_box(v___y_1433_);
v___x_1460_ = lean_box(v___y_1457_);
v___x_1461_ = lean_box(v___x_1437_);
v___f_1462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_1462_, 0, v_declName_1430_);
lean_closure_set(v___f_1462_, 1, v_type_1431_);
lean_closure_set(v___f_1462_, 2, v___y_1458_);
lean_closure_set(v___f_1462_, 3, v_value_1432_);
lean_closure_set(v___f_1462_, 4, v___x_1459_);
lean_closure_set(v___f_1462_, 5, v___x_1434_);
lean_closure_set(v___f_1462_, 6, v___x_1460_);
lean_closure_set(v___f_1462_, 7, v_toPure_1435_);
lean_closure_set(v___f_1462_, 8, v_us_1436_);
lean_closure_set(v___f_1462_, 9, v___x_1461_);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_decl_1438_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_mk_empty_array_with_capacity(v___x_1465_);
lean_inc_ref(v_x_1439_);
v___x_1467_ = lean_array_push(v___x_1466_, v_x_1439_);
v___x_1468_ = lean_nat_add(v_i_1440_, v___x_1465_);
v___x_1469_ = lean_array_push(v_xs_1441_, v_x_1439_);
lean_inc_ref(v_inst_1444_);
lean_inc_ref(v_inst_1442_);
v___x_1470_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1442_, v_inst_1443_, v_inst_1444_, v_inst_1445_, v_info_1446_, v_fixed_1447_, v_used_1448_, v_body_1449_, v___x_1468_, v___x_1469_);
v___x_1471_ = lean_apply_4(v_toBind_1450_, lean_box(0), lean_box(0), v___x_1470_, v___f_1462_);
v___x_1472_ = lean_apply_3(v_withNewLemmas_1451_, lean_box(0), v___x_1467_, v___x_1471_);
v___x_1473_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1444_, v_inst_1442_, v___x_1464_, v___x_1472_);
return v___x_1473_;
}
v___jp_1474_:
{
if (v___y_1475_ == 0)
{
lean_inc_ref(v_value_1432_);
v___y_1457_ = v___y_1475_;
v___y_1458_ = v_value_1432_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_expr_abstract(v_val_x27_1452_, v_xs_1441_);
v___y_1457_ = v___y_1475_;
v___y_1458_ = v___x_1476_;
goto v___jp_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1478_ = _args[0];
lean_object* v_type_1479_ = _args[1];
lean_object* v_value_1480_ = _args[2];
lean_object* v___y_1481_ = _args[3];
lean_object* v___x_1482_ = _args[4];
lean_object* v_toPure_1483_ = _args[5];
lean_object* v_us_1484_ = _args[6];
lean_object* v___x_1485_ = _args[7];
lean_object* v_decl_1486_ = _args[8];
lean_object* v_x_1487_ = _args[9];
lean_object* v_i_1488_ = _args[10];
lean_object* v_xs_1489_ = _args[11];
lean_object* v_inst_1490_ = _args[12];
lean_object* v_inst_1491_ = _args[13];
lean_object* v_inst_1492_ = _args[14];
lean_object* v_inst_1493_ = _args[15];
lean_object* v_info_1494_ = _args[16];
lean_object* v_fixed_1495_ = _args[17];
lean_object* v_used_1496_ = _args[18];
lean_object* v_body_1497_ = _args[19];
lean_object* v_toBind_1498_ = _args[20];
lean_object* v_withNewLemmas_1499_ = _args[21];
lean_object* v_val_x27_1500_ = _args[22];
lean_object* v_val_1501_ = _args[23];
lean_object* v___x_1502_ = _args[24];
lean_object* v_____r_1503_ = _args[25];
_start:
{
uint8_t v___y_9010__boxed_1504_; uint8_t v___x_9012__boxed_1505_; uint8_t v___x_9018__boxed_1506_; lean_object* v_res_1507_; 
v___y_9010__boxed_1504_ = lean_unbox(v___y_1481_);
v___x_9012__boxed_1505_ = lean_unbox(v___x_1485_);
v___x_9018__boxed_1506_ = lean_unbox(v___x_1502_);
v_res_1507_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1478_, v_type_1479_, v_value_1480_, v___y_9010__boxed_1504_, v___x_1482_, v_toPure_1483_, v_us_1484_, v___x_9012__boxed_1505_, v_decl_1486_, v_x_1487_, v_i_1488_, v_xs_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v_inst_1493_, v_info_1494_, v_fixed_1495_, v_used_1496_, v_body_1497_, v_toBind_1498_, v_withNewLemmas_1499_, v_val_x27_1500_, v_val_1501_, v___x_9018__boxed_1506_, v_____r_1503_);
lean_dec_ref(v_val_1501_);
lean_dec_ref(v_val_x27_1500_);
lean_dec(v_i_1488_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1508_, lean_object* v_type_1509_, lean_object* v_value_1510_, uint8_t v___y_1511_, lean_object* v___x_1512_, lean_object* v_toPure_1513_, lean_object* v_us_1514_, uint8_t v___x_1515_, lean_object* v_decl_1516_, lean_object* v_x_1517_, lean_object* v_i_1518_, lean_object* v_xs_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_info_1524_, lean_object* v_fixed_1525_, lean_object* v_used_1526_, lean_object* v_body_1527_, lean_object* v_toBind_1528_, lean_object* v_withNewLemmas_1529_, lean_object* v_val_1530_, uint8_t v___x_1531_, lean_object* v___x_1532_, lean_object* v___x_1533_, lean_object* v_toMonadRef_1534_, lean_object* v___x_1535_, lean_object* v_val_x27_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___f_1540_; lean_object* v_cls_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1537_ = lean_box(v___y_1511_);
v___x_1538_ = lean_box(v___x_1515_);
v___x_1539_ = lean_box(v___x_1531_);
lean_inc_ref(v_val_1530_);
lean_inc_ref(v_val_x27_1536_);
lean_inc(v_toBind_1528_);
lean_inc(v_inst_1521_);
lean_inc(v_declName_1508_);
v___f_1540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 26, 25);
lean_closure_set(v___f_1540_, 0, v_declName_1508_);
lean_closure_set(v___f_1540_, 1, v_type_1509_);
lean_closure_set(v___f_1540_, 2, v_value_1510_);
lean_closure_set(v___f_1540_, 3, v___x_1537_);
lean_closure_set(v___f_1540_, 4, v___x_1512_);
lean_closure_set(v___f_1540_, 5, v_toPure_1513_);
lean_closure_set(v___f_1540_, 6, v_us_1514_);
lean_closure_set(v___f_1540_, 7, v___x_1538_);
lean_closure_set(v___f_1540_, 8, v_decl_1516_);
lean_closure_set(v___f_1540_, 9, v_x_1517_);
lean_closure_set(v___f_1540_, 10, v_i_1518_);
lean_closure_set(v___f_1540_, 11, v_xs_1519_);
lean_closure_set(v___f_1540_, 12, v_inst_1520_);
lean_closure_set(v___f_1540_, 13, v_inst_1521_);
lean_closure_set(v___f_1540_, 14, v_inst_1522_);
lean_closure_set(v___f_1540_, 15, v_inst_1523_);
lean_closure_set(v___f_1540_, 16, v_info_1524_);
lean_closure_set(v___f_1540_, 17, v_fixed_1525_);
lean_closure_set(v___f_1540_, 18, v_used_1526_);
lean_closure_set(v___f_1540_, 19, v_body_1527_);
lean_closure_set(v___f_1540_, 20, v_toBind_1528_);
lean_closure_set(v___f_1540_, 21, v_withNewLemmas_1529_);
lean_closure_set(v___f_1540_, 22, v_val_x27_1536_);
lean_closure_set(v___f_1540_, 23, v_val_1530_);
lean_closure_set(v___f_1540_, 24, v___x_1539_);
v_cls_1541_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1542_, 0, v_cls_1541_);
lean_closure_set(v___f_1542_, 1, v_declName_1508_);
lean_closure_set(v___f_1542_, 2, v_val_1530_);
lean_closure_set(v___f_1542_, 3, v_val_x27_1536_);
lean_closure_set(v___f_1542_, 4, v___x_1532_);
lean_closure_set(v___f_1542_, 5, v___x_1533_);
lean_closure_set(v___f_1542_, 6, v_toMonadRef_1534_);
lean_closure_set(v___f_1542_, 7, v___x_1535_);
v___x_1543_ = lean_apply_2(v_inst_1521_, lean_box(0), v___f_1542_);
v___x_1544_ = lean_apply_4(v_toBind_1528_, lean_box(0), lean_box(0), v___x_1543_, v___f_1540_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1545_ = _args[0];
lean_object* v_type_1546_ = _args[1];
lean_object* v_value_1547_ = _args[2];
lean_object* v___y_1548_ = _args[3];
lean_object* v___x_1549_ = _args[4];
lean_object* v_toPure_1550_ = _args[5];
lean_object* v_us_1551_ = _args[6];
lean_object* v___x_1552_ = _args[7];
lean_object* v_decl_1553_ = _args[8];
lean_object* v_x_1554_ = _args[9];
lean_object* v_i_1555_ = _args[10];
lean_object* v_xs_1556_ = _args[11];
lean_object* v_inst_1557_ = _args[12];
lean_object* v_inst_1558_ = _args[13];
lean_object* v_inst_1559_ = _args[14];
lean_object* v_inst_1560_ = _args[15];
lean_object* v_info_1561_ = _args[16];
lean_object* v_fixed_1562_ = _args[17];
lean_object* v_used_1563_ = _args[18];
lean_object* v_body_1564_ = _args[19];
lean_object* v_toBind_1565_ = _args[20];
lean_object* v_withNewLemmas_1566_ = _args[21];
lean_object* v_val_1567_ = _args[22];
lean_object* v___x_1568_ = _args[23];
lean_object* v___x_1569_ = _args[24];
lean_object* v___x_1570_ = _args[25];
lean_object* v_toMonadRef_1571_ = _args[26];
lean_object* v___x_1572_ = _args[27];
lean_object* v_val_x27_1573_ = _args[28];
_start:
{
uint8_t v___y_8957__boxed_1574_; uint8_t v___x_8959__boxed_1575_; uint8_t v___x_8965__boxed_1576_; lean_object* v_res_1577_; 
v___y_8957__boxed_1574_ = lean_unbox(v___y_1548_);
v___x_8959__boxed_1575_ = lean_unbox(v___x_1552_);
v___x_8965__boxed_1576_ = lean_unbox(v___x_1568_);
v_res_1577_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1545_, v_type_1546_, v_value_1547_, v___y_8957__boxed_1574_, v___x_1549_, v_toPure_1550_, v_us_1551_, v___x_8959__boxed_1575_, v_decl_1553_, v_x_1554_, v_i_1555_, v_xs_1556_, v_inst_1557_, v_inst_1558_, v_inst_1559_, v_inst_1560_, v_info_1561_, v_fixed_1562_, v_used_1563_, v_body_1564_, v_toBind_1565_, v_withNewLemmas_1566_, v_val_1567_, v___x_8965__boxed_1576_, v___x_1569_, v___x_1570_, v_toMonadRef_1571_, v___x_1572_, v_val_x27_1573_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1578_, lean_object* v_declName_1579_, lean_object* v_type_1580_, lean_object* v_value_1581_, uint8_t v___x_1582_, lean_object* v___x_1583_, uint8_t v___x_1584_, lean_object* v_toPure_1585_, lean_object* v_us_1586_, lean_object* v___x_1587_, lean_object* v_x_1588_, lean_object* v_i_1589_, lean_object* v_xs_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_info_1595_, lean_object* v_fixed_1596_, lean_object* v_used_1597_, lean_object* v_body_1598_, lean_object* v_toBind_1599_, lean_object* v_withNewLemmas_1600_, lean_object* v_____x_1601_){
_start:
{
lean_object* v_snd_1602_; lean_object* v_fst_1603_; lean_object* v_fst_1604_; lean_object* v_snd_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1625_; 
v_snd_1602_ = lean_ctor_get(v_____x_1601_, 1);
lean_inc(v_snd_1602_);
v_fst_1603_ = lean_ctor_get(v_____x_1601_, 0);
lean_inc(v_fst_1603_);
lean_dec_ref(v_____x_1601_);
v_fst_1604_ = lean_ctor_get(v_snd_1602_, 0);
v_snd_1605_ = lean_ctor_get(v_snd_1602_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_snd_1602_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1607_ = v_snd_1602_;
v_isShared_1608_ = v_isSharedCheck_1625_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snd_1605_);
lean_inc(v_fst_1604_);
lean_dec(v_snd_1602_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1625_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_box(0);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
lean_ctor_set(v___x_1607_, 1, v___x_1609_);
lean_ctor_set(v___x_1607_, 0, v_decl_1578_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_decl_1578_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_box(v___x_1582_);
v___x_1614_ = lean_box(v___x_1584_);
v___f_1615_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 14, 13);
lean_closure_set(v___f_1615_, 0, v_declName_1579_);
lean_closure_set(v___f_1615_, 1, v_type_1580_);
lean_closure_set(v___f_1615_, 2, v_fst_1603_);
lean_closure_set(v___f_1615_, 3, v___x_1612_);
lean_closure_set(v___f_1615_, 4, v_value_1581_);
lean_closure_set(v___f_1615_, 5, v___x_1613_);
lean_closure_set(v___f_1615_, 6, v_fst_1604_);
lean_closure_set(v___f_1615_, 7, v___x_1583_);
lean_closure_set(v___f_1615_, 8, v___x_1614_);
lean_closure_set(v___f_1615_, 9, v_toPure_1585_);
lean_closure_set(v___f_1615_, 10, v_us_1586_);
lean_closure_set(v___f_1615_, 11, v_snd_1605_);
lean_closure_set(v___f_1615_, 12, v___x_1587_);
v___x_1616_ = lean_mk_empty_array_with_capacity(v___x_1612_);
lean_inc_ref(v_x_1588_);
v___x_1617_ = lean_array_push(v___x_1616_, v_x_1588_);
v___x_1618_ = lean_nat_add(v_i_1589_, v___x_1612_);
v___x_1619_ = lean_array_push(v_xs_1590_, v_x_1588_);
lean_inc_ref(v_inst_1593_);
lean_inc_ref(v_inst_1591_);
v___x_1620_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1591_, v_inst_1592_, v_inst_1593_, v_inst_1594_, v_info_1595_, v_fixed_1596_, v_used_1597_, v_body_1598_, v___x_1618_, v___x_1619_);
v___x_1621_ = lean_apply_4(v_toBind_1599_, lean_box(0), lean_box(0), v___x_1620_, v___f_1615_);
v___x_1622_ = lean_apply_3(v_withNewLemmas_1600_, lean_box(0), v___x_1617_, v___x_1621_);
v___x_1623_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1593_, v_inst_1591_, v___x_1611_, v___x_1622_);
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1626_ = _args[0];
lean_object* v_declName_1627_ = _args[1];
lean_object* v_type_1628_ = _args[2];
lean_object* v_value_1629_ = _args[3];
lean_object* v___x_1630_ = _args[4];
lean_object* v___x_1631_ = _args[5];
lean_object* v___x_1632_ = _args[6];
lean_object* v_toPure_1633_ = _args[7];
lean_object* v_us_1634_ = _args[8];
lean_object* v___x_1635_ = _args[9];
lean_object* v_x_1636_ = _args[10];
lean_object* v_i_1637_ = _args[11];
lean_object* v_xs_1638_ = _args[12];
lean_object* v_inst_1639_ = _args[13];
lean_object* v_inst_1640_ = _args[14];
lean_object* v_inst_1641_ = _args[15];
lean_object* v_inst_1642_ = _args[16];
lean_object* v_info_1643_ = _args[17];
lean_object* v_fixed_1644_ = _args[18];
lean_object* v_used_1645_ = _args[19];
lean_object* v_body_1646_ = _args[20];
lean_object* v_toBind_1647_ = _args[21];
lean_object* v_withNewLemmas_1648_ = _args[22];
lean_object* v_____x_1649_ = _args[23];
_start:
{
uint8_t v___x_8981__boxed_1650_; uint8_t v___x_8983__boxed_1651_; lean_object* v_res_1652_; 
v___x_8981__boxed_1650_ = lean_unbox(v___x_1630_);
v___x_8983__boxed_1651_ = lean_unbox(v___x_1632_);
v_res_1652_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1626_, v_declName_1627_, v_type_1628_, v_value_1629_, v___x_8981__boxed_1650_, v___x_1631_, v___x_8983__boxed_1651_, v_toPure_1633_, v_us_1634_, v___x_1635_, v_x_1636_, v_i_1637_, v_xs_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_inst_1642_, v_info_1643_, v_fixed_1644_, v_used_1645_, v_body_1646_, v_toBind_1647_, v_withNewLemmas_1648_, v_____x_1649_);
lean_dec(v_i_1637_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1653_ = _args[0];
lean_object* v_declName_1654_ = _args[1];
lean_object* v_type_1655_ = _args[2];
lean_object* v_value_1656_ = _args[3];
lean_object* v_us_1657_ = _args[4];
lean_object* v___x_1658_ = _args[5];
lean_object* v___x_1659_ = _args[6];
lean_object* v_toPure_1660_ = _args[7];
lean_object* v_i_1661_ = _args[8];
lean_object* v_xs_1662_ = _args[9];
lean_object* v_inst_1663_ = _args[10];
lean_object* v_inst_1664_ = _args[11];
lean_object* v_inst_1665_ = _args[12];
lean_object* v_inst_1666_ = _args[13];
lean_object* v_info_1667_ = _args[14];
lean_object* v_fixed_1668_ = _args[15];
lean_object* v_used_1669_ = _args[16];
lean_object* v_body_1670_ = _args[17];
lean_object* v_toBind_1671_ = _args[18];
lean_object* v_____r_1672_ = _args[19];
_start:
{
uint8_t v___x_8940__boxed_1673_; lean_object* v_res_1674_; 
v___x_8940__boxed_1673_ = lean_unbox(v___x_1659_);
v_res_1674_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1653_, v_declName_1654_, v_type_1655_, v_value_1656_, v_us_1657_, v___x_1658_, v___x_8940__boxed_1673_, v_toPure_1660_, v_i_1661_, v_xs_1662_, v_inst_1663_, v_inst_1664_, v_inst_1665_, v_inst_1666_, v_info_1667_, v_fixed_1668_, v_used_1669_, v_body_1670_, v_toBind_1671_, v_____r_1672_);
lean_dec(v_i_1661_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_info_1679_, lean_object* v_fixed_1680_, lean_object* v_used_1681_, lean_object* v_e_1682_, lean_object* v_i_1683_, lean_object* v_xs_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v_toApplicative_1686_; lean_object* v_toFunctor_1687_; lean_object* v_toSeq_1688_; lean_object* v_toSeqLeft_1689_; lean_object* v_toSeqRight_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_toApplicative_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1803_; 
v___x_1685_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v_toApplicative_1686_ = lean_ctor_get(v___x_1685_, 0);
v_toFunctor_1687_ = lean_ctor_get(v_toApplicative_1686_, 0);
v_toSeq_1688_ = lean_ctor_get(v_toApplicative_1686_, 2);
v_toSeqLeft_1689_ = lean_ctor_get(v_toApplicative_1686_, 3);
v_toSeqRight_1690_ = lean_ctor_get(v_toApplicative_1686_, 4);
v___f_1691_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2));
v___f_1692_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1687_, 2);
v___f_1693_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1693_, 0, v_toFunctor_1687_);
v___f_1694_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1694_, 0, v_toFunctor_1687_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___f_1693_);
lean_ctor_set(v___x_1695_, 1, v___f_1694_);
lean_inc(v_toSeqRight_1690_);
v___f_1696_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1696_, 0, v_toSeqRight_1690_);
lean_inc(v_toSeqLeft_1689_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toSeqLeft_1689_);
lean_inc(v_toSeq_1688_);
v___f_1698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1698_, 0, v_toSeq_1688_);
v___x_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1695_);
lean_ctor_set(v___x_1699_, 1, v___f_1691_);
lean_ctor_set(v___x_1699_, 2, v___f_1698_);
lean_ctor_set(v___x_1699_, 3, v___f_1697_);
lean_ctor_set(v___x_1699_, 4, v___f_1696_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v___f_1692_);
v___x_1701_ = l_StateRefT_x27_instMonad___redArg(v___x_1700_);
v_toApplicative_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v___x_1701_, 1);
lean_dec(v_unused_1804_);
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1803_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_toApplicative_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1803_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_toFunctor_1706_; lean_object* v_toSeq_1707_; lean_object* v_toSeqLeft_1708_; lean_object* v_toSeqRight_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1801_; 
v_toFunctor_1706_ = lean_ctor_get(v_toApplicative_1702_, 0);
v_toSeq_1707_ = lean_ctor_get(v_toApplicative_1702_, 2);
v_toSeqLeft_1708_ = lean_ctor_get(v_toApplicative_1702_, 3);
v_toSeqRight_1709_ = lean_ctor_get(v_toApplicative_1702_, 4);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_toApplicative_1702_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_toApplicative_1702_, 1);
lean_dec(v_unused_1802_);
v___x_1711_ = v_toApplicative_1702_;
v_isShared_1712_ = v_isSharedCheck_1801_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_toSeqRight_1709_);
lean_inc(v_toSeqLeft_1708_);
lean_inc(v_toSeq_1707_);
lean_inc(v_toFunctor_1706_);
lean_dec(v_toApplicative_1702_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1801_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___x_1722_; 
v___f_1713_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4));
v___f_1714_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5));
lean_inc_ref(v_toFunctor_1706_);
v___f_1715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1715_, 0, v_toFunctor_1706_);
v___f_1716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1716_, 0, v_toFunctor_1706_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___f_1715_);
lean_ctor_set(v___x_1717_, 1, v___f_1716_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toSeqRight_1709_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toSeqLeft_1708_);
v___f_1720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1720_, 0, v_toSeq_1707_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v___f_1718_);
lean_ctor_set(v___x_1711_, 3, v___f_1719_);
lean_ctor_set(v___x_1711_, 2, v___f_1720_);
lean_ctor_set(v___x_1711_, 1, v___f_1713_);
lean_ctor_set(v___x_1711_, 0, v___x_1717_);
v___x_1722_ = v___x_1711_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v___f_1713_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v___f_1720_);
lean_ctor_set(v_reuseFailAlloc_1800_, 3, v___f_1719_);
lean_ctor_set(v_reuseFailAlloc_1800_, 4, v___f_1718_);
v___x_1722_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v___f_1714_);
lean_ctor_set(v___x_1704_, 0, v___x_1722_);
v___x_1724_ = v___x_1704_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___f_1714_);
v___x_1724_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_toApplicative_1727_; lean_object* v_toMonadRef_1728_; lean_object* v_haveInfo_1729_; lean_object* v_body_1730_; lean_object* v_bodyType_1731_; lean_object* v_level_1732_; lean_object* v_toBind_1733_; lean_object* v_toPure_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1725_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9);
v___x_1726_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13);
v_toApplicative_1727_ = lean_ctor_get(v_inst_1675_, 0);
v_toMonadRef_1728_ = lean_ctor_get(v___x_1726_, 0);
v_haveInfo_1729_ = lean_ctor_get(v_info_1679_, 0);
v_body_1730_ = lean_ctor_get(v_info_1679_, 3);
v_bodyType_1731_ = lean_ctor_get(v_info_1679_, 4);
v_level_1732_ = lean_ctor_get(v_info_1679_, 5);
v_toBind_1733_ = lean_ctor_get(v_inst_1675_, 1);
lean_inc(v_toBind_1733_);
v_toPure_1734_ = lean_ctor_get(v_toApplicative_1727_, 1);
lean_inc(v_toPure_1734_);
v___x_1735_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1736_ = lean_array_get_size(v_haveInfo_1729_);
v___x_1737_ = lean_nat_dec_lt(v_i_1683_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___f_1739_; lean_object* v_cls_1740_; lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc(v_level_1732_);
lean_inc_ref(v_bodyType_1731_);
lean_inc_ref_n(v_body_1730_, 2);
lean_dec(v_i_1683_);
lean_dec_ref(v_used_1681_);
lean_dec_ref(v_fixed_1680_);
lean_dec_ref(v_info_1679_);
lean_dec_ref(v_inst_1677_);
lean_dec_ref(v_inst_1675_);
v___x_1738_ = lean_box(v___x_1737_);
lean_inc(v_toBind_1733_);
v___f_1739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1739_, 0, v_inst_1678_);
lean_closure_set(v___f_1739_, 1, v_bodyType_1731_);
lean_closure_set(v___f_1739_, 2, v_xs_1684_);
lean_closure_set(v___f_1739_, 3, v_level_1732_);
lean_closure_set(v___f_1739_, 4, v_e_1682_);
lean_closure_set(v___f_1739_, 5, v___x_1738_);
lean_closure_set(v___f_1739_, 6, v_toPure_1734_);
lean_closure_set(v___f_1739_, 7, v_body_1730_);
lean_closure_set(v___f_1739_, 8, v_toBind_1733_);
v_cls_1740_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1728_);
v___f_1741_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1741_, 0, v_cls_1740_);
lean_closure_set(v___f_1741_, 1, v_body_1730_);
lean_closure_set(v___f_1741_, 2, v___x_1724_);
lean_closure_set(v___f_1741_, 3, v___x_1725_);
lean_closure_set(v___f_1741_, 4, v_toMonadRef_1728_);
lean_closure_set(v___f_1741_, 5, v___x_1735_);
v___x_1742_ = lean_apply_2(v_inst_1676_, lean_box(0), v___f_1741_);
v___x_1743_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1742_, v___f_1739_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
lean_inc_ref(v_inst_1675_);
v___x_1745_ = l_instInhabitedOfMonad___redArg(v_inst_1675_, v___x_1744_);
if (lean_obj_tag(v_e_1682_) == 8)
{
uint8_t v_nondep_1749_; 
v_nondep_1749_ = lean_ctor_get_uint8(v_e_1682_, sizeof(void*)*4 + 8);
if (v_nondep_1749_ == 1)
{
lean_object* v_declName_1750_; lean_object* v_type_1751_; lean_object* v_value_1752_; lean_object* v_body_1753_; lean_object* v_hinfo_1754_; lean_object* v_decl_1755_; lean_object* v_level_1756_; lean_object* v_x_1757_; lean_object* v_val_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_us_1761_; uint8_t v___y_1763_; uint8_t v___y_1764_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_declName_1750_ = lean_ctor_get(v_e_1682_, 0);
lean_inc(v_declName_1750_);
v_type_1751_ = lean_ctor_get(v_e_1682_, 1);
lean_inc_ref(v_type_1751_);
v_value_1752_ = lean_ctor_get(v_e_1682_, 2);
lean_inc_ref(v_value_1752_);
v_body_1753_ = lean_ctor_get(v_e_1682_, 3);
lean_inc_ref(v_body_1753_);
lean_dec_ref_known(v_e_1682_, 4);
v_hinfo_1754_ = lean_array_fget_borrowed(v_haveInfo_1729_, v_i_1683_);
v_decl_1755_ = lean_ctor_get(v_hinfo_1754_, 2);
v_level_1756_ = lean_ctor_get(v_hinfo_1754_, 3);
lean_inc_ref(v_decl_1755_);
v_x_1757_ = l_Lean_LocalDecl_toExpr(v_decl_1755_);
v_val_1758_ = l_Lean_LocalDecl_value(v_decl_1755_, v___x_1737_);
v___x_1759_ = lean_box(0);
lean_inc(v_level_1732_);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_level_1732_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
lean_inc_ref(v___x_1760_);
lean_inc(v_level_1756_);
v_us_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1761_, 0, v_level_1756_);
lean_ctor_set(v_us_1761_, 1, v___x_1760_);
v___x_1789_ = lean_array_get_size(v_used_1681_);
v___x_1790_ = lean_nat_dec_lt(v_i_1683_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_inc_ref(v_decl_1755_);
goto v___jp_1773_;
}
else
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = lean_array_fget_borrowed(v_used_1681_, v_i_1683_);
v___x_1792_ = lean_unbox(v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v_cls_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v_x_1757_);
lean_dec(v___x_1745_);
v___x_1793_ = lean_box(v___x_1737_);
lean_inc(v_toBind_1733_);
lean_inc(v_inst_1676_);
lean_inc(v_declName_1750_);
v___f_1794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1794_, 0, v___x_1759_);
lean_closure_set(v___f_1794_, 1, v_declName_1750_);
lean_closure_set(v___f_1794_, 2, v_type_1751_);
lean_closure_set(v___f_1794_, 3, v_value_1752_);
lean_closure_set(v___f_1794_, 4, v_us_1761_);
lean_closure_set(v___f_1794_, 5, v___x_1760_);
lean_closure_set(v___f_1794_, 6, v___x_1793_);
lean_closure_set(v___f_1794_, 7, v_toPure_1734_);
lean_closure_set(v___f_1794_, 8, v_i_1683_);
lean_closure_set(v___f_1794_, 9, v_xs_1684_);
lean_closure_set(v___f_1794_, 10, v_inst_1675_);
lean_closure_set(v___f_1794_, 11, v_inst_1676_);
lean_closure_set(v___f_1794_, 12, v_inst_1677_);
lean_closure_set(v___f_1794_, 13, v_inst_1678_);
lean_closure_set(v___f_1794_, 14, v_info_1679_);
lean_closure_set(v___f_1794_, 15, v_fixed_1680_);
lean_closure_set(v___f_1794_, 16, v_used_1681_);
lean_closure_set(v___f_1794_, 17, v_body_1753_);
lean_closure_set(v___f_1794_, 18, v_toBind_1733_);
v_cls_1795_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1728_);
v___f_1796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1796_, 0, v_cls_1795_);
lean_closure_set(v___f_1796_, 1, v_declName_1750_);
lean_closure_set(v___f_1796_, 2, v_val_1758_);
lean_closure_set(v___f_1796_, 3, v___x_1724_);
lean_closure_set(v___f_1796_, 4, v___x_1725_);
lean_closure_set(v___f_1796_, 5, v_toMonadRef_1728_);
lean_closure_set(v___f_1796_, 6, v___x_1735_);
v___x_1797_ = lean_apply_2(v_inst_1676_, lean_box(0), v___f_1796_);
v___x_1798_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1797_, v___f_1794_);
return v___x_1798_;
}
else
{
lean_inc_ref(v_decl_1755_);
goto v___jp_1773_;
}
}
v___jp_1762_:
{
lean_object* v_withNewLemmas_1765_; lean_object* v_dsimp_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_withNewLemmas_1765_ = lean_ctor_get(v_inst_1678_, 0);
lean_inc(v_withNewLemmas_1765_);
v_dsimp_1766_ = lean_ctor_get(v_inst_1678_, 1);
lean_inc(v_dsimp_1766_);
v___x_1767_ = lean_box(v___y_1764_);
v___x_1768_ = lean_box(v___x_1737_);
v___x_1769_ = lean_box(v___y_1763_);
lean_inc_ref(v_toMonadRef_1728_);
lean_inc_ref(v_val_1758_);
lean_inc(v_toBind_1733_);
v___f_1770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 29, 28);
lean_closure_set(v___f_1770_, 0, v_declName_1750_);
lean_closure_set(v___f_1770_, 1, v_type_1751_);
lean_closure_set(v___f_1770_, 2, v_value_1752_);
lean_closure_set(v___f_1770_, 3, v___x_1767_);
lean_closure_set(v___f_1770_, 4, v___x_1760_);
lean_closure_set(v___f_1770_, 5, v_toPure_1734_);
lean_closure_set(v___f_1770_, 6, v_us_1761_);
lean_closure_set(v___f_1770_, 7, v___x_1768_);
lean_closure_set(v___f_1770_, 8, v_decl_1755_);
lean_closure_set(v___f_1770_, 9, v_x_1757_);
lean_closure_set(v___f_1770_, 10, v_i_1683_);
lean_closure_set(v___f_1770_, 11, v_xs_1684_);
lean_closure_set(v___f_1770_, 12, v_inst_1675_);
lean_closure_set(v___f_1770_, 13, v_inst_1676_);
lean_closure_set(v___f_1770_, 14, v_inst_1677_);
lean_closure_set(v___f_1770_, 15, v_inst_1678_);
lean_closure_set(v___f_1770_, 16, v_info_1679_);
lean_closure_set(v___f_1770_, 17, v_fixed_1680_);
lean_closure_set(v___f_1770_, 18, v_used_1681_);
lean_closure_set(v___f_1770_, 19, v_body_1753_);
lean_closure_set(v___f_1770_, 20, v_toBind_1733_);
lean_closure_set(v___f_1770_, 21, v_withNewLemmas_1765_);
lean_closure_set(v___f_1770_, 22, v_val_1758_);
lean_closure_set(v___f_1770_, 23, v___x_1769_);
lean_closure_set(v___f_1770_, 24, v___x_1724_);
lean_closure_set(v___f_1770_, 25, v___x_1725_);
lean_closure_set(v___f_1770_, 26, v_toMonadRef_1728_);
lean_closure_set(v___f_1770_, 27, v___x_1735_);
v___x_1771_ = lean_apply_1(v_dsimp_1766_, v_val_1758_);
v___x_1772_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1771_, v___f_1770_);
return v___x_1772_;
}
v___jp_1773_:
{
uint8_t v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = 0;
v___x_1775_ = lean_array_get_size(v_fixed_1680_);
v___x_1776_ = lean_nat_dec_lt(v_i_1683_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec(v___x_1745_);
v___y_1763_ = v___x_1774_;
v___y_1764_ = v___x_1737_;
goto v___jp_1762_;
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_array_fget_borrowed(v_fixed_1680_, v_i_1683_);
v___x_1778_ = lean_unbox(v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v_withNewLemmas_1779_; lean_object* v_simp_1780_; lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_inc_n(v___x_1777_, 2);
lean_inc(v_level_1756_);
v_withNewLemmas_1779_ = lean_ctor_get(v_inst_1678_, 0);
lean_inc(v_withNewLemmas_1779_);
v_simp_1780_ = lean_ctor_get(v_inst_1678_, 2);
lean_inc(v_simp_1780_);
v___x_1781_ = lean_box(v___x_1737_);
lean_inc_n(v_toBind_1733_, 2);
lean_inc(v_inst_1676_);
lean_inc_ref(v_xs_1684_);
lean_inc(v_toPure_1734_);
lean_inc_ref(v_value_1752_);
lean_inc_ref(v_type_1751_);
lean_inc(v_declName_1750_);
v___f_1782_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 24, 23);
lean_closure_set(v___f_1782_, 0, v_decl_1755_);
lean_closure_set(v___f_1782_, 1, v_declName_1750_);
lean_closure_set(v___f_1782_, 2, v_type_1751_);
lean_closure_set(v___f_1782_, 3, v_value_1752_);
lean_closure_set(v___f_1782_, 4, v___x_1781_);
lean_closure_set(v___f_1782_, 5, v___x_1760_);
lean_closure_set(v___f_1782_, 6, v___x_1777_);
lean_closure_set(v___f_1782_, 7, v_toPure_1734_);
lean_closure_set(v___f_1782_, 8, v_us_1761_);
lean_closure_set(v___f_1782_, 9, v___x_1745_);
lean_closure_set(v___f_1782_, 10, v_x_1757_);
lean_closure_set(v___f_1782_, 11, v_i_1683_);
lean_closure_set(v___f_1782_, 12, v_xs_1684_);
lean_closure_set(v___f_1782_, 13, v_inst_1675_);
lean_closure_set(v___f_1782_, 14, v_inst_1676_);
lean_closure_set(v___f_1782_, 15, v_inst_1677_);
lean_closure_set(v___f_1782_, 16, v_inst_1678_);
lean_closure_set(v___f_1782_, 17, v_info_1679_);
lean_closure_set(v___f_1782_, 18, v_fixed_1680_);
lean_closure_set(v___f_1782_, 19, v_used_1681_);
lean_closure_set(v___f_1782_, 20, v_body_1753_);
lean_closure_set(v___f_1782_, 21, v_toBind_1733_);
lean_closure_set(v___f_1782_, 22, v_withNewLemmas_1779_);
v___f_1783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1783_, 0, v___f_1782_);
v___x_1784_ = lean_box(v___x_1737_);
lean_inc_ref(v_toMonadRef_1728_);
lean_inc_ref(v_val_1758_);
lean_inc_ref(v___f_1783_);
v___f_1785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_1785_, 0, v_level_1756_);
lean_closure_set(v___f_1785_, 1, v___x_1759_);
lean_closure_set(v___f_1785_, 2, v_type_1751_);
lean_closure_set(v___f_1785_, 3, v_value_1752_);
lean_closure_set(v___f_1785_, 4, v___x_1777_);
lean_closure_set(v___f_1785_, 5, v_toPure_1734_);
lean_closure_set(v___f_1785_, 6, v_toBind_1733_);
lean_closure_set(v___f_1785_, 7, v___f_1783_);
lean_closure_set(v___f_1785_, 8, v_xs_1684_);
lean_closure_set(v___f_1785_, 9, v___x_1784_);
lean_closure_set(v___f_1785_, 10, v___f_1783_);
lean_closure_set(v___f_1785_, 11, v_declName_1750_);
lean_closure_set(v___f_1785_, 12, v_val_1758_);
lean_closure_set(v___f_1785_, 13, v___x_1724_);
lean_closure_set(v___f_1785_, 14, v___x_1725_);
lean_closure_set(v___f_1785_, 15, v_toMonadRef_1728_);
lean_closure_set(v___f_1785_, 16, v___x_1735_);
lean_closure_set(v___f_1785_, 17, v_inst_1676_);
v___x_1786_ = lean_apply_1(v_simp_1780_, v_val_1758_);
v___x_1787_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1786_, v___f_1785_);
return v___x_1787_;
}
else
{
uint8_t v___x_1788_; 
lean_dec(v___x_1745_);
v___x_1788_ = lean_unbox(v___x_1777_);
v___y_1763_ = v___x_1774_;
v___y_1764_ = v___x_1788_;
goto v___jp_1762_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1682_, 4);
lean_dec(v_toPure_1734_);
lean_dec(v_toBind_1733_);
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_xs_1684_);
lean_dec(v_i_1683_);
lean_dec_ref(v_used_1681_);
lean_dec_ref(v_fixed_1680_);
lean_dec_ref(v_info_1679_);
lean_dec_ref(v_inst_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec(v_inst_1676_);
lean_dec_ref(v_inst_1675_);
goto v___jp_1746_;
}
}
else
{
lean_dec(v_toPure_1734_);
lean_dec(v_toBind_1733_);
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_xs_1684_);
lean_dec(v_i_1683_);
lean_dec_ref(v_e_1682_);
lean_dec_ref(v_used_1681_);
lean_dec_ref(v_fixed_1680_);
lean_dec_ref(v_info_1679_);
lean_dec_ref(v_inst_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec(v_inst_1676_);
lean_dec_ref(v_inst_1675_);
goto v___jp_1746_;
}
v___jp_1746_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15);
v___x_1748_ = l_panic___redArg(v___x_1745_, v___x_1747_);
lean_dec(v___x_1745_);
return v___x_1748_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1805_, lean_object* v_declName_1806_, lean_object* v_type_1807_, lean_object* v_value_1808_, lean_object* v_us_1809_, lean_object* v___x_1810_, uint8_t v___x_1811_, lean_object* v_toPure_1812_, lean_object* v_i_1813_, lean_object* v_xs_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_info_1819_, lean_object* v_fixed_1820_, lean_object* v_used_1821_, lean_object* v_body_1822_, lean_object* v_toBind_1823_, lean_object* v_____r_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v_x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1826_ = l_Lean_mkConst(v___x_1825_, v___x_1805_);
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = lean_box(v___x_1811_);
v___f_1829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1829_, 0, v___x_1827_);
lean_closure_set(v___f_1829_, 1, v_declName_1806_);
lean_closure_set(v___f_1829_, 2, v_type_1807_);
lean_closure_set(v___f_1829_, 3, v_value_1808_);
lean_closure_set(v___f_1829_, 4, v_us_1809_);
lean_closure_set(v___f_1829_, 5, v___x_1810_);
lean_closure_set(v___f_1829_, 6, v___x_1828_);
lean_closure_set(v___f_1829_, 7, v_toPure_1812_);
v___x_1830_ = lean_nat_add(v_i_1813_, v___x_1827_);
v___x_1831_ = lean_array_push(v_xs_1814_, v_x_1826_);
v___x_1832_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1815_, v_inst_1816_, v_inst_1817_, v_inst_1818_, v_info_1819_, v_fixed_1820_, v_used_1821_, v_body_1822_, v___x_1830_, v___x_1831_);
v___x_1833_ = lean_apply_4(v_toBind_1823_, lean_box(0), lean_box(0), v___x_1832_, v___f_1829_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_info_1839_, lean_object* v_fixed_1840_, lean_object* v_used_1841_, lean_object* v_e_1842_, lean_object* v_i_1843_, lean_object* v_xs_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1835_, v_inst_1836_, v_inst_1837_, v_inst_1838_, v_info_1839_, v_fixed_1840_, v_used_1841_, v_e_1842_, v_i_1843_, v_xs_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_1846_){
_start:
{
switch(v_x_1846_)
{
case 0:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_unsigned_to_nat(0u);
return v___x_1847_;
}
case 1:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_unsigned_to_nat(1u);
return v___x_1848_;
}
default: 
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_unsigned_to_nat(2u);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_1850_){
_start:
{
uint8_t v_x_boxed_1851_; lean_object* v_res_1852_; 
v_x_boxed_1851_ = lean_unbox(v_x_1850_);
v_res_1852_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_1853_){
_start:
{
lean_inc(v_k_1853_);
return v_k_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_1854_);
lean_dec(v_k_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_1856_, lean_object* v_ctorIdx_1857_, uint8_t v_t_1858_, lean_object* v_h_1859_, lean_object* v_k_1860_){
_start:
{
lean_inc(v_k_1860_);
return v_k_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_1861_, lean_object* v_ctorIdx_1862_, lean_object* v_t_1863_, lean_object* v_h_1864_, lean_object* v_k_1865_){
_start:
{
uint8_t v_t_boxed_1866_; lean_object* v_res_1867_; 
v_t_boxed_1866_ = lean_unbox(v_t_1863_);
v_res_1867_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_1861_, v_ctorIdx_1862_, v_t_boxed_1866_, v_h_1864_, v_k_1865_);
lean_dec(v_k_1865_);
lean_dec(v_ctorIdx_1862_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_1868_){
_start:
{
lean_inc(v_no_1868_);
return v_no_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_1869_);
lean_dec(v_no_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_1871_, uint8_t v_t_1872_, lean_object* v_h_1873_, lean_object* v_no_1874_){
_start:
{
lean_inc(v_no_1874_);
return v_no_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_1875_, lean_object* v_t_1876_, lean_object* v_h_1877_, lean_object* v_no_1878_){
_start:
{
uint8_t v_t_boxed_1879_; lean_object* v_res_1880_; 
v_t_boxed_1879_ = lean_unbox(v_t_1876_);
v_res_1880_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_1875_, v_t_boxed_1879_, v_h_1877_, v_no_1878_);
lean_dec(v_no_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_1881_){
_start:
{
lean_inc(v_singlePass_1881_);
return v_singlePass_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_1882_);
lean_dec(v_singlePass_1882_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_1884_, uint8_t v_t_1885_, lean_object* v_h_1886_, lean_object* v_singlePass_1887_){
_start:
{
lean_inc(v_singlePass_1887_);
return v_singlePass_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_1888_, lean_object* v_t_1889_, lean_object* v_h_1890_, lean_object* v_singlePass_1891_){
_start:
{
uint8_t v_t_boxed_1892_; lean_object* v_res_1893_; 
v_t_boxed_1892_ = lean_unbox(v_t_1889_);
v_res_1893_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_1888_, v_t_boxed_1892_, v_h_1890_, v_singlePass_1891_);
lean_dec(v_singlePass_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_1894_){
_start:
{
lean_inc(v_twoPasses_1894_);
return v_twoPasses_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_1895_);
lean_dec(v_twoPasses_1895_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_1897_, uint8_t v_t_1898_, lean_object* v_h_1899_, lean_object* v_twoPasses_1900_){
_start:
{
lean_inc(v_twoPasses_1900_);
return v_twoPasses_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_1901_, lean_object* v_t_1902_, lean_object* v_h_1903_, lean_object* v_twoPasses_1904_){
_start:
{
uint8_t v_t_boxed_1905_; lean_object* v_res_1906_; 
v_t_boxed_1905_ = lean_unbox(v_t_1902_);
v_res_1906_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_1901_, v_t_boxed_1905_, v_h_1903_, v_twoPasses_1904_);
lean_dec(v_twoPasses_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_1907_, lean_object* v_b_1908_, lean_object* v_c_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
v___x_1915_ = lean_apply_7(v_k_1907_, v_b_1908_, v_c_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, lean_box(0));
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_1916_, lean_object* v_b_1917_, lean_object* v_c_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_1916_, v_b_1917_, v_c_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_1925_, lean_object* v_k_1926_, uint8_t v_cleanupAnnotations_1927_, uint8_t v_preserveNondepLet_1928_, uint8_t v_nondepLetOnly_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___f_1935_; uint8_t v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1935_, 0, v_k_1926_);
v___x_1936_ = 0;
v___x_1937_ = 1;
v___x_1938_ = lean_box(0);
v___x_1939_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1925_, v___x_1936_, v___x_1937_, v_preserveNondepLet_1928_, v_nondepLetOnly_1929_, v___x_1938_, v___f_1935_, v_cleanupAnnotations_1927_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1939_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1939_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_1956_, lean_object* v_k_1957_, lean_object* v_cleanupAnnotations_1958_, lean_object* v_preserveNondepLet_1959_, lean_object* v_nondepLetOnly_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1966_; uint8_t v_preserveNondepLet_boxed_1967_; uint8_t v_nondepLetOnly_boxed_1968_; lean_object* v_res_1969_; 
v_cleanupAnnotations_boxed_1966_ = lean_unbox(v_cleanupAnnotations_1958_);
v_preserveNondepLet_boxed_1967_ = lean_unbox(v_preserveNondepLet_1959_);
v_nondepLetOnly_boxed_1968_ = lean_unbox(v_nondepLetOnly_1960_);
v_res_1969_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1956_, v_k_1957_, v_cleanupAnnotations_boxed_1966_, v_preserveNondepLet_boxed_1967_, v_nondepLetOnly_boxed_1968_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_1970_, lean_object* v_e_1971_, lean_object* v_k_1972_, uint8_t v_cleanupAnnotations_1973_, uint8_t v_preserveNondepLet_1974_, uint8_t v_nondepLetOnly_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1971_, v_k_1972_, v_cleanupAnnotations_1973_, v_preserveNondepLet_1974_, v_nondepLetOnly_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_1982_, lean_object* v_e_1983_, lean_object* v_k_1984_, lean_object* v_cleanupAnnotations_1985_, lean_object* v_preserveNondepLet_1986_, lean_object* v_nondepLetOnly_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1993_; uint8_t v_preserveNondepLet_boxed_1994_; uint8_t v_nondepLetOnly_boxed_1995_; lean_object* v_res_1996_; 
v_cleanupAnnotations_boxed_1993_ = lean_unbox(v_cleanupAnnotations_1985_);
v_preserveNondepLet_boxed_1994_ = lean_unbox(v_preserveNondepLet_1986_);
v_nondepLetOnly_boxed_1995_ = lean_unbox(v_nondepLetOnly_1987_);
v_res_1996_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_1982_, v_e_1983_, v_k_1984_, v_cleanupAnnotations_boxed_1993_, v_preserveNondepLet_boxed_1994_, v_nondepLetOnly_boxed_1995_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_1997_, lean_object* v_a_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_snd_2003_; lean_object* v_fst_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2059_; 
v_snd_2003_ = lean_ctor_get(v_a_1998_, 1);
v_fst_2004_ = lean_ctor_get(v_a_1998_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2006_ = v_a_1998_;
v_isShared_2007_ = v_isSharedCheck_2059_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2004_);
lean_dec(v_a_1998_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2059_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_fst_2008_; lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2058_; 
v_fst_2008_ = lean_ctor_get(v_snd_2003_, 0);
v_snd_2009_ = lean_ctor_get(v_snd_2003_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_snd_2003_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2011_ = v_snd_2003_;
v_isShared_2012_ = v_isSharedCheck_2058_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_inc(v_fst_2008_);
lean_dec(v_snd_2003_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2058_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_nat_dec_lt(v___x_2013_, v_snd_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2016_; 
if (v_isShared_2012_ == 0)
{
v___x_2016_ = v___x_2011_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_fst_2008_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_snd_2009_);
v___x_2016_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___x_2016_);
v___x_2018_ = v___x_2006_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_fst_2004_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
}
else
{
lean_object* v_fvarSet_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_fvarSet_2022_ = lean_ctor_get(v_fst_2004_, 1);
v___x_2023_ = l_Lean_instInhabitedExpr;
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_sub(v_snd_2009_, v___x_2024_);
lean_dec(v_snd_2009_);
v___x_2026_ = lean_array_get_borrowed(v___x_2023_, v_xs_1997_, v___x_2025_);
v___x_2027_ = l_Lean_Expr_fvarId_x21(v___x_2026_);
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2027_, v_fvarSet_2022_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2030_; 
lean_dec(v___x_2027_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v___x_2025_);
v___x_2030_ = v___x_2011_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_fst_2008_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2025_);
v___x_2030_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___x_2030_);
v___x_2032_ = v___x_2006_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_fst_2004_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
v_a_1998_ = v___x_2032_;
goto _start;
}
}
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_FVarId_getDecl___redArg(v___x_2027_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = l_Lean_LocalDecl_type(v_a_2037_);
v___x_2039_ = l_Lean_collectFVars(v_fst_2004_, v___x_2038_);
v___x_2040_ = l_Lean_LocalDecl_value(v_a_2037_, v___x_2014_);
lean_dec(v_a_2037_);
v___x_2041_ = l_Lean_collectFVars(v___x_2039_, v___x_2040_);
lean_inc(v___x_2026_);
v___x_2042_ = lean_array_push(v_fst_2008_, v___x_2026_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v___x_2025_);
lean_ctor_set(v___x_2011_, 0, v___x_2042_);
v___x_2044_ = v___x_2011_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2025_);
v___x_2044_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___x_2044_);
lean_ctor_set(v___x_2006_, 0, v___x_2041_);
v___x_2046_ = v___x_2006_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
v_a_1998_ = v___x_2046_;
goto _start;
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v___x_2025_);
lean_del_object(v___x_2011_);
lean_dec(v_fst_2008_);
lean_del_object(v___x_2006_);
lean_dec(v_fst_2004_);
v_a_2050_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2036_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2036_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2060_, lean_object* v_a_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2060_, v_a_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v_xs_2060_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2067_, lean_object* v_e_2068_, lean_object* v_xs_2069_, lean_object* v_body_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_s_2079_; lean_object* v_i_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2076_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2067_);
lean_ctor_set(v___x_2078_, 2, v___x_2077_);
lean_inc_ref(v_body_2070_);
v_s_2079_ = l_Lean_collectFVars(v___x_2078_, v_body_2070_);
v_i_2080_ = lean_array_get_size(v_xs_2069_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2077_);
lean_ctor_set(v___x_2081_, 1, v_i_2080_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v_s_2079_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2069_, v___x_2082_, v___y_2071_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2099_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2099_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2099_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_snd_2088_; lean_object* v_fst_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_snd_2088_ = lean_ctor_get(v_a_2084_, 1);
lean_inc(v_snd_2088_);
lean_dec(v_a_2084_);
v_fst_2089_ = lean_ctor_get(v_snd_2088_, 0);
lean_inc(v_fst_2089_);
lean_dec(v_snd_2088_);
v___x_2090_ = lean_array_get_size(v_fst_2089_);
v___x_2091_ = lean_nat_dec_eq(v___x_2090_, v_i_2080_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; 
lean_del_object(v___x_2086_);
lean_dec_ref(v_e_2068_);
v___x_2092_ = 1;
v___x_2093_ = l_Array_reverse___redArg(v_fst_2089_);
v___x_2094_ = 1;
v___x_2095_ = l_Lean_Meta_mkLetFVars(v___x_2093_, v_body_2070_, v___x_2092_, v___x_2091_, v___x_2094_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec_ref(v___x_2093_);
return v___x_2095_;
}
else
{
lean_object* v___x_2097_; 
lean_dec(v_fst_2089_);
lean_dec_ref(v_body_2070_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_e_2068_);
v___x_2097_ = v___x_2086_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_e_2068_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_body_2070_);
lean_dec_ref(v_e_2068_);
v_a_2100_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2083_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2083_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2108_, lean_object* v_e_2109_, lean_object* v_xs_2110_, lean_object* v_body_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2108_, v_e_2109_, v_xs_2110_, v_body_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_xs_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___f_2125_; uint8_t v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2124_ = lean_box(1);
lean_inc_ref(v_e_2118_);
v___f_2125_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2125_, 0, v___x_2124_);
lean_closure_set(v___f_2125_, 1, v_e_2118_);
v___x_2126_ = 0;
v___x_2127_ = 1;
v___x_2128_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2118_, v___f_2125_, v___x_2126_, v___x_2127_, v___x_2126_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_Meta_zetaUnused(v_e_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2136_, lean_object* v_inst_2137_, lean_object* v_a_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2136_, v_a_2138_, v___y_2139_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2145_, lean_object* v_inst_2146_, lean_object* v_a_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2145_, v_inst_2146_, v_a_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v_xs_2145_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2158_, lean_object* v_source_2159_, lean_object* v_result_2160_, uint8_t v_keepUnused_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
uint8_t v_modified_2167_; 
v_modified_2167_ = lean_ctor_get_uint8(v_result_2160_, sizeof(void*)*5);
if (v_modified_2167_ == 0)
{
if (v_keepUnused_2161_ == 0)
{
lean_object* v_exprType_2168_; lean_object* v___x_2169_; 
v_exprType_2168_ = lean_ctor_get(v_result_2160_, 1);
lean_inc_ref(v_exprType_2168_);
lean_dec_ref(v_result_2160_);
lean_inc_ref(v_source_2159_);
v___x_2169_ = l_Lean_Meta_zetaUnused(v_source_2159_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2188_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2188_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2188_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_expr_eqv(v_a_2170_, v_source_2159_);
lean_dec_ref(v_source_2159_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_u_2158_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_mkConst(v___x_2175_, v___x_2177_);
lean_inc(v_a_2170_);
v___x_2179_ = l_Lean_mkAppB(v___x_2178_, v_exprType_2168_, v_a_2170_);
v___x_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2170_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2180_);
v___x_2182_ = v___x_2172_;
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
else
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec(v_a_2170_);
lean_dec_ref(v_exprType_2168_);
lean_dec(v_u_2158_);
v___x_2184_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2184_);
v___x_2186_ = v___x_2172_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_exprType_2168_);
lean_dec_ref(v_source_2159_);
lean_dec(v_u_2158_);
v_a_2189_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2169_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2169_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_result_2160_);
lean_dec_ref(v_source_2159_);
lean_dec(v_u_2158_);
v___x_2197_ = lean_box(0);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
else
{
lean_object* v_expr_2199_; lean_object* v_exprType_2200_; lean_object* v_exprInit_2201_; lean_object* v_exprResult_2202_; lean_object* v_proof_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v_proof_2211_; 
v_expr_2199_ = lean_ctor_get(v_result_2160_, 0);
lean_inc_ref(v_expr_2199_);
v_exprType_2200_ = lean_ctor_get(v_result_2160_, 1);
lean_inc_ref_n(v_exprType_2200_, 3);
v_exprInit_2201_ = lean_ctor_get(v_result_2160_, 2);
lean_inc_ref(v_exprInit_2201_);
v_exprResult_2202_ = lean_ctor_get(v_result_2160_, 3);
lean_inc_ref_n(v_exprResult_2202_, 2);
v_proof_2203_ = lean_ctor_get(v_result_2160_, 4);
lean_inc_ref(v_proof_2203_);
lean_dec_ref(v_result_2160_);
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_u_2158_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
lean_inc_ref(v___x_2206_);
v___x_2207_ = l_Lean_mkConst(v___x_2204_, v___x_2206_);
lean_inc_ref(v___x_2207_);
v___x_2208_ = l_Lean_mkApp3(v___x_2207_, v_exprType_2200_, v_exprInit_2201_, v_expr_2199_);
v___x_2209_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2203_, v___x_2208_);
lean_inc_ref(v_source_2159_);
v___x_2210_ = l_Lean_mkApp3(v___x_2207_, v_exprType_2200_, v_source_2159_, v_exprResult_2202_);
v_proof_2211_ = l_Lean_Meta_mkExpectedPropHint(v___x_2209_, v___x_2210_);
if (v_keepUnused_2161_ == 0)
{
lean_object* v___x_2212_; 
lean_inc_ref(v_exprResult_2202_);
v___x_2212_ = l_Lean_Meta_zetaUnused(v_exprResult_2202_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2232_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2232_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2232_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
uint8_t v___x_2217_; 
v___x_2217_ = lean_expr_eqv(v_a_2213_, v_exprResult_2202_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2206_);
v___x_2219_ = l_Lean_mkConst(v___x_2218_, v___x_2206_);
v___x_2220_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2221_ = l_Lean_mkConst(v___x_2220_, v___x_2206_);
lean_inc_n(v_a_2213_, 2);
lean_inc_ref(v_exprType_2200_);
v___x_2222_ = l_Lean_mkAppB(v___x_2221_, v_exprType_2200_, v_a_2213_);
v___x_2223_ = l_Lean_mkApp6(v___x_2219_, v_exprType_2200_, v_source_2159_, v_exprResult_2202_, v_a_2213_, v_proof_2211_, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_a_2213_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2224_);
v___x_2226_ = v___x_2215_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_dec(v_a_2213_);
lean_dec_ref_known(v___x_2206_, 2);
lean_dec_ref(v_exprType_2200_);
lean_dec_ref(v_source_2159_);
v___x_2228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_exprResult_2202_);
lean_ctor_set(v___x_2228_, 1, v_proof_2211_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2228_);
v___x_2230_ = v___x_2215_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_proof_2211_);
lean_dec_ref_known(v___x_2206_, 2);
lean_dec_ref(v_exprResult_2202_);
lean_dec_ref(v_exprType_2200_);
lean_dec_ref(v_source_2159_);
v_a_2233_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2212_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2212_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref_known(v___x_2206_, 2);
lean_dec_ref(v_exprType_2200_);
lean_dec_ref(v_source_2159_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_exprResult_2202_);
lean_ctor_set(v___x_2241_, 1, v_proof_2211_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2243_, lean_object* v_source_2244_, lean_object* v_result_2245_, lean_object* v_keepUnused_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
uint8_t v_keepUnused_boxed_2252_; lean_object* v_res_2253_; 
v_keepUnused_boxed_2252_ = lean_unbox(v_keepUnused_2246_);
v_res_2253_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2243_, v_source_2244_, v_result_2245_, v_keepUnused_boxed_2252_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2254_, lean_object* v_e_2255_, lean_object* v_inst_2256_, uint8_t v_zetaUnusedMode_2257_, uint8_t v___x_2258_, uint8_t v___x_2259_, lean_object* v_r_2260_){
_start:
{
uint8_t v___y_2262_; 
switch(v_zetaUnusedMode_2257_)
{
case 0:
{
v___y_2262_ = v___x_2258_;
goto v___jp_2261_;
}
case 1:
{
v___y_2262_ = v___x_2258_;
goto v___jp_2261_;
}
default: 
{
v___y_2262_ = v___x_2259_;
goto v___jp_2261_;
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_box(v___y_2262_);
v___x_2264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2264_, 0, v_level_2254_);
lean_closure_set(v___x_2264_, 1, v_e_2255_);
lean_closure_set(v___x_2264_, 2, v_r_2260_);
lean_closure_set(v___x_2264_, 3, v___x_2263_);
v___x_2265_ = lean_apply_2(v_inst_2256_, lean_box(0), v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2266_, lean_object* v_e_2267_, lean_object* v_inst_2268_, lean_object* v_zetaUnusedMode_2269_, lean_object* v___x_2270_, lean_object* v___x_2271_, lean_object* v_r_2272_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2273_; uint8_t v___x_289__boxed_2274_; uint8_t v___x_290__boxed_2275_; lean_object* v_res_2276_; 
v_zetaUnusedMode_boxed_2273_ = lean_unbox(v_zetaUnusedMode_2269_);
v___x_289__boxed_2274_ = lean_unbox(v___x_2270_);
v___x_290__boxed_2275_ = lean_unbox(v___x_2271_);
v_res_2276_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2266_, v_e_2267_, v_inst_2268_, v_zetaUnusedMode_boxed_2273_, v___x_289__boxed_2274_, v___x_290__boxed_2275_, v_r_2272_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_info_2282_, lean_object* v_e_2283_, lean_object* v___x_2284_, lean_object* v_toBind_2285_, lean_object* v___f_2286_, lean_object* v_____x_2287_){
_start:
{
lean_object* v_fst_2288_; lean_object* v_snd_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_fst_2288_ = lean_ctor_get(v_____x_2287_, 0);
lean_inc(v_fst_2288_);
v_snd_2289_ = lean_ctor_get(v_____x_2287_, 1);
lean_inc(v_snd_2289_);
lean_dec_ref(v_____x_2287_);
v___x_2290_ = lean_mk_empty_array_with_capacity(v___x_2277_);
v___x_2291_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2278_, v_inst_2279_, v_inst_2280_, v_inst_2281_, v_info_2282_, v_fst_2288_, v_snd_2289_, v_e_2283_, v___x_2284_, v___x_2290_);
v___x_2292_ = lean_apply_4(v_toBind_2285_, lean_box(0), lean_box(0), v___x_2291_, v___f_2286_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_info_2298_, lean_object* v_e_2299_, lean_object* v___x_2300_, lean_object* v_toBind_2301_, lean_object* v___f_2302_, lean_object* v_____x_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2293_, v_inst_2294_, v_inst_2295_, v_inst_2296_, v_inst_2297_, v_info_2298_, v_e_2299_, v___x_2300_, v_toBind_2301_, v___f_2302_, v_____x_2303_);
lean_dec(v___x_2293_);
return v_res_2304_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2307_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2308_ = lean_unsigned_to_nat(2u);
v___x_2309_ = lean_unsigned_to_nat(456u);
v___x_2310_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2312_ = l_mkPanicMessageWithDecl(v___x_2311_, v___x_2310_, v___x_2309_, v___x_2308_, v___x_2307_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2313_, lean_object* v_inst_2314_, uint8_t v_zetaUnusedMode_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_toBind_2319_, lean_object* v___x_2320_, lean_object* v_info_2321_){
_start:
{
lean_object* v_haveInfo_2322_; lean_object* v_level_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_haveInfo_2322_ = lean_ctor_get(v_info_2321_, 0);
v_level_2323_ = lean_ctor_get(v_info_2321_, 5);
v___x_2324_ = lean_array_get_size(v_haveInfo_2322_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_nat_dec_eq(v___x_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___f_2331_; lean_object* v___f_2332_; uint8_t v___y_2334_; 
v___x_2327_ = 1;
v___x_2328_ = lean_box(v_zetaUnusedMode_2315_);
v___x_2329_ = lean_box(v___x_2327_);
v___x_2330_ = lean_box(v___x_2326_);
lean_inc_n(v_inst_2314_, 2);
lean_inc_ref(v_e_2313_);
lean_inc(v_level_2323_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2331_, 0, v_level_2323_);
lean_closure_set(v___f_2331_, 1, v_e_2313_);
lean_closure_set(v___f_2331_, 2, v_inst_2314_);
lean_closure_set(v___f_2331_, 3, v___x_2328_);
lean_closure_set(v___f_2331_, 4, v___x_2329_);
lean_closure_set(v___f_2331_, 5, v___x_2330_);
lean_inc(v_toBind_2319_);
lean_inc_ref(v_info_2321_);
v___f_2332_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2332_, 0, v___x_2324_);
lean_closure_set(v___f_2332_, 1, v_inst_2316_);
lean_closure_set(v___f_2332_, 2, v_inst_2314_);
lean_closure_set(v___f_2332_, 3, v_inst_2317_);
lean_closure_set(v___f_2332_, 4, v_inst_2318_);
lean_closure_set(v___f_2332_, 5, v_info_2321_);
lean_closure_set(v___f_2332_, 6, v_e_2313_);
lean_closure_set(v___f_2332_, 7, v___x_2325_);
lean_closure_set(v___f_2332_, 8, v_toBind_2319_);
lean_closure_set(v___f_2332_, 9, v___f_2331_);
switch(v_zetaUnusedMode_2315_)
{
case 0:
{
v___y_2334_ = v___x_2327_;
goto v___jp_2333_;
}
case 2:
{
v___y_2334_ = v___x_2327_;
goto v___jp_2333_;
}
default: 
{
v___y_2334_ = v___x_2326_;
goto v___jp_2333_;
}
}
v___jp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2335_ = lean_box(v___y_2334_);
v___x_2336_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2336_, 0, v_info_2321_);
lean_closure_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_apply_2(v_inst_2314_, lean_box(0), v___x_2336_);
v___x_2338_ = lean_apply_4(v_toBind_2319_, lean_box(0), lean_box(0), v___x_2337_, v___f_2332_);
return v___x_2338_;
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec_ref(v_info_2321_);
lean_dec(v_toBind_2319_);
lean_dec_ref(v_inst_2318_);
lean_dec_ref(v_inst_2317_);
lean_dec_ref(v_inst_2316_);
lean_dec(v_inst_2314_);
lean_dec_ref(v_e_2313_);
v___x_2339_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2340_ = l_panic___redArg(v___x_2320_, v___x_2339_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2341_, lean_object* v_inst_2342_, lean_object* v_zetaUnusedMode_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_toBind_2347_, lean_object* v___x_2348_, lean_object* v_info_2349_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2350_; lean_object* v_res_2351_; 
v_zetaUnusedMode_boxed_2350_ = lean_unbox(v_zetaUnusedMode_2343_);
v_res_2351_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2341_, v_inst_2342_, v_zetaUnusedMode_boxed_2350_, v_inst_2344_, v_inst_2345_, v_inst_2346_, v_toBind_2347_, v___x_2348_, v_info_2349_);
lean_dec(v___x_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_e_2356_, uint8_t v_zetaUnusedMode_2357_){
_start:
{
lean_object* v_toBind_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; 
v_toBind_2358_ = lean_ctor_get(v_inst_2352_, 1);
lean_inc_n(v_toBind_2358_, 2);
v___x_2359_ = lean_box(0);
lean_inc_ref(v_e_2356_);
v___x_2360_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2360_, 0, v_e_2356_);
lean_inc(v_inst_2353_);
v___x_2361_ = lean_apply_2(v_inst_2353_, lean_box(0), v___x_2360_);
lean_inc_ref(v_inst_2352_);
v___x_2362_ = l_instInhabitedOfMonad___redArg(v_inst_2352_, v___x_2359_);
v___x_2363_ = lean_box(v_zetaUnusedMode_2357_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2364_, 0, v_e_2356_);
lean_closure_set(v___f_2364_, 1, v_inst_2353_);
lean_closure_set(v___f_2364_, 2, v___x_2363_);
lean_closure_set(v___f_2364_, 3, v_inst_2352_);
lean_closure_set(v___f_2364_, 4, v_inst_2354_);
lean_closure_set(v___f_2364_, 5, v_inst_2355_);
lean_closure_set(v___f_2364_, 6, v_toBind_2358_);
lean_closure_set(v___f_2364_, 7, v___x_2362_);
v___x_2365_ = lean_apply_4(v_toBind_2358_, lean_box(0), lean_box(0), v___x_2361_, v___f_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_e_2370_, lean_object* v_zetaUnusedMode_2371_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2372_; lean_object* v_res_2373_; 
v_zetaUnusedMode_boxed_2372_ = lean_unbox(v_zetaUnusedMode_2371_);
v_res_2373_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2366_, v_inst_2367_, v_inst_2368_, v_inst_2369_, v_e_2370_, v_zetaUnusedMode_boxed_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_e_2379_, uint8_t v_zetaUnusedMode_2380_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2375_, v_inst_2376_, v_inst_2377_, v_inst_2378_, v_e_2379_, v_zetaUnusedMode_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_e_2387_, lean_object* v_zetaUnusedMode_2388_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2389_; lean_object* v_res_2390_; 
v_zetaUnusedMode_boxed_2389_ = lean_unbox(v_zetaUnusedMode_2388_);
v_res_2390_ = l_Lean_Meta_simpHaveTelescope(v_m_2382_, v_inst_2383_, v_inst_2384_, v_inst_2385_, v_inst_2386_, v_e_2387_, v_zetaUnusedMode_boxed_2389_);
return v_res_2390_;
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
