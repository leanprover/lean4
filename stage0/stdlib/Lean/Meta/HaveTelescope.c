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
lean_object* v___x_341_; lean_object* v_ngen_342_; lean_object* v_namePrefix_343_; lean_object* v_idx_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_373_; 
v___x_341_ = lean_st_ref_get(v___y_339_);
v_ngen_342_ = lean_ctor_get(v___x_341_, 2);
lean_inc_ref(v_ngen_342_);
lean_dec(v___x_341_);
v_namePrefix_343_ = lean_ctor_get(v_ngen_342_, 0);
v_idx_344_ = lean_ctor_get(v_ngen_342_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_ngen_342_);
if (v_isSharedCheck_373_ == 0)
{
v___x_346_ = v_ngen_342_;
v_isShared_347_ = v_isSharedCheck_373_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_idx_344_);
lean_inc(v_namePrefix_343_);
lean_dec(v_ngen_342_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_373_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v_nextMacroScope_350_; lean_object* v_auxDeclNGen_351_; lean_object* v_traceState_352_; lean_object* v_cache_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_371_; 
v___x_348_ = lean_st_ref_take(v___y_339_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_350_ = lean_ctor_get(v___x_348_, 1);
v_auxDeclNGen_351_ = lean_ctor_get(v___x_348_, 3);
v_traceState_352_ = lean_ctor_get(v___x_348_, 4);
v_cache_353_ = lean_ctor_get(v___x_348_, 5);
v_messages_354_ = lean_ctor_get(v___x_348_, 6);
v_infoState_355_ = lean_ctor_get(v___x_348_, 7);
v_snapshotTasks_356_ = lean_ctor_get(v___x_348_, 8);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_348_, 2);
lean_dec(v_unused_372_);
v___x_358_ = v___x_348_;
v_isShared_359_ = v_isSharedCheck_371_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_cache_353_);
lean_inc(v_traceState_352_);
lean_inc(v_auxDeclNGen_351_);
lean_inc(v_nextMacroScope_350_);
lean_inc(v_env_349_);
lean_dec(v___x_348_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_371_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_r_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
lean_inc(v_idx_344_);
lean_inc(v_namePrefix_343_);
v_r_360_ = l_Lean_Name_num___override(v_namePrefix_343_, v_idx_344_);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_add(v_idx_344_, v___x_361_);
lean_dec(v_idx_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_362_);
v___x_364_ = v___x_346_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_namePrefix_343_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_362_);
v___x_364_ = v_reuseFailAlloc_370_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 2, v___x_364_);
v___x_366_ = v___x_358_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_env_349_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_nextMacroScope_350_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_traceState_352_);
lean_ctor_set(v_reuseFailAlloc_369_, 5, v_cache_353_);
lean_ctor_set(v_reuseFailAlloc_369_, 6, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_369_, 7, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_369_, 8, v_snapshotTasks_356_);
v___x_366_ = v_reuseFailAlloc_369_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_st_ref_put(v___y_339_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_r_360_);
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_374_);
lean_dec(v___y_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v___x_382_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_380_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_397_, lean_object* v_numHaves_398_, lean_object* v_info_399_, lean_object* v_lctx_400_, lean_object* v_fvars_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; 
v___x_407_ = lean_box(1);
if (lean_obj_tag(v_e_397_) == 8)
{
uint8_t v_nondep_417_; 
v_nondep_417_ = lean_ctor_get_uint8(v_e_397_, sizeof(void*)*4 + 8);
if (v_nondep_417_ == 1)
{
lean_object* v_declName_418_; lean_object* v_type_419_; lean_object* v_value_420_; lean_object* v_body_421_; lean_object* v_t_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_declName_418_ = lean_ctor_get(v_e_397_, 0);
lean_inc(v_declName_418_);
v_type_419_ = lean_ctor_get(v_e_397_, 1);
lean_inc_ref(v_type_419_);
v_value_420_ = lean_ctor_get(v_e_397_, 2);
lean_inc_ref(v_value_420_);
v_body_421_ = lean_ctor_get(v_e_397_, 3);
lean_inc_ref(v_body_421_);
lean_dec_ref_known(v_e_397_, 4);
v_t_422_ = lean_expr_instantiate_rev(v_type_419_, v_fvars_401_);
lean_inc_ref(v_t_422_);
v___x_423_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_423_, 0, v_t_422_);
lean_inc_ref(v_lctx_400_);
v___x_424_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_400_, v___x_423_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v_haveInfo_428_; lean_object* v_bodyDeps_429_; lean_object* v_bodyTypeDeps_430_; lean_object* v_body_431_; lean_object* v_bodyType_432_; lean_object* v_level_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_454_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v_haveInfo_428_ = lean_ctor_get(v_info_399_, 0);
v_bodyDeps_429_ = lean_ctor_get(v_info_399_, 1);
v_bodyTypeDeps_430_ = lean_ctor_get(v_info_399_, 2);
v_body_431_ = lean_ctor_get(v_info_399_, 3);
v_bodyType_432_ = lean_ctor_get(v_info_399_, 4);
v_level_433_ = lean_ctor_get(v_info_399_, 5);
v_isSharedCheck_454_ = !lean_is_exclusive(v_info_399_);
if (v_isSharedCheck_454_ == 0)
{
v___x_435_ = v_info_399_;
v_isShared_436_ = v_isSharedCheck_454_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_level_433_);
lean_inc(v_bodyType_432_);
lean_inc(v_body_431_);
lean_inc(v_bodyTypeDeps_430_);
lean_inc(v_bodyDeps_429_);
lean_inc(v_haveInfo_428_);
lean_dec(v_info_399_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_454_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_typeBackDeps_437_; lean_object* v_valueBackDeps_438_; lean_object* v_v_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v_typeBackDeps_437_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_398_, v_type_419_);
lean_inc_ref(v_value_420_);
v_valueBackDeps_438_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_398_, v_value_420_);
v_v_439_ = lean_expr_instantiate_rev(v_value_420_, v_fvars_401_);
lean_dec_ref(v_value_420_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = 0;
lean_inc(v_a_427_);
v___x_442_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v_a_427_);
lean_ctor_set(v___x_442_, 2, v_declName_418_);
lean_ctor_set(v___x_442_, 3, v_t_422_);
lean_ctor_set(v___x_442_, 4, v_v_439_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*5, v_nondep_417_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*5 + 1, v___x_441_);
lean_inc_ref(v___x_442_);
v___x_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_443_, 0, v_typeBackDeps_437_);
lean_ctor_set(v___x_443_, 1, v_valueBackDeps_438_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_ctor_set(v___x_443_, 3, v_a_425_);
v___x_444_ = lean_array_push(v_haveInfo_428_, v___x_443_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_444_);
v___x_446_ = v___x_435_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_bodyDeps_429_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_bodyTypeDeps_430_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_body_431_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_bodyType_432_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_level_433_);
v___x_446_ = v_reuseFailAlloc_453_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_447_ = l_Lean_LocalContext_addDecl(v_lctx_400_, v___x_442_);
v___x_448_ = l_Lean_mkFVar(v_a_427_);
v___x_449_ = lean_array_push(v_fvars_401_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_add(v_numHaves_398_, v___x_450_);
lean_dec(v_numHaves_398_);
v_e_397_ = v_body_421_;
v_numHaves_398_ = v___x_451_;
v_info_399_ = v___x_446_;
v_lctx_400_ = v___x_447_;
v_fvars_401_ = v___x_449_;
goto _start;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_a_425_);
lean_dec_ref(v_t_422_);
lean_dec_ref(v_body_421_);
lean_dec_ref(v_value_420_);
lean_dec_ref(v_type_419_);
lean_dec(v_declName_418_);
lean_dec_ref(v_fvars_401_);
lean_dec_ref(v_lctx_400_);
lean_dec_ref(v_info_399_);
lean_dec(v_numHaves_398_);
v_a_455_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_426_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_426_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_t_422_);
lean_dec_ref(v_body_421_);
lean_dec_ref(v_value_420_);
lean_dec_ref(v_type_419_);
lean_dec(v_declName_418_);
lean_dec_ref(v_fvars_401_);
lean_dec_ref(v_lctx_400_);
lean_dec_ref(v_info_399_);
lean_dec(v_numHaves_398_);
v_a_463_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_424_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_424_);
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
v___y_409_ = v_a_402_;
v___y_410_ = v_a_403_;
v___y_411_ = v_a_404_;
v___y_412_ = v_a_405_;
goto v___jp_408_;
}
}
else
{
v___y_409_ = v_a_402_;
v___y_410_ = v_a_403_;
v___y_411_ = v_a_404_;
v___y_412_ = v_a_405_;
goto v___jp_408_;
}
v___jp_408_:
{
lean_object* v_bodyDeps_413_; lean_object* v_body_414_; lean_object* v___f_415_; lean_object* v___x_416_; 
lean_inc_ref(v_e_397_);
v_bodyDeps_413_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_398_, v_e_397_);
lean_dec(v_numHaves_398_);
v_body_414_ = lean_expr_instantiate_rev(v_e_397_, v_fvars_401_);
lean_dec_ref(v_e_397_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_415_, 0, v_body_414_);
lean_closure_set(v___f_415_, 1, v___x_407_);
lean_closure_set(v___f_415_, 2, v_fvars_401_);
lean_closure_set(v___f_415_, 3, v_info_399_);
lean_closure_set(v___f_415_, 4, v_bodyDeps_413_);
v___x_416_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_400_, v___f_415_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_471_, lean_object* v_numHaves_472_, lean_object* v_info_473_, lean_object* v_lctx_474_, lean_object* v_fvars_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_471_, v_numHaves_472_, v_info_473_, v_lctx_474_, v_fvars_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_482_, lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_483_, v_a_484_, v_b_485_);
return v___x_486_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_487_, lean_object* v_k_488_, lean_object* v_t_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_488_, v_t_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_491_, lean_object* v_k_492_, lean_object* v_t_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_491_, v_k_492_, v_t_493_);
lean_dec(v_t_493_);
lean_dec(v_k_492_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_496_, lean_object* v___x_497_, lean_object* v_n_498_, lean_object* v_j_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_496_, v___x_497_, v_n_498_, v_j_499_, v_a_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_503_, lean_object* v___x_504_, lean_object* v_n_505_, lean_object* v_j_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_503_, v___x_504_, v_n_505_, v_j_506_, v_a_507_, v_a_508_);
lean_dec(v_n_505_);
lean_dec(v___x_504_);
lean_dec_ref(v_fvars_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_521_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_522_, lean_object* v_a_523_, lean_object* v_x_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_523_, v_x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_526_, v_a_527_, v_x_528_);
lean_dec(v_x_528_);
lean_dec(v_a_527_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_531_, lean_object* v_data_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_534_, lean_object* v_i_535_, lean_object* v_source_536_, lean_object* v_target_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_535_, v_source_536_, v_target_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_lctx_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_lctx_549_ = lean_ctor_get(v_a_544_, 2);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_552_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_549_);
v___x_553_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_543_, v___x_550_, v___x_552_, v_lctx_549_, v___x_551_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
return v_x_561_;
}
else
{
lean_object* v_key_563_; lean_object* v_tail_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_key_563_ = lean_ctor_get(v_x_562_, 0);
v_tail_564_ = lean_ctor_get(v_x_562_, 2);
v___x_565_ = 1;
v___x_566_ = lean_box(v___x_565_);
v___x_567_ = lean_array_set(v_x_561_, v_key_563_, v___x_566_);
v_x_561_ = v___x_567_;
v_x_562_ = v_tail_564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_569_, v_x_570_);
lean_dec(v_x_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_572_, size_t v_i_573_, size_t v_stop_574_, lean_object* v_b_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_eq(v_i_573_, v_stop_574_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; 
v___x_577_ = lean_array_uget_borrowed(v_as_572_, v_i_573_);
v___x_578_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_575_, v___x_577_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_573_, v___x_579_);
v_i_573_ = v___x_580_;
v_b_575_ = v___x_578_;
goto _start;
}
else
{
return v_b_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_582_, lean_object* v_i_583_, lean_object* v_stop_584_, lean_object* v_b_585_){
_start:
{
size_t v_i_boxed_586_; size_t v_stop_boxed_587_; lean_object* v_res_588_; 
v_i_boxed_586_ = lean_unbox_usize(v_i_583_);
lean_dec(v_i_583_);
v_stop_boxed_587_ = lean_unbox_usize(v_stop_584_);
lean_dec(v_stop_584_);
v_res_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_582_, v_i_boxed_586_, v_stop_boxed_587_, v_b_585_);
lean_dec_ref(v_as_582_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_589_, lean_object* v_s_590_){
_start:
{
lean_object* v_buckets_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_buckets_591_ = lean_ctor_get(v_s_590_, 1);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_array_get_size(v_buckets_591_);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
return v_arr_589_;
}
else
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_595_ = ((size_t)0ULL);
v___x_596_ = lean_usize_of_nat(v___x_593_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_591_, v___x_595_, v___x_596_, v_arr_589_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_598_, lean_object* v_s_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_598_, v_s_599_);
lean_dec_ref(v_s_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_601_, lean_object* v_numHaves_602_, lean_object* v___x_603_, lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
lean_object* v_a_608_; uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_lt(v_a_604_, v_upperBound_601_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec(v_a_604_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_b_605_);
return v___x_613_;
}
else
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_614_ = 0;
v___x_615_ = lean_nat_sub(v_numHaves_602_, v_a_604_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_sub(v___x_615_, v___x_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(v___x_614_);
v___x_619_ = lean_array_get(v___x_618_, v_b_605_, v___x_617_);
lean_dec(v___x_618_);
v___x_620_ = lean_unbox(v___x_619_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
lean_dec(v___x_617_);
v_a_608_ = v_b_605_;
goto v___jp_607_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_typeBackDeps_623_; lean_object* v_valueBackDeps_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_621_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_622_ = lean_array_get_borrowed(v___x_621_, v___x_603_, v___x_617_);
lean_dec(v___x_617_);
v_typeBackDeps_623_ = lean_ctor_get(v___x_622_, 0);
v_valueBackDeps_624_ = lean_ctor_get(v___x_622_, 1);
v___x_625_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_605_, v_typeBackDeps_623_);
v___x_626_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_625_, v_valueBackDeps_624_);
v_a_608_ = v___x_626_;
goto v___jp_607_;
}
}
v___jp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_a_604_, v___x_609_);
lean_dec(v_a_604_);
v_a_604_ = v___x_610_;
v_b_605_ = v_a_608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_627_, lean_object* v_numHaves_628_, lean_object* v___x_629_, lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_627_, v_numHaves_628_, v___x_629_, v_a_630_, v_b_631_);
lean_dec_ref(v___x_629_);
lean_dec(v_numHaves_628_);
lean_dec(v_upperBound_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_634_, lean_object* v_init_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_haveInfo_641_; lean_object* v_numHaves_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v_used_645_; lean_object* v___x_646_; lean_object* v_used_647_; lean_object* v___x_648_; 
v_haveInfo_641_ = lean_ctor_get(v_info_634_, 0);
v_numHaves_642_ = lean_array_get_size(v_haveInfo_641_);
v___x_643_ = 0;
v___x_644_ = lean_box(v___x_643_);
v_used_645_ = lean_mk_array(v_numHaves_642_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(0u);
v_used_647_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_645_, v_init_635_);
v___x_648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_642_, v_numHaves_642_, v_haveInfo_641_, v___x_646_, v_used_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_649_, lean_object* v_init_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_649_, v_init_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec_ref(v_init_650_);
lean_dec_ref(v_info_649_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_657_, lean_object* v_numHaves_658_, lean_object* v___x_659_, lean_object* v_inst_660_, lean_object* v_R_661_, lean_object* v_a_662_, lean_object* v_b_663_, lean_object* v_c_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_657_, v_numHaves_658_, v___x_659_, v_a_662_, v_b_663_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_671_, lean_object* v_numHaves_672_, lean_object* v___x_673_, lean_object* v_inst_674_, lean_object* v_R_675_, lean_object* v_a_676_, lean_object* v_b_677_, lean_object* v_c_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_671_, v_numHaves_672_, v___x_673_, v_inst_674_, v_R_675_, v_a_676_, v_b_677_, v_c_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec_ref(v___x_673_);
lean_dec(v_numHaves_672_);
lean_dec(v_upperBound_671_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_687_, uint8_t v_keepUnused_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_bodyDeps_694_; lean_object* v_bodyTypeDeps_695_; lean_object* v___x_696_; 
v_bodyDeps_694_ = lean_ctor_get(v_info_687_, 1);
v_bodyTypeDeps_695_ = lean_ctor_get(v_info_687_, 2);
v___x_696_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_687_, v_bodyTypeDeps_695_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_696_) == 0)
{
if (v_keepUnused_688_ == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_687_, v_bodyDeps_694_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_a_697_);
lean_ctor_set(v___x_703_, 1, v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_a_697_);
v_a_708_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_698_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_698_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
v_a_716_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v___x_696_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_696_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v_a_716_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_696_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_696_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_734_, lean_object* v_keepUnused_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
uint8_t v_keepUnused_boxed_741_; lean_object* v_res_742_; 
v_keepUnused_boxed_741_ = lean_unbox(v_keepUnused_735_);
v_res_742_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_734_, v_keepUnused_boxed_741_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec_ref(v_info_734_);
return v_res_742_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_box(0);
v___x_747_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_748_ = l_Lean_Expr_const___override(v___x_747_, v___x_746_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = 0;
v___x_750_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_751_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
lean_ctor_set(v___x_751_, 3, v___x_750_);
lean_ctor_set(v___x_751_, 4, v___x_750_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*5, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_752_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_level_770_, lean_object* v_exprType_771_, lean_object* v_e_772_, uint8_t v___x_773_, lean_object* v_toPure_774_, lean_object* v_xs_775_, lean_object* v_____do__lift_776_){
_start:
{
if (lean_obj_tag(v_____do__lift_776_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_proof_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_779_, 0, v_level_770_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_mkConst(v___x_777_, v___x_779_);
lean_inc_ref_n(v_e_772_, 3);
lean_inc_ref(v_exprType_771_);
v_proof_781_ = l_Lean_mkAppB(v___x_780_, v_exprType_771_, v_e_772_);
v___x_782_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_782_, 0, v_e_772_);
lean_ctor_set(v___x_782_, 1, v_exprType_771_);
lean_ctor_set(v___x_782_, 2, v_e_772_);
lean_ctor_set(v___x_782_, 3, v_e_772_);
lean_ctor_set(v___x_782_, 4, v_proof_781_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*5, v___x_773_);
v___x_783_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_e_784_; lean_object* v_h_785_; lean_object* v_expr_786_; lean_object* v_proof_787_; lean_object* v___x_792_; uint8_t v___x_793_; 
lean_dec(v_level_770_);
v_e_784_ = lean_ctor_get(v_____do__lift_776_, 0);
v_h_785_ = lean_ctor_get(v_____do__lift_776_, 1);
v_expr_786_ = lean_expr_abstract(v_e_784_, v_xs_775_);
v_proof_787_ = lean_expr_abstract(v_h_785_, v_xs_775_);
lean_inc_ref(v_proof_787_);
v___x_792_ = l_Lean_Expr_cleanupAnnotations(v_proof_787_);
v___x_793_ = l_Lean_Expr_isApp(v___x_792_);
if (v___x_793_ == 0)
{
lean_dec_ref(v___x_792_);
goto v___jp_788_;
}
else
{
lean_object* v_arg_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_arg_794_ = lean_ctor_get(v___x_792_, 1);
lean_inc_ref(v_arg_794_);
v___x_795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_792_);
v___x_796_ = l_Lean_Expr_isApp(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v___x_795_);
lean_dec_ref(v_arg_794_);
goto v___jp_788_;
}
else
{
lean_object* v_arg_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_arg_797_ = lean_ctor_get(v___x_795_, 1);
lean_inc_ref(v_arg_797_);
v___x_798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_795_);
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_800_ = l_Lean_Expr_isConstOf(v___x_798_, v___x_799_);
lean_dec_ref(v___x_798_);
if (v___x_800_ == 0)
{
lean_dec_ref(v_arg_797_);
lean_dec_ref(v_arg_794_);
goto v___jp_788_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_802_ = lean_unsigned_to_nat(3u);
v___x_803_ = l_Lean_Expr_isAppOfArity(v_arg_797_, v___x_801_, v___x_802_);
lean_dec_ref(v_arg_797_);
if (v___x_803_ == 0)
{
lean_dec_ref(v_arg_794_);
goto v___jp_788_;
}
else
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = l_Lean_Expr_cleanupAnnotations(v_arg_794_);
v___x_805_ = l_Lean_Expr_isApp(v___x_804_);
if (v___x_805_ == 0)
{
lean_dec_ref(v___x_804_);
goto v___jp_788_;
}
else
{
lean_object* v_arg_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_arg_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc_ref(v_arg_806_);
v___x_807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_804_);
v___x_808_ = l_Lean_Expr_isApp(v___x_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v_arg_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_arg_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc_ref(v_arg_809_);
v___x_810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_807_);
v___x_811_ = l_Lean_Expr_isConstOf(v___x_810_, v___x_799_);
lean_dec_ref(v___x_810_);
if (v___x_811_ == 0)
{
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = l_Lean_Expr_cleanupAnnotations(v_arg_809_);
v___x_813_ = l_Lean_Expr_isApp(v___x_812_);
if (v___x_813_ == 0)
{
lean_dec_ref(v___x_812_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v_arg_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_arg_814_ = lean_ctor_get(v___x_812_, 1);
lean_inc_ref(v_arg_814_);
v___x_815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_812_);
v___x_816_ = l_Lean_Expr_isApp(v___x_815_);
if (v___x_816_ == 0)
{
lean_dec_ref(v___x_815_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v_arg_817_; uint8_t v___y_819_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_arg_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc_ref(v_arg_817_);
v___x_822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_815_);
v___x_823_ = l_Lean_Expr_isApp(v___x_822_);
if (v___x_823_ == 0)
{
lean_dec_ref(v___x_822_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_822_);
v___x_825_ = l_Lean_Expr_isConstOf(v___x_824_, v___x_801_);
lean_dec_ref(v___x_824_);
if (v___x_825_ == 0)
{
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Expr_getAppFn(v_arg_806_);
if (lean_obj_tag(v___x_826_) == 4)
{
lean_object* v_declName_827_; 
v_declName_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_declName_827_);
lean_dec_ref_known(v___x_826_, 2);
if (lean_obj_tag(v_declName_827_) == 1)
{
lean_object* v_pre_828_; 
v_pre_828_ = lean_ctor_get(v_declName_827_, 0);
if (lean_obj_tag(v_pre_828_) == 0)
{
lean_object* v_str_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_str_829_ = lean_ctor_get(v_declName_827_, 1);
lean_inc_ref(v_str_829_);
lean_dec_ref_known(v_declName_827_, 2);
v___x_830_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_831_ = lean_string_dec_eq(v_str_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_833_ = lean_string_dec_eq(v_str_829_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_835_ = lean_string_dec_eq(v_str_829_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_837_ = lean_string_dec_eq(v_str_829_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_839_ = lean_string_dec_eq(v_str_829_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_841_ = lean_string_dec_eq(v_str_829_, v___x_840_);
lean_dec_ref(v_str_829_);
if (v___x_841_ == 0)
{
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
v___y_819_ = v___x_800_;
goto v___jp_818_;
}
}
else
{
lean_dec_ref(v_str_829_);
v___y_819_ = v___x_800_;
goto v___jp_818_;
}
}
else
{
lean_dec_ref(v_str_829_);
v___y_819_ = v___x_800_;
goto v___jp_818_;
}
}
else
{
lean_dec_ref(v_str_829_);
v___y_819_ = v___x_800_;
goto v___jp_818_;
}
}
else
{
lean_dec_ref(v_str_829_);
v___y_819_ = v___x_800_;
goto v___jp_818_;
}
}
else
{
lean_dec_ref(v_str_829_);
v___y_819_ = v___x_800_;
goto v___jp_818_;
}
}
else
{
lean_dec_ref_known(v_declName_827_, 2);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
}
else
{
lean_dec(v_declName_827_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
}
else
{
lean_dec_ref(v___x_826_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
}
}
v___jp_818_:
{
if (v___y_819_ == 0)
{
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_806_);
goto v___jp_788_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref(v_proof_787_);
lean_dec_ref(v_e_772_);
v___x_820_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_820_, 0, v_arg_814_);
lean_ctor_set(v___x_820_, 1, v_exprType_771_);
lean_ctor_set(v___x_820_, 2, v_arg_817_);
lean_ctor_set(v___x_820_, 3, v_expr_786_);
lean_ctor_set(v___x_820_, 4, v_arg_806_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*5, v___x_800_);
v___x_821_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_820_);
return v___x_821_;
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
v___jp_788_:
{
uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = 1;
lean_inc_ref(v_expr_786_);
v___x_790_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_790_, 0, v_expr_786_);
lean_ctor_set(v___x_790_, 1, v_exprType_771_);
lean_ctor_set(v___x_790_, 2, v_e_772_);
lean_ctor_set(v___x_790_, 3, v_expr_786_);
lean_ctor_set(v___x_790_, 4, v_proof_787_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*5, v___x_789_);
v___x_791_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_790_);
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_level_842_, lean_object* v_exprType_843_, lean_object* v_e_844_, lean_object* v___x_845_, lean_object* v_toPure_846_, lean_object* v_xs_847_, lean_object* v_____do__lift_848_){
_start:
{
uint8_t v___x_7825__boxed_849_; lean_object* v_res_850_; 
v___x_7825__boxed_849_ = lean_unbox(v___x_845_);
v_res_850_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_level_842_, v_exprType_843_, v_e_844_, v___x_7825__boxed_849_, v_toPure_846_, v_xs_847_, v_____do__lift_848_);
lean_dec(v_____do__lift_848_);
lean_dec_ref(v_xs_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_851_, lean_object* v_bodyType_852_, lean_object* v_xs_853_, lean_object* v_level_854_, lean_object* v_e_855_, uint8_t v___x_856_, lean_object* v_toPure_857_, lean_object* v_body_858_, lean_object* v_toBind_859_, lean_object* v_____r_860_){
_start:
{
lean_object* v_simp_861_; lean_object* v_exprType_862_; lean_object* v___x_863_; lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_simp_861_ = lean_ctor_get(v_inst_851_, 2);
lean_inc(v_simp_861_);
lean_dec_ref(v_inst_851_);
v_exprType_862_ = lean_expr_abstract(v_bodyType_852_, v_xs_853_);
v___x_863_ = lean_box(v___x_856_);
v___f_864_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_864_, 0, v_level_854_);
lean_closure_set(v___f_864_, 1, v_exprType_862_);
lean_closure_set(v___f_864_, 2, v_e_855_);
lean_closure_set(v___f_864_, 3, v___x_863_);
lean_closure_set(v___f_864_, 4, v_toPure_857_);
lean_closure_set(v___f_864_, 5, v_xs_853_);
v___x_865_ = lean_apply_1(v_simp_861_, v_body_858_);
v___x_866_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v___x_865_, v___f_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_867_, lean_object* v_bodyType_868_, lean_object* v_xs_869_, lean_object* v_level_870_, lean_object* v_e_871_, lean_object* v___x_872_, lean_object* v_toPure_873_, lean_object* v_body_874_, lean_object* v_toBind_875_, lean_object* v_____r_876_){
_start:
{
uint8_t v___x_7978__boxed_877_; lean_object* v_res_878_; 
v___x_7978__boxed_877_ = lean_unbox(v___x_872_);
v_res_878_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_867_, v_bodyType_868_, v_xs_869_, v_level_870_, v_e_871_, v___x_7978__boxed_877_, v_toPure_873_, v_body_874_, v_toBind_875_, v_____r_876_);
lean_dec_ref(v_bodyType_868_);
return v_res_878_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_885_, lean_object* v_body_886_, lean_object* v___x_887_, lean_object* v___x_888_, lean_object* v_toMonadRef_889_, lean_object* v___x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_toCold_899_; lean_object* v_options_900_; uint8_t v_hasTrace_901_; 
v_toCold_899_ = lean_ctor_get(v___y_893_, 0);
v_options_900_ = lean_ctor_get(v_toCold_899_, 2);
v_hasTrace_901_ = lean_ctor_get_uint8(v_options_900_, sizeof(void*)*1);
if (v_hasTrace_901_ == 0)
{
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_toMonadRef_889_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v_body_886_);
lean_dec(v_cls_885_);
goto v___jp_896_;
}
else
{
lean_object* v_inheritedTraceOptions_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_inheritedTraceOptions_902_ = lean_ctor_get(v_toCold_899_, 11);
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_885_);
v___x_904_ = l_Lean_Name_append(v___x_903_, v_cls_885_);
v___x_905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_902_, v_options_900_, v___x_904_);
lean_dec(v___x_904_);
if (v___x_905_ == 0)
{
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_toMonadRef_889_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v_body_886_);
lean_dec(v_cls_885_);
goto v___jp_896_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_7447__overap_909_; lean_object* v___x_910_; 
v___x_906_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3);
v___x_907_ = l_Lean_MessageData_ofExpr(v_body_886_);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_7447__overap_909_ = l_Lean_addTrace___redArg(v___x_887_, v___x_888_, v_toMonadRef_889_, v___x_890_, v_cls_885_, v___x_908_);
v___x_910_ = lean_apply_5(v___x_7447__overap_909_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, lean_box(0));
return v___x_910_;
}
}
v___jp_896_:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_box(0);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_911_, lean_object* v_body_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_toMonadRef_915_, lean_object* v___x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_911_, v_body_912_, v___x_913_, v___x_914_, v_toMonadRef_915_, v___x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_925_, lean_object* v_type_926_, lean_object* v___y_927_, lean_object* v_value_928_, uint8_t v___y_929_, lean_object* v___x_930_, uint8_t v___y_931_, lean_object* v_toPure_932_, lean_object* v_us_933_, uint8_t v___x_934_, lean_object* v_rb_935_){
_start:
{
lean_object* v_expr_936_; lean_object* v_exprType_937_; lean_object* v_exprInit_938_; lean_object* v_exprResult_939_; lean_object* v_proof_940_; uint8_t v_modified_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_968_; 
v_expr_936_ = lean_ctor_get(v_rb_935_, 0);
v_exprType_937_ = lean_ctor_get(v_rb_935_, 1);
v_exprInit_938_ = lean_ctor_get(v_rb_935_, 2);
v_exprResult_939_ = lean_ctor_get(v_rb_935_, 3);
v_proof_940_ = lean_ctor_get(v_rb_935_, 4);
v_modified_941_ = lean_ctor_get_uint8(v_rb_935_, sizeof(void*)*5);
v_isSharedCheck_968_ = !lean_is_exclusive(v_rb_935_);
if (v_isSharedCheck_968_ == 0)
{
v___x_943_ = v_rb_935_;
v_isShared_944_ = v_isSharedCheck_968_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_proof_940_);
lean_inc(v_exprResult_939_);
lean_inc(v_exprInit_938_);
lean_inc(v_exprType_937_);
lean_inc(v_expr_936_);
lean_dec(v_rb_935_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_968_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v_expr_947_; lean_object* v___x_948_; lean_object* v_exprType_949_; lean_object* v___x_950_; lean_object* v_exprInit_951_; lean_object* v_exprResult_952_; 
v___x_945_ = 0;
lean_inc_ref_n(v_type_926_, 4);
lean_inc_n(v_declName_925_, 4);
v___x_946_ = l_Lean_mkLambda(v_declName_925_, v___x_945_, v_type_926_, v_expr_936_);
lean_inc_ref_n(v___y_927_, 3);
lean_inc_ref(v___x_946_);
v_expr_947_ = l_Lean_Expr_app___override(v___x_946_, v___y_927_);
v___x_948_ = l_Lean_mkLambda(v_declName_925_, v___x_945_, v_type_926_, v_exprType_937_);
lean_inc_ref(v___x_948_);
v_exprType_949_ = l_Lean_Expr_app___override(v___x_948_, v___y_927_);
v___x_950_ = l_Lean_mkLambda(v_declName_925_, v___x_945_, v_type_926_, v_exprInit_938_);
lean_inc_ref(v___x_950_);
v_exprInit_951_ = l_Lean_Expr_app___override(v___x_950_, v_value_928_);
v_exprResult_952_ = l_Lean_Expr_letE___override(v_declName_925_, v_type_926_, v___y_927_, v_exprResult_939_, v___y_929_);
if (v_modified_941_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_proof_955_; lean_object* v___x_957_; 
lean_dec_ref(v___x_950_);
lean_dec_ref(v___x_948_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v_proof_940_);
lean_dec(v_us_933_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_type_926_);
lean_dec(v_declName_925_);
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_954_ = l_Lean_mkConst(v___x_953_, v___x_930_);
lean_inc_ref(v_expr_947_);
lean_inc_ref(v_exprType_949_);
v_proof_955_ = l_Lean_mkAppB(v___x_954_, v_exprType_949_, v_expr_947_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 4, v_proof_955_);
lean_ctor_set(v___x_943_, 3, v_exprResult_952_);
lean_ctor_set(v___x_943_, 2, v_exprInit_951_);
lean_ctor_set(v___x_943_, 1, v_exprType_949_);
lean_ctor_set(v___x_943_, 0, v_expr_947_);
v___x_957_ = v___x_943_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_expr_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_exprType_949_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_exprInit_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_exprResult_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_proof_955_);
v___x_957_ = v_reuseFailAlloc_959_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; 
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*5, v___y_931_);
v___x_958_ = lean_apply_2(v_toPure_932_, lean_box(0), v___x_957_);
return v___x_958_;
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_proof_963_; lean_object* v___x_965_; 
lean_dec(v___x_930_);
v___x_960_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_961_ = l_Lean_mkConst(v___x_960_, v_us_933_);
lean_inc_ref(v_type_926_);
v___x_962_ = l_Lean_mkLambda(v_declName_925_, v___x_945_, v_type_926_, v_proof_940_);
v_proof_963_ = l_Lean_mkApp6(v___x_961_, v_type_926_, v___x_948_, v___y_927_, v___x_950_, v___x_946_, v___x_962_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 4, v_proof_963_);
lean_ctor_set(v___x_943_, 3, v_exprResult_952_);
lean_ctor_set(v___x_943_, 2, v_exprInit_951_);
lean_ctor_set(v___x_943_, 1, v_exprType_949_);
lean_ctor_set(v___x_943_, 0, v_expr_947_);
v___x_965_ = v___x_943_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_expr_947_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_exprType_949_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_exprInit_951_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_exprResult_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_proof_963_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; 
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*5, v___x_934_);
v___x_966_ = lean_apply_2(v_toPure_932_, lean_box(0), v___x_965_);
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_969_, lean_object* v_type_970_, lean_object* v___y_971_, lean_object* v_value_972_, lean_object* v___y_973_, lean_object* v___x_974_, lean_object* v___y_975_, lean_object* v_toPure_976_, lean_object* v_us_977_, lean_object* v___x_978_, lean_object* v_rb_979_){
_start:
{
uint8_t v___y_8073__boxed_980_; uint8_t v___y_8075__boxed_981_; uint8_t v___x_8076__boxed_982_; lean_object* v_res_983_; 
v___y_8073__boxed_980_ = lean_unbox(v___y_973_);
v___y_8075__boxed_981_ = lean_unbox(v___y_975_);
v___x_8076__boxed_982_ = lean_unbox(v___x_978_);
v_res_983_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_969_, v_type_970_, v___y_971_, v_value_972_, v___y_8073__boxed_980_, v___x_974_, v___y_8075__boxed_981_, v_toPure_976_, v_us_977_, v___x_8076__boxed_982_, v_rb_979_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_984_, lean_object* v_____x_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_apply_1(v___f_984_, v_____x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_991_, lean_object* v_declName_992_, lean_object* v_type_993_, lean_object* v_value_994_, lean_object* v_us_995_, lean_object* v___x_996_, uint8_t v___x_997_, lean_object* v_toPure_998_, lean_object* v_rb_999_){
_start:
{
lean_object* v_expr_1000_; lean_object* v_exprType_1001_; lean_object* v_exprInit_1002_; lean_object* v_exprResult_1003_; lean_object* v_proof_1004_; uint8_t v_modified_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1033_; 
v_expr_1000_ = lean_ctor_get(v_rb_999_, 0);
v_exprType_1001_ = lean_ctor_get(v_rb_999_, 1);
v_exprInit_1002_ = lean_ctor_get(v_rb_999_, 2);
v_exprResult_1003_ = lean_ctor_get(v_rb_999_, 3);
v_proof_1004_ = lean_ctor_get(v_rb_999_, 4);
v_modified_1005_ = lean_ctor_get_uint8(v_rb_999_, sizeof(void*)*5);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_rb_999_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1007_ = v_rb_999_;
v_isShared_1008_ = v_isSharedCheck_1033_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_proof_1004_);
lean_inc(v_exprResult_1003_);
lean_inc(v_exprInit_1002_);
lean_inc(v_exprType_1001_);
lean_inc(v_expr_1000_);
lean_dec(v_rb_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1033_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_expr_1009_; lean_object* v_exprType_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v_exprInit_1013_; lean_object* v_exprResult_1014_; 
v_expr_1009_ = lean_expr_lower_loose_bvars(v_expr_1000_, v___x_991_, v___x_991_);
lean_dec_ref(v_expr_1000_);
v_exprType_1010_ = lean_expr_lower_loose_bvars(v_exprType_1001_, v___x_991_, v___x_991_);
lean_dec_ref(v_exprType_1001_);
v___x_1011_ = 0;
lean_inc_ref(v_type_993_);
lean_inc(v_declName_992_);
v___x_1012_ = l_Lean_mkLambda(v_declName_992_, v___x_1011_, v_type_993_, v_exprInit_1002_);
lean_inc_ref(v_value_994_);
lean_inc_ref(v___x_1012_);
v_exprInit_1013_ = l_Lean_Expr_app___override(v___x_1012_, v_value_994_);
v_exprResult_1014_ = lean_expr_lower_loose_bvars(v_exprResult_1003_, v___x_991_, v___x_991_);
lean_dec_ref(v_exprResult_1003_);
if (v_modified_1005_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_proof_1020_; lean_object* v___x_1022_; 
lean_dec_ref(v___x_1012_);
lean_dec_ref(v_proof_1004_);
lean_dec(v_declName_992_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1016_ = l_Lean_mkConst(v___x_1015_, v_us_995_);
v___x_1017_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1018_ = l_Lean_mkConst(v___x_1017_, v___x_996_);
lean_inc_ref_n(v_expr_1009_, 3);
lean_inc_ref_n(v_exprType_1010_, 2);
v___x_1019_ = l_Lean_mkAppB(v___x_1018_, v_exprType_1010_, v_expr_1009_);
v_proof_1020_ = l_Lean_mkApp6(v___x_1016_, v_type_993_, v_exprType_1010_, v_value_994_, v_expr_1009_, v_expr_1009_, v___x_1019_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 4, v_proof_1020_);
lean_ctor_set(v___x_1007_, 3, v_exprResult_1014_);
lean_ctor_set(v___x_1007_, 2, v_exprInit_1013_);
lean_ctor_set(v___x_1007_, 1, v_exprType_1010_);
lean_ctor_set(v___x_1007_, 0, v_expr_1009_);
v___x_1022_ = v___x_1007_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_expr_1009_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_exprType_1010_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_exprInit_1013_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_exprResult_1014_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_proof_1020_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*5, v___x_997_);
v___x_1023_ = lean_apply_2(v_toPure_998_, lean_box(0), v___x_1022_);
return v___x_1023_;
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_proof_1028_; lean_object* v___x_1030_; 
lean_dec(v___x_996_);
v___x_1025_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1026_ = l_Lean_mkConst(v___x_1025_, v_us_995_);
lean_inc_ref(v_type_993_);
v___x_1027_ = l_Lean_mkLambda(v_declName_992_, v___x_1011_, v_type_993_, v_proof_1004_);
lean_inc_ref(v_expr_1009_);
lean_inc_ref(v_exprType_1010_);
v_proof_1028_ = l_Lean_mkApp6(v___x_1026_, v_type_993_, v_exprType_1010_, v_value_994_, v___x_1012_, v_expr_1009_, v___x_1027_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 4, v_proof_1028_);
lean_ctor_set(v___x_1007_, 3, v_exprResult_1014_);
lean_ctor_set(v___x_1007_, 2, v_exprInit_1013_);
lean_ctor_set(v___x_1007_, 1, v_exprType_1010_);
lean_ctor_set(v___x_1007_, 0, v_expr_1009_);
v___x_1030_ = v___x_1007_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_expr_1009_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_exprType_1010_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_exprInit_1013_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_exprResult_1014_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_proof_1028_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*5, v___x_997_);
v___x_1031_ = lean_apply_2(v_toPure_998_, lean_box(0), v___x_1030_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1034_, lean_object* v_declName_1035_, lean_object* v_type_1036_, lean_object* v_value_1037_, lean_object* v_us_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_toPure_1041_, lean_object* v_rb_1042_){
_start:
{
uint8_t v___x_8163__boxed_1043_; lean_object* v_res_1044_; 
v___x_8163__boxed_1043_ = lean_unbox(v___x_1040_);
v_res_1044_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1034_, v_declName_1035_, v_type_1036_, v_value_1037_, v_us_1038_, v___x_1039_, v___x_8163__boxed_1043_, v_toPure_1041_, v_rb_1042_);
lean_dec(v___x_1034_);
return v_res_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1051_, lean_object* v_declName_1052_, lean_object* v_val_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_toMonadRef_1056_, lean_object* v___x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_toCold_1066_; lean_object* v_options_1067_; uint8_t v_hasTrace_1068_; 
v_toCold_1066_ = lean_ctor_get(v___y_1060_, 0);
v_options_1067_ = lean_ctor_get(v_toCold_1066_, 2);
v_hasTrace_1068_ = lean_ctor_get_uint8(v_options_1067_, sizeof(void*)*1);
if (v_hasTrace_1068_ == 0)
{
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v___x_1057_);
lean_dec_ref(v_toMonadRef_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_val_1053_);
lean_dec(v_declName_1052_);
lean_dec(v_cls_1051_);
goto v___jp_1063_;
}
else
{
lean_object* v_inheritedTraceOptions_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_inheritedTraceOptions_1069_ = lean_ctor_get(v_toCold_1066_, 11);
v___x_1070_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1051_);
v___x_1071_ = l_Lean_Name_append(v___x_1070_, v_cls_1051_);
v___x_1072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1069_, v_options_1067_, v___x_1071_);
lean_dec(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v___x_1057_);
lean_dec_ref(v_toMonadRef_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_val_1053_);
lean_dec(v_declName_1052_);
lean_dec(v_cls_1051_);
goto v___jp_1063_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_7791__overap_1080_; lean_object* v___x_1081_; 
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1074_ = l_Lean_MessageData_ofName(v_declName_1052_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_MessageData_ofExpr(v_val_1053_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_7791__overap_1080_ = l_Lean_addTrace___redArg(v___x_1054_, v___x_1055_, v_toMonadRef_1056_, v___x_1057_, v_cls_1051_, v___x_1079_);
v___x_1081_ = lean_apply_5(v___x_7791__overap_1080_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, lean_box(0));
return v___x_1081_;
}
}
v___jp_1063_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1082_, lean_object* v_declName_1083_, lean_object* v_val_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_toMonadRef_1087_, lean_object* v___x_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1082_, v_declName_1083_, v_val_1084_, v___x_1085_, v___x_1086_, v_toMonadRef_1087_, v___x_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v_res_1094_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1101_, lean_object* v_declName_1102_, lean_object* v_val_1103_, lean_object* v_val_x27_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v_toMonadRef_1107_, lean_object* v___x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_toCold_1117_; lean_object* v_options_1118_; uint8_t v_hasTrace_1119_; 
v_toCold_1117_ = lean_ctor_get(v___y_1111_, 0);
v_options_1118_ = lean_ctor_get(v_toCold_1117_, 2);
v_hasTrace_1119_ = lean_ctor_get_uint8(v_options_1118_, sizeof(void*)*1);
if (v_hasTrace_1119_ == 0)
{
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_toMonadRef_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_val_x27_1104_);
lean_dec_ref(v_val_1103_);
lean_dec(v_declName_1102_);
lean_dec(v_cls_1101_);
goto v___jp_1114_;
}
else
{
lean_object* v_inheritedTraceOptions_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_inheritedTraceOptions_1120_ = lean_ctor_get(v_toCold_1117_, 11);
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1101_);
v___x_1122_ = l_Lean_Name_append(v___x_1121_, v_cls_1101_);
v___x_1123_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1120_, v_options_1118_, v___x_1122_);
lean_dec(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_toMonadRef_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_val_x27_1104_);
lean_dec_ref(v_val_1103_);
lean_dec(v_declName_1102_);
lean_dec(v_cls_1101_);
goto v___jp_1114_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_7535__overap_1135_; lean_object* v___x_1136_; 
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1125_ = l_Lean_MessageData_ofName(v_declName_1102_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_ofExpr(v_val_1103_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_MessageData_ofExpr(v_val_x27_1104_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_7535__overap_1135_ = l_Lean_addTrace___redArg(v___x_1105_, v___x_1106_, v_toMonadRef_1107_, v___x_1108_, v_cls_1101_, v___x_1134_);
v___x_1136_ = lean_apply_5(v___x_7535__overap_1135_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, lean_box(0));
return v___x_1136_;
}
}
v___jp_1114_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1137_, lean_object* v_declName_1138_, lean_object* v_val_1139_, lean_object* v_val_x27_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v_toMonadRef_1143_, lean_object* v___x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1137_, v_declName_1138_, v_val_1139_, v_val_x27_1140_, v___x_1141_, v___x_1142_, v_toMonadRef_1143_, v___x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_e_1151_, lean_object* v_xs_1152_, lean_object* v_h_1153_, uint8_t v___x_1154_, lean_object* v_toPure_1155_, lean_object* v_toBind_1156_, lean_object* v___f_1157_, lean_object* v_____r_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1159_ = lean_expr_abstract(v_e_1151_, v_xs_1152_);
v___x_1160_ = lean_expr_abstract(v_h_1153_, v_xs_1152_);
v___x_1161_ = lean_box(v___x_1154_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1159_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_apply_2(v_toPure_1155_, lean_box(0), v___x_1163_);
v___x_1165_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v___x_1164_, v___f_1157_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_e_1166_, lean_object* v_xs_1167_, lean_object* v_h_1168_, lean_object* v___x_1169_, lean_object* v_toPure_1170_, lean_object* v_toBind_1171_, lean_object* v___f_1172_, lean_object* v_____r_1173_){
_start:
{
uint8_t v___x_8395__boxed_1174_; lean_object* v_res_1175_; 
v___x_8395__boxed_1174_ = lean_unbox(v___x_1169_);
v_res_1175_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_e_1166_, v_xs_1167_, v_h_1168_, v___x_8395__boxed_1174_, v_toPure_1170_, v_toBind_1171_, v___f_1172_, v_____r_1173_);
lean_dec_ref(v_h_1168_);
lean_dec_ref(v_xs_1167_);
lean_dec_ref(v_e_1166_);
return v_res_1175_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1179_, lean_object* v_declName_1180_, lean_object* v_val_1181_, lean_object* v_e_1182_, lean_object* v___x_1183_, lean_object* v___x_1184_, lean_object* v_toMonadRef_1185_, lean_object* v___x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_toCold_1195_; lean_object* v_options_1196_; uint8_t v_hasTrace_1197_; 
v_toCold_1195_ = lean_ctor_get(v___y_1189_, 0);
v_options_1196_ = lean_ctor_get(v_toCold_1195_, 2);
v_hasTrace_1197_ = lean_ctor_get_uint8(v_options_1196_, sizeof(void*)*1);
if (v_hasTrace_1197_ == 0)
{
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_toMonadRef_1185_);
lean_dec_ref(v___x_1184_);
lean_dec_ref(v___x_1183_);
lean_dec_ref(v_e_1182_);
lean_dec_ref(v_val_1181_);
lean_dec(v_declName_1180_);
lean_dec(v_cls_1179_);
goto v___jp_1192_;
}
else
{
lean_object* v_inheritedTraceOptions_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_inheritedTraceOptions_1198_ = lean_ctor_get(v_toCold_1195_, 11);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1179_);
v___x_1200_ = l_Lean_Name_append(v___x_1199_, v_cls_1179_);
v___x_1201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1198_, v_options_1196_, v___x_1200_);
lean_dec(v___x_1200_);
if (v___x_1201_ == 0)
{
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_toMonadRef_1185_);
lean_dec_ref(v___x_1184_);
lean_dec_ref(v___x_1183_);
lean_dec_ref(v_e_1182_);
lean_dec_ref(v_val_1181_);
lean_dec(v_declName_1180_);
lean_dec(v_cls_1179_);
goto v___jp_1192_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_7685__overap_1213_; lean_object* v___x_1214_; 
v___x_1202_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1203_ = l_Lean_MessageData_ofName(v_declName_1180_);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_MessageData_ofExpr(v_val_1181_);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = l_Lean_MessageData_ofExpr(v_e_1182_);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_7685__overap_1213_ = l_Lean_addTrace___redArg(v___x_1183_, v___x_1184_, v_toMonadRef_1185_, v___x_1186_, v_cls_1179_, v___x_1212_);
v___x_1214_ = lean_apply_5(v___x_7685__overap_1213_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1214_;
}
}
v___jp_1192_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1215_, lean_object* v_declName_1216_, lean_object* v_val_1217_, lean_object* v_e_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v_toMonadRef_1221_, lean_object* v___x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1215_, v_declName_1216_, v_val_1217_, v_e_1218_, v___x_1219_, v___x_1220_, v_toMonadRef_1221_, v___x_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_level_1238_, lean_object* v___x_1239_, lean_object* v_type_1240_, lean_object* v_value_1241_, uint8_t v___x_1242_, lean_object* v_toPure_1243_, lean_object* v_toBind_1244_, lean_object* v___f_1245_, lean_object* v_xs_1246_, uint8_t v___x_1247_, lean_object* v___f_1248_, lean_object* v_declName_1249_, lean_object* v_val_1250_, lean_object* v___x_1251_, lean_object* v___x_1252_, lean_object* v_toMonadRef_1253_, lean_object* v___x_1254_, lean_object* v_inst_1255_, lean_object* v_____do__lift_1256_){
_start:
{
if (lean_obj_tag(v_____do__lift_1256_) == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_inst_1255_);
lean_dec_ref(v___x_1254_);
lean_dec_ref(v_toMonadRef_1253_);
lean_dec_ref(v___x_1252_);
lean_dec_ref(v___x_1251_);
lean_dec_ref(v_val_1250_);
lean_dec(v_declName_1249_);
lean_dec(v___f_1248_);
lean_dec_ref(v_xs_1246_);
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_level_1238_);
lean_ctor_set(v___x_1258_, 1, v___x_1239_);
v___x_1259_ = l_Lean_mkConst(v___x_1257_, v___x_1258_);
lean_inc_ref(v_value_1241_);
v___x_1260_ = l_Lean_mkAppB(v___x_1259_, v_type_1240_, v_value_1241_);
v___x_1261_ = lean_box(v___x_1242_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_value_1241_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_apply_2(v_toPure_1243_, lean_box(0), v___x_1263_);
v___x_1265_ = lean_apply_4(v_toBind_1244_, lean_box(0), lean_box(0), v___x_1264_, v___f_1245_);
return v___x_1265_;
}
else
{
lean_object* v_e_1266_; lean_object* v_h_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; lean_object* v_cls_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec(v___f_1245_);
lean_dec_ref(v_value_1241_);
lean_dec_ref(v_type_1240_);
lean_dec(v___x_1239_);
lean_dec(v_level_1238_);
v_e_1266_ = lean_ctor_get(v_____do__lift_1256_, 0);
lean_inc_ref_n(v_e_1266_, 2);
v_h_1267_ = lean_ctor_get(v_____do__lift_1256_, 1);
lean_inc_ref(v_h_1267_);
lean_dec_ref_known(v_____do__lift_1256_, 2);
v___x_1268_ = lean_box(v___x_1247_);
lean_inc(v_toBind_1244_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1269_, 0, v_e_1266_);
lean_closure_set(v___f_1269_, 1, v_xs_1246_);
lean_closure_set(v___f_1269_, 2, v_h_1267_);
lean_closure_set(v___f_1269_, 3, v___x_1268_);
lean_closure_set(v___f_1269_, 4, v_toPure_1243_);
lean_closure_set(v___f_1269_, 5, v_toBind_1244_);
lean_closure_set(v___f_1269_, 6, v___f_1248_);
v_cls_1270_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1271_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1271_, 0, v_cls_1270_);
lean_closure_set(v___f_1271_, 1, v_declName_1249_);
lean_closure_set(v___f_1271_, 2, v_val_1250_);
lean_closure_set(v___f_1271_, 3, v_e_1266_);
lean_closure_set(v___f_1271_, 4, v___x_1251_);
lean_closure_set(v___f_1271_, 5, v___x_1252_);
lean_closure_set(v___f_1271_, 6, v_toMonadRef_1253_);
lean_closure_set(v___f_1271_, 7, v___x_1254_);
v___x_1272_ = lean_apply_2(v_inst_1255_, lean_box(0), v___f_1271_);
v___x_1273_ = lean_apply_4(v_toBind_1244_, lean_box(0), lean_box(0), v___x_1272_, v___f_1269_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_level_1274_ = _args[0];
lean_object* v___x_1275_ = _args[1];
lean_object* v_type_1276_ = _args[2];
lean_object* v_value_1277_ = _args[3];
lean_object* v___x_1278_ = _args[4];
lean_object* v_toPure_1279_ = _args[5];
lean_object* v_toBind_1280_ = _args[6];
lean_object* v___f_1281_ = _args[7];
lean_object* v_xs_1282_ = _args[8];
lean_object* v___x_1283_ = _args[9];
lean_object* v___f_1284_ = _args[10];
lean_object* v_declName_1285_ = _args[11];
lean_object* v_val_1286_ = _args[12];
lean_object* v___x_1287_ = _args[13];
lean_object* v___x_1288_ = _args[14];
lean_object* v_toMonadRef_1289_ = _args[15];
lean_object* v___x_1290_ = _args[16];
lean_object* v_inst_1291_ = _args[17];
lean_object* v_____do__lift_1292_ = _args[18];
_start:
{
uint8_t v___x_8535__boxed_1293_; uint8_t v___x_8537__boxed_1294_; lean_object* v_res_1295_; 
v___x_8535__boxed_1293_ = lean_unbox(v___x_1278_);
v___x_8537__boxed_1294_ = lean_unbox(v___x_1283_);
v_res_1295_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_level_1274_, v___x_1275_, v_type_1276_, v_value_1277_, v___x_8535__boxed_1293_, v_toPure_1279_, v_toBind_1280_, v___f_1281_, v_xs_1282_, v___x_8537__boxed_1294_, v___f_1284_, v_declName_1285_, v_val_1286_, v___x_1287_, v___x_1288_, v_toMonadRef_1289_, v___x_1290_, v_inst_1291_, v_____do__lift_1292_);
return v_res_1295_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1306_ = lean_unsigned_to_nat(8u);
v___x_1307_ = lean_unsigned_to_nat(287u);
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1309_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1310_ = l_mkPanicMessageWithDecl(v___x_1309_, v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1311_, lean_object* v_type_1312_, lean_object* v_fst_1313_, lean_object* v___x_1314_, lean_object* v_value_1315_, uint8_t v___x_1316_, uint8_t v_fst_1317_, lean_object* v___x_1318_, uint8_t v___x_1319_, lean_object* v_toPure_1320_, lean_object* v_us_1321_, lean_object* v_snd_1322_, lean_object* v___x_1323_, lean_object* v_rb_1324_){
_start:
{
lean_object* v_expr_1325_; lean_object* v_exprType_1326_; lean_object* v_exprInit_1327_; lean_object* v_exprResult_1328_; lean_object* v_proof_1329_; uint8_t v_modified_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1375_; 
v_expr_1325_ = lean_ctor_get(v_rb_1324_, 0);
v_exprType_1326_ = lean_ctor_get(v_rb_1324_, 1);
v_exprInit_1327_ = lean_ctor_get(v_rb_1324_, 2);
v_exprResult_1328_ = lean_ctor_get(v_rb_1324_, 3);
v_proof_1329_ = lean_ctor_get(v_rb_1324_, 4);
v_modified_1330_ = lean_ctor_get_uint8(v_rb_1324_, sizeof(void*)*5);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_rb_1324_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1332_ = v_rb_1324_;
v_isShared_1333_ = v_isSharedCheck_1375_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_proof_1329_);
lean_inc(v_exprResult_1328_);
lean_inc(v_exprInit_1327_);
lean_inc(v_exprType_1326_);
lean_inc(v_expr_1325_);
lean_dec(v_rb_1324_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1375_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_expr_has_loose_bvar(v_exprType_1326_, v___x_1334_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v_expr_1338_; lean_object* v_exprType_1339_; lean_object* v___x_1340_; lean_object* v_exprInit_1341_; lean_object* v_exprResult_1342_; 
v___x_1336_ = 0;
lean_inc_ref_n(v_type_1312_, 3);
lean_inc_n(v_declName_1311_, 3);
v___x_1337_ = l_Lean_mkLambda(v_declName_1311_, v___x_1336_, v_type_1312_, v_expr_1325_);
lean_inc_ref_n(v_fst_1313_, 2);
lean_inc_ref(v___x_1337_);
v_expr_1338_ = l_Lean_Expr_app___override(v___x_1337_, v_fst_1313_);
v_exprType_1339_ = lean_expr_lower_loose_bvars(v_exprType_1326_, v___x_1314_, v___x_1314_);
lean_dec_ref(v_exprType_1326_);
v___x_1340_ = l_Lean_mkLambda(v_declName_1311_, v___x_1336_, v_type_1312_, v_exprInit_1327_);
lean_inc_ref(v_value_1315_);
lean_inc_ref(v___x_1340_);
v_exprInit_1341_ = l_Lean_Expr_app___override(v___x_1340_, v_value_1315_);
v_exprResult_1342_ = l_Lean_Expr_letE___override(v_declName_1311_, v_type_1312_, v_fst_1313_, v_exprResult_1328_, v___x_1316_);
if (v_fst_1317_ == 0)
{
lean_dec_ref(v_snd_1322_);
lean_dec_ref(v_fst_1313_);
if (v_modified_1330_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_proof_1345_; lean_object* v___x_1347_; 
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_proof_1329_);
lean_dec(v_us_1321_);
lean_dec_ref(v_value_1315_);
lean_dec_ref(v_type_1312_);
lean_dec(v_declName_1311_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1344_ = l_Lean_mkConst(v___x_1343_, v___x_1318_);
lean_inc_ref(v_expr_1338_);
lean_inc_ref(v_exprType_1339_);
v_proof_1345_ = l_Lean_mkAppB(v___x_1344_, v_exprType_1339_, v_expr_1338_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_proof_1345_);
lean_ctor_set(v___x_1332_, 3, v_exprResult_1342_);
lean_ctor_set(v___x_1332_, 2, v_exprInit_1341_);
lean_ctor_set(v___x_1332_, 1, v_exprType_1339_);
lean_ctor_set(v___x_1332_, 0, v_expr_1338_);
v___x_1347_ = v___x_1332_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_expr_1338_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_exprType_1339_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_exprInit_1341_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_exprResult_1342_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_proof_1345_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; 
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*5, v___x_1319_);
v___x_1348_ = lean_apply_2(v_toPure_1320_, lean_box(0), v___x_1347_);
return v___x_1348_;
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_proof_1353_; lean_object* v___x_1355_; 
lean_dec(v___x_1318_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1351_ = l_Lean_mkConst(v___x_1350_, v_us_1321_);
lean_inc_ref(v_type_1312_);
v___x_1352_ = l_Lean_mkLambda(v_declName_1311_, v___x_1336_, v_type_1312_, v_proof_1329_);
lean_inc_ref(v_exprType_1339_);
v_proof_1353_ = l_Lean_mkApp6(v___x_1351_, v_type_1312_, v_exprType_1339_, v_value_1315_, v___x_1340_, v___x_1337_, v___x_1352_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_proof_1353_);
lean_ctor_set(v___x_1332_, 3, v_exprResult_1342_);
lean_ctor_set(v___x_1332_, 2, v_exprInit_1341_);
lean_ctor_set(v___x_1332_, 1, v_exprType_1339_);
lean_ctor_set(v___x_1332_, 0, v_expr_1338_);
v___x_1355_ = v___x_1332_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_expr_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_exprType_1339_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_exprInit_1341_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_exprResult_1342_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_proof_1353_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*5, v___x_1316_);
v___x_1356_ = lean_apply_2(v_toPure_1320_, lean_box(0), v___x_1355_);
return v___x_1356_;
}
}
}
else
{
lean_dec(v___x_1318_);
if (v_modified_1330_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_proof_1360_; lean_object* v___x_1362_; 
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_proof_1329_);
lean_dec(v_declName_1311_);
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1359_ = l_Lean_mkConst(v___x_1358_, v_us_1321_);
lean_inc_ref(v_exprType_1339_);
v_proof_1360_ = l_Lean_mkApp6(v___x_1359_, v_type_1312_, v_exprType_1339_, v_value_1315_, v_fst_1313_, v___x_1340_, v_snd_1322_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_proof_1360_);
lean_ctor_set(v___x_1332_, 3, v_exprResult_1342_);
lean_ctor_set(v___x_1332_, 2, v_exprInit_1341_);
lean_ctor_set(v___x_1332_, 1, v_exprType_1339_);
lean_ctor_set(v___x_1332_, 0, v_expr_1338_);
v___x_1362_ = v___x_1332_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_expr_1338_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_exprType_1339_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_exprInit_1341_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_exprResult_1342_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_proof_1360_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*5, v___x_1316_);
v___x_1363_ = lean_apply_2(v_toPure_1320_, lean_box(0), v___x_1362_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_proof_1368_; lean_object* v___x_1370_; 
v___x_1365_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1366_ = l_Lean_mkConst(v___x_1365_, v_us_1321_);
lean_inc_ref(v_type_1312_);
v___x_1367_ = l_Lean_mkLambda(v_declName_1311_, v___x_1336_, v_type_1312_, v_proof_1329_);
lean_inc_ref(v_exprType_1339_);
v_proof_1368_ = l_Lean_mkApp8(v___x_1366_, v_type_1312_, v_exprType_1339_, v_value_1315_, v_fst_1313_, v___x_1340_, v___x_1337_, v_snd_1322_, v___x_1367_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_proof_1368_);
lean_ctor_set(v___x_1332_, 3, v_exprResult_1342_);
lean_ctor_set(v___x_1332_, 2, v_exprInit_1341_);
lean_ctor_set(v___x_1332_, 1, v_exprType_1339_);
lean_ctor_set(v___x_1332_, 0, v_expr_1338_);
v___x_1370_ = v___x_1332_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_expr_1338_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_exprType_1339_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_exprInit_1341_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_exprResult_1342_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_proof_1368_);
v___x_1370_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; 
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*5, v___x_1316_);
v___x_1371_ = lean_apply_2(v_toPure_1320_, lean_box(0), v___x_1370_);
return v___x_1371_;
}
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_del_object(v___x_1332_);
lean_dec_ref(v_proof_1329_);
lean_dec_ref(v_exprResult_1328_);
lean_dec_ref(v_exprInit_1327_);
lean_dec_ref(v_exprType_1326_);
lean_dec_ref(v_expr_1325_);
lean_dec_ref(v_snd_1322_);
lean_dec(v_us_1321_);
lean_dec(v_toPure_1320_);
lean_dec(v___x_1318_);
lean_dec_ref(v_value_1315_);
lean_dec_ref(v_fst_1313_);
lean_dec_ref(v_type_1312_);
lean_dec(v_declName_1311_);
v___x_1373_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1374_ = l_panic___redArg(v___x_1323_, v___x_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1376_, lean_object* v_type_1377_, lean_object* v_fst_1378_, lean_object* v___x_1379_, lean_object* v_value_1380_, lean_object* v___x_1381_, lean_object* v_fst_1382_, lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v_toPure_1385_, lean_object* v_us_1386_, lean_object* v_snd_1387_, lean_object* v___x_1388_, lean_object* v_rb_1389_){
_start:
{
uint8_t v___x_8657__boxed_1390_; uint8_t v_fst_8658__boxed_1391_; uint8_t v___x_8660__boxed_1392_; lean_object* v_res_1393_; 
v___x_8657__boxed_1390_ = lean_unbox(v___x_1381_);
v_fst_8658__boxed_1391_ = lean_unbox(v_fst_1382_);
v___x_8660__boxed_1392_ = lean_unbox(v___x_1384_);
v_res_1393_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1376_, v_type_1377_, v_fst_1378_, v___x_1379_, v_value_1380_, v___x_8657__boxed_1390_, v_fst_8658__boxed_1391_, v___x_1383_, v___x_8660__boxed_1392_, v_toPure_1385_, v_us_1386_, v_snd_1387_, v___x_1388_, v_rb_1389_);
lean_dec(v___x_1388_);
lean_dec(v___x_1379_);
return v_res_1393_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_instMonadEIO(lean_box(0));
return v___x_1397_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0);
v___x_1399_ = l_StateRefT_x27_instMonad___redArg(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1407_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1406_, v___x_1405_);
return v___x_1407_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8);
v___f_1410_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___x_1411_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1410_, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1414_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1415_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11));
v___x_1416_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1415_, v___x_1414_, v___x_1413_);
return v___x_1416_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
v___x_1418_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12);
v___f_1419_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___f_1420_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10));
v___x_1421_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1420_, v___f_1419_, v___x_1418_);
return v___x_1421_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14));
v___x_1424_ = lean_unsigned_to_nat(34u);
v___x_1425_ = lean_unsigned_to_nat(217u);
v___x_1426_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1427_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1428_ = l_mkPanicMessageWithDecl(v___x_1427_, v___x_1426_, v___x_1425_, v___x_1424_, v___x_1423_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1429_, lean_object* v_type_1430_, lean_object* v_value_1431_, uint8_t v___y_1432_, lean_object* v___x_1433_, lean_object* v_toPure_1434_, lean_object* v_us_1435_, uint8_t v___x_1436_, lean_object* v_decl_1437_, lean_object* v_x_1438_, lean_object* v_i_1439_, lean_object* v_xs_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_info_1445_, lean_object* v_fixed_1446_, lean_object* v_used_1447_, lean_object* v_body_1448_, lean_object* v_toBind_1449_, lean_object* v_withNewLemmas_1450_, lean_object* v_val_x27_1451_, lean_object* v_val_1452_, uint8_t v___x_1453_, lean_object* v_____r_1454_){
_start:
{
uint8_t v___y_1456_; lean_object* v___y_1457_; uint8_t v___y_1474_; uint8_t v___x_1476_; 
v___x_1476_ = lean_expr_eqv(v_val_1452_, v_val_x27_1451_);
if (v___x_1476_ == 0)
{
v___y_1474_ = v___y_1432_;
goto v___jp_1473_;
}
else
{
v___y_1474_ = v___x_1453_;
goto v___jp_1473_;
}
v___jp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1458_ = lean_box(v___y_1432_);
v___x_1459_ = lean_box(v___y_1456_);
v___x_1460_ = lean_box(v___x_1436_);
v___f_1461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_1461_, 0, v_declName_1429_);
lean_closure_set(v___f_1461_, 1, v_type_1430_);
lean_closure_set(v___f_1461_, 2, v___y_1457_);
lean_closure_set(v___f_1461_, 3, v_value_1431_);
lean_closure_set(v___f_1461_, 4, v___x_1458_);
lean_closure_set(v___f_1461_, 5, v___x_1433_);
lean_closure_set(v___f_1461_, 6, v___x_1459_);
lean_closure_set(v___f_1461_, 7, v_toPure_1434_);
lean_closure_set(v___f_1461_, 8, v_us_1435_);
lean_closure_set(v___f_1461_, 9, v___x_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_decl_1437_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_mk_empty_array_with_capacity(v___x_1464_);
lean_inc_ref(v_x_1438_);
v___x_1466_ = lean_array_push(v___x_1465_, v_x_1438_);
v___x_1467_ = lean_nat_add(v_i_1439_, v___x_1464_);
v___x_1468_ = lean_array_push(v_xs_1440_, v_x_1438_);
lean_inc_ref(v_inst_1443_);
lean_inc_ref(v_inst_1441_);
v___x_1469_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1441_, v_inst_1442_, v_inst_1443_, v_inst_1444_, v_info_1445_, v_fixed_1446_, v_used_1447_, v_body_1448_, v___x_1467_, v___x_1468_);
v___x_1470_ = lean_apply_4(v_toBind_1449_, lean_box(0), lean_box(0), v___x_1469_, v___f_1461_);
v___x_1471_ = lean_apply_3(v_withNewLemmas_1450_, lean_box(0), v___x_1466_, v___x_1470_);
v___x_1472_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1443_, v_inst_1441_, v___x_1463_, v___x_1471_);
return v___x_1472_;
}
v___jp_1473_:
{
if (v___y_1474_ == 0)
{
lean_inc_ref(v_value_1431_);
v___y_1456_ = v___y_1474_;
v___y_1457_ = v_value_1431_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_expr_abstract(v_val_x27_1451_, v_xs_1440_);
v___y_1456_ = v___y_1474_;
v___y_1457_ = v___x_1475_;
goto v___jp_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1477_ = _args[0];
lean_object* v_type_1478_ = _args[1];
lean_object* v_value_1479_ = _args[2];
lean_object* v___y_1480_ = _args[3];
lean_object* v___x_1481_ = _args[4];
lean_object* v_toPure_1482_ = _args[5];
lean_object* v_us_1483_ = _args[6];
lean_object* v___x_1484_ = _args[7];
lean_object* v_decl_1485_ = _args[8];
lean_object* v_x_1486_ = _args[9];
lean_object* v_i_1487_ = _args[10];
lean_object* v_xs_1488_ = _args[11];
lean_object* v_inst_1489_ = _args[12];
lean_object* v_inst_1490_ = _args[13];
lean_object* v_inst_1491_ = _args[14];
lean_object* v_inst_1492_ = _args[15];
lean_object* v_info_1493_ = _args[16];
lean_object* v_fixed_1494_ = _args[17];
lean_object* v_used_1495_ = _args[18];
lean_object* v_body_1496_ = _args[19];
lean_object* v_toBind_1497_ = _args[20];
lean_object* v_withNewLemmas_1498_ = _args[21];
lean_object* v_val_x27_1499_ = _args[22];
lean_object* v_val_1500_ = _args[23];
lean_object* v___x_1501_ = _args[24];
lean_object* v_____r_1502_ = _args[25];
_start:
{
uint8_t v___y_8918__boxed_1503_; uint8_t v___x_8920__boxed_1504_; uint8_t v___x_8926__boxed_1505_; lean_object* v_res_1506_; 
v___y_8918__boxed_1503_ = lean_unbox(v___y_1480_);
v___x_8920__boxed_1504_ = lean_unbox(v___x_1484_);
v___x_8926__boxed_1505_ = lean_unbox(v___x_1501_);
v_res_1506_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1477_, v_type_1478_, v_value_1479_, v___y_8918__boxed_1503_, v___x_1481_, v_toPure_1482_, v_us_1483_, v___x_8920__boxed_1504_, v_decl_1485_, v_x_1486_, v_i_1487_, v_xs_1488_, v_inst_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v_info_1493_, v_fixed_1494_, v_used_1495_, v_body_1496_, v_toBind_1497_, v_withNewLemmas_1498_, v_val_x27_1499_, v_val_1500_, v___x_8926__boxed_1505_, v_____r_1502_);
lean_dec_ref(v_val_1500_);
lean_dec_ref(v_val_x27_1499_);
lean_dec(v_i_1487_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1507_, lean_object* v_type_1508_, lean_object* v_value_1509_, uint8_t v___y_1510_, lean_object* v___x_1511_, lean_object* v_toPure_1512_, lean_object* v_us_1513_, uint8_t v___x_1514_, lean_object* v_decl_1515_, lean_object* v_x_1516_, lean_object* v_i_1517_, lean_object* v_xs_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_info_1523_, lean_object* v_fixed_1524_, lean_object* v_used_1525_, lean_object* v_body_1526_, lean_object* v_toBind_1527_, lean_object* v_withNewLemmas_1528_, lean_object* v_val_1529_, uint8_t v___x_1530_, lean_object* v___x_1531_, lean_object* v___x_1532_, lean_object* v_toMonadRef_1533_, lean_object* v___x_1534_, lean_object* v_val_x27_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v_cls_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1536_ = lean_box(v___y_1510_);
v___x_1537_ = lean_box(v___x_1514_);
v___x_1538_ = lean_box(v___x_1530_);
lean_inc_ref(v_val_1529_);
lean_inc_ref(v_val_x27_1535_);
lean_inc(v_toBind_1527_);
lean_inc(v_inst_1520_);
lean_inc(v_declName_1507_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 26, 25);
lean_closure_set(v___f_1539_, 0, v_declName_1507_);
lean_closure_set(v___f_1539_, 1, v_type_1508_);
lean_closure_set(v___f_1539_, 2, v_value_1509_);
lean_closure_set(v___f_1539_, 3, v___x_1536_);
lean_closure_set(v___f_1539_, 4, v___x_1511_);
lean_closure_set(v___f_1539_, 5, v_toPure_1512_);
lean_closure_set(v___f_1539_, 6, v_us_1513_);
lean_closure_set(v___f_1539_, 7, v___x_1537_);
lean_closure_set(v___f_1539_, 8, v_decl_1515_);
lean_closure_set(v___f_1539_, 9, v_x_1516_);
lean_closure_set(v___f_1539_, 10, v_i_1517_);
lean_closure_set(v___f_1539_, 11, v_xs_1518_);
lean_closure_set(v___f_1539_, 12, v_inst_1519_);
lean_closure_set(v___f_1539_, 13, v_inst_1520_);
lean_closure_set(v___f_1539_, 14, v_inst_1521_);
lean_closure_set(v___f_1539_, 15, v_inst_1522_);
lean_closure_set(v___f_1539_, 16, v_info_1523_);
lean_closure_set(v___f_1539_, 17, v_fixed_1524_);
lean_closure_set(v___f_1539_, 18, v_used_1525_);
lean_closure_set(v___f_1539_, 19, v_body_1526_);
lean_closure_set(v___f_1539_, 20, v_toBind_1527_);
lean_closure_set(v___f_1539_, 21, v_withNewLemmas_1528_);
lean_closure_set(v___f_1539_, 22, v_val_x27_1535_);
lean_closure_set(v___f_1539_, 23, v_val_1529_);
lean_closure_set(v___f_1539_, 24, v___x_1538_);
v_cls_1540_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1541_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1541_, 0, v_cls_1540_);
lean_closure_set(v___f_1541_, 1, v_declName_1507_);
lean_closure_set(v___f_1541_, 2, v_val_1529_);
lean_closure_set(v___f_1541_, 3, v_val_x27_1535_);
lean_closure_set(v___f_1541_, 4, v___x_1531_);
lean_closure_set(v___f_1541_, 5, v___x_1532_);
lean_closure_set(v___f_1541_, 6, v_toMonadRef_1533_);
lean_closure_set(v___f_1541_, 7, v___x_1534_);
v___x_1542_ = lean_apply_2(v_inst_1520_, lean_box(0), v___f_1541_);
v___x_1543_ = lean_apply_4(v_toBind_1527_, lean_box(0), lean_box(0), v___x_1542_, v___f_1539_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1544_ = _args[0];
lean_object* v_type_1545_ = _args[1];
lean_object* v_value_1546_ = _args[2];
lean_object* v___y_1547_ = _args[3];
lean_object* v___x_1548_ = _args[4];
lean_object* v_toPure_1549_ = _args[5];
lean_object* v_us_1550_ = _args[6];
lean_object* v___x_1551_ = _args[7];
lean_object* v_decl_1552_ = _args[8];
lean_object* v_x_1553_ = _args[9];
lean_object* v_i_1554_ = _args[10];
lean_object* v_xs_1555_ = _args[11];
lean_object* v_inst_1556_ = _args[12];
lean_object* v_inst_1557_ = _args[13];
lean_object* v_inst_1558_ = _args[14];
lean_object* v_inst_1559_ = _args[15];
lean_object* v_info_1560_ = _args[16];
lean_object* v_fixed_1561_ = _args[17];
lean_object* v_used_1562_ = _args[18];
lean_object* v_body_1563_ = _args[19];
lean_object* v_toBind_1564_ = _args[20];
lean_object* v_withNewLemmas_1565_ = _args[21];
lean_object* v_val_1566_ = _args[22];
lean_object* v___x_1567_ = _args[23];
lean_object* v___x_1568_ = _args[24];
lean_object* v___x_1569_ = _args[25];
lean_object* v_toMonadRef_1570_ = _args[26];
lean_object* v___x_1571_ = _args[27];
lean_object* v_val_x27_1572_ = _args[28];
_start:
{
uint8_t v___y_8865__boxed_1573_; uint8_t v___x_8867__boxed_1574_; uint8_t v___x_8873__boxed_1575_; lean_object* v_res_1576_; 
v___y_8865__boxed_1573_ = lean_unbox(v___y_1547_);
v___x_8867__boxed_1574_ = lean_unbox(v___x_1551_);
v___x_8873__boxed_1575_ = lean_unbox(v___x_1567_);
v_res_1576_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1544_, v_type_1545_, v_value_1546_, v___y_8865__boxed_1573_, v___x_1548_, v_toPure_1549_, v_us_1550_, v___x_8867__boxed_1574_, v_decl_1552_, v_x_1553_, v_i_1554_, v_xs_1555_, v_inst_1556_, v_inst_1557_, v_inst_1558_, v_inst_1559_, v_info_1560_, v_fixed_1561_, v_used_1562_, v_body_1563_, v_toBind_1564_, v_withNewLemmas_1565_, v_val_1566_, v___x_8873__boxed_1575_, v___x_1568_, v___x_1569_, v_toMonadRef_1570_, v___x_1571_, v_val_x27_1572_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1577_, lean_object* v_declName_1578_, lean_object* v_type_1579_, lean_object* v_value_1580_, uint8_t v___x_1581_, lean_object* v___x_1582_, uint8_t v___x_1583_, lean_object* v_toPure_1584_, lean_object* v_us_1585_, lean_object* v___x_1586_, lean_object* v_x_1587_, lean_object* v_i_1588_, lean_object* v_xs_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_info_1594_, lean_object* v_fixed_1595_, lean_object* v_used_1596_, lean_object* v_body_1597_, lean_object* v_toBind_1598_, lean_object* v_withNewLemmas_1599_, lean_object* v_____x_1600_){
_start:
{
lean_object* v_snd_1601_; lean_object* v_fst_1602_; lean_object* v_fst_1603_; lean_object* v_snd_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1624_; 
v_snd_1601_ = lean_ctor_get(v_____x_1600_, 1);
lean_inc(v_snd_1601_);
v_fst_1602_ = lean_ctor_get(v_____x_1600_, 0);
lean_inc(v_fst_1602_);
lean_dec_ref(v_____x_1600_);
v_fst_1603_ = lean_ctor_get(v_snd_1601_, 0);
v_snd_1604_ = lean_ctor_get(v_snd_1601_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_snd_1601_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1606_ = v_snd_1601_;
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_snd_1604_);
lean_inc(v_fst_1603_);
lean_dec(v_snd_1601_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_box(0);
if (v_isShared_1607_ == 0)
{
lean_ctor_set_tag(v___x_1606_, 1);
lean_ctor_set(v___x_1606_, 1, v___x_1608_);
lean_ctor_set(v___x_1606_, 0, v_decl_1577_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_decl_1577_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
v___x_1612_ = lean_box(v___x_1581_);
v___x_1613_ = lean_box(v___x_1583_);
v___f_1614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 14, 13);
lean_closure_set(v___f_1614_, 0, v_declName_1578_);
lean_closure_set(v___f_1614_, 1, v_type_1579_);
lean_closure_set(v___f_1614_, 2, v_fst_1602_);
lean_closure_set(v___f_1614_, 3, v___x_1611_);
lean_closure_set(v___f_1614_, 4, v_value_1580_);
lean_closure_set(v___f_1614_, 5, v___x_1612_);
lean_closure_set(v___f_1614_, 6, v_fst_1603_);
lean_closure_set(v___f_1614_, 7, v___x_1582_);
lean_closure_set(v___f_1614_, 8, v___x_1613_);
lean_closure_set(v___f_1614_, 9, v_toPure_1584_);
lean_closure_set(v___f_1614_, 10, v_us_1585_);
lean_closure_set(v___f_1614_, 11, v_snd_1604_);
lean_closure_set(v___f_1614_, 12, v___x_1586_);
v___x_1615_ = lean_mk_empty_array_with_capacity(v___x_1611_);
lean_inc_ref(v_x_1587_);
v___x_1616_ = lean_array_push(v___x_1615_, v_x_1587_);
v___x_1617_ = lean_nat_add(v_i_1588_, v___x_1611_);
v___x_1618_ = lean_array_push(v_xs_1589_, v_x_1587_);
lean_inc_ref(v_inst_1592_);
lean_inc_ref(v_inst_1590_);
v___x_1619_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1590_, v_inst_1591_, v_inst_1592_, v_inst_1593_, v_info_1594_, v_fixed_1595_, v_used_1596_, v_body_1597_, v___x_1617_, v___x_1618_);
v___x_1620_ = lean_apply_4(v_toBind_1598_, lean_box(0), lean_box(0), v___x_1619_, v___f_1614_);
v___x_1621_ = lean_apply_3(v_withNewLemmas_1599_, lean_box(0), v___x_1616_, v___x_1620_);
v___x_1622_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1592_, v_inst_1590_, v___x_1610_, v___x_1621_);
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1625_ = _args[0];
lean_object* v_declName_1626_ = _args[1];
lean_object* v_type_1627_ = _args[2];
lean_object* v_value_1628_ = _args[3];
lean_object* v___x_1629_ = _args[4];
lean_object* v___x_1630_ = _args[5];
lean_object* v___x_1631_ = _args[6];
lean_object* v_toPure_1632_ = _args[7];
lean_object* v_us_1633_ = _args[8];
lean_object* v___x_1634_ = _args[9];
lean_object* v_x_1635_ = _args[10];
lean_object* v_i_1636_ = _args[11];
lean_object* v_xs_1637_ = _args[12];
lean_object* v_inst_1638_ = _args[13];
lean_object* v_inst_1639_ = _args[14];
lean_object* v_inst_1640_ = _args[15];
lean_object* v_inst_1641_ = _args[16];
lean_object* v_info_1642_ = _args[17];
lean_object* v_fixed_1643_ = _args[18];
lean_object* v_used_1644_ = _args[19];
lean_object* v_body_1645_ = _args[20];
lean_object* v_toBind_1646_ = _args[21];
lean_object* v_withNewLemmas_1647_ = _args[22];
lean_object* v_____x_1648_ = _args[23];
_start:
{
uint8_t v___x_8889__boxed_1649_; uint8_t v___x_8891__boxed_1650_; lean_object* v_res_1651_; 
v___x_8889__boxed_1649_ = lean_unbox(v___x_1629_);
v___x_8891__boxed_1650_ = lean_unbox(v___x_1631_);
v_res_1651_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1625_, v_declName_1626_, v_type_1627_, v_value_1628_, v___x_8889__boxed_1649_, v___x_1630_, v___x_8891__boxed_1650_, v_toPure_1632_, v_us_1633_, v___x_1634_, v_x_1635_, v_i_1636_, v_xs_1637_, v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_info_1642_, v_fixed_1643_, v_used_1644_, v_body_1645_, v_toBind_1646_, v_withNewLemmas_1647_, v_____x_1648_);
lean_dec(v_i_1636_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1652_ = _args[0];
lean_object* v_declName_1653_ = _args[1];
lean_object* v_type_1654_ = _args[2];
lean_object* v_value_1655_ = _args[3];
lean_object* v_us_1656_ = _args[4];
lean_object* v___x_1657_ = _args[5];
lean_object* v___x_1658_ = _args[6];
lean_object* v_toPure_1659_ = _args[7];
lean_object* v_i_1660_ = _args[8];
lean_object* v_xs_1661_ = _args[9];
lean_object* v_inst_1662_ = _args[10];
lean_object* v_inst_1663_ = _args[11];
lean_object* v_inst_1664_ = _args[12];
lean_object* v_inst_1665_ = _args[13];
lean_object* v_info_1666_ = _args[14];
lean_object* v_fixed_1667_ = _args[15];
lean_object* v_used_1668_ = _args[16];
lean_object* v_body_1669_ = _args[17];
lean_object* v_toBind_1670_ = _args[18];
lean_object* v_____r_1671_ = _args[19];
_start:
{
uint8_t v___x_8848__boxed_1672_; lean_object* v_res_1673_; 
v___x_8848__boxed_1672_ = lean_unbox(v___x_1658_);
v_res_1673_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1652_, v_declName_1653_, v_type_1654_, v_value_1655_, v_us_1656_, v___x_1657_, v___x_8848__boxed_1672_, v_toPure_1659_, v_i_1660_, v_xs_1661_, v_inst_1662_, v_inst_1663_, v_inst_1664_, v_inst_1665_, v_info_1666_, v_fixed_1667_, v_used_1668_, v_body_1669_, v_toBind_1670_, v_____r_1671_);
lean_dec(v_i_1660_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_info_1678_, lean_object* v_fixed_1679_, lean_object* v_used_1680_, lean_object* v_e_1681_, lean_object* v_i_1682_, lean_object* v_xs_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v_toApplicative_1685_; lean_object* v_toFunctor_1686_; lean_object* v_toSeq_1687_; lean_object* v_toSeqLeft_1688_; lean_object* v_toSeqRight_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_toApplicative_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1802_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v_toApplicative_1685_ = lean_ctor_get(v___x_1684_, 0);
v_toFunctor_1686_ = lean_ctor_get(v_toApplicative_1685_, 0);
v_toSeq_1687_ = lean_ctor_get(v_toApplicative_1685_, 2);
v_toSeqLeft_1688_ = lean_ctor_get(v_toApplicative_1685_, 3);
v_toSeqRight_1689_ = lean_ctor_get(v_toApplicative_1685_, 4);
v___f_1690_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2));
v___f_1691_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1686_, 2);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toFunctor_1686_);
v___f_1693_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1693_, 0, v_toFunctor_1686_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___f_1692_);
lean_ctor_set(v___x_1694_, 1, v___f_1693_);
lean_inc(v_toSeqRight_1689_);
v___f_1695_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1695_, 0, v_toSeqRight_1689_);
lean_inc(v_toSeqLeft_1688_);
v___f_1696_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1696_, 0, v_toSeqLeft_1688_);
lean_inc(v_toSeq_1687_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toSeq_1687_);
v___x_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1694_);
lean_ctor_set(v___x_1698_, 1, v___f_1690_);
lean_ctor_set(v___x_1698_, 2, v___f_1697_);
lean_ctor_set(v___x_1698_, 3, v___f_1696_);
lean_ctor_set(v___x_1698_, 4, v___f_1695_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___f_1691_);
v___x_1700_ = l_StateRefT_x27_instMonad___redArg(v___x_1699_);
v_toApplicative_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v___x_1700_, 1);
lean_dec(v_unused_1803_);
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1802_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_toApplicative_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1802_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_toFunctor_1705_; lean_object* v_toSeq_1706_; lean_object* v_toSeqLeft_1707_; lean_object* v_toSeqRight_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1800_; 
v_toFunctor_1705_ = lean_ctor_get(v_toApplicative_1701_, 0);
v_toSeq_1706_ = lean_ctor_get(v_toApplicative_1701_, 2);
v_toSeqLeft_1707_ = lean_ctor_get(v_toApplicative_1701_, 3);
v_toSeqRight_1708_ = lean_ctor_get(v_toApplicative_1701_, 4);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_toApplicative_1701_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_toApplicative_1701_, 1);
lean_dec(v_unused_1801_);
v___x_1710_ = v_toApplicative_1701_;
v_isShared_1711_ = v_isSharedCheck_1800_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_toSeqRight_1708_);
lean_inc(v_toSeqLeft_1707_);
lean_inc(v_toSeq_1706_);
lean_inc(v_toFunctor_1705_);
lean_dec(v_toApplicative_1701_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1800_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___x_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1721_; 
v___f_1712_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4));
v___f_1713_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5));
lean_inc_ref(v_toFunctor_1705_);
v___f_1714_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1714_, 0, v_toFunctor_1705_);
v___f_1715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1715_, 0, v_toFunctor_1705_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___f_1714_);
lean_ctor_set(v___x_1716_, 1, v___f_1715_);
v___f_1717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1717_, 0, v_toSeqRight_1708_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toSeqLeft_1707_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toSeq_1706_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 4, v___f_1717_);
lean_ctor_set(v___x_1710_, 3, v___f_1718_);
lean_ctor_set(v___x_1710_, 2, v___f_1719_);
lean_ctor_set(v___x_1710_, 1, v___f_1712_);
lean_ctor_set(v___x_1710_, 0, v___x_1716_);
v___x_1721_ = v___x_1710_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___f_1712_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v___f_1719_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v___f_1718_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v___f_1717_);
v___x_1721_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v___f_1713_);
lean_ctor_set(v___x_1703_, 0, v___x_1721_);
v___x_1723_ = v___x_1703_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___f_1713_);
v___x_1723_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_toApplicative_1726_; lean_object* v_toMonadRef_1727_; lean_object* v_haveInfo_1728_; lean_object* v_body_1729_; lean_object* v_bodyType_1730_; lean_object* v_level_1731_; lean_object* v_toBind_1732_; lean_object* v_toPure_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1724_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9);
v___x_1725_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13);
v_toApplicative_1726_ = lean_ctor_get(v_inst_1674_, 0);
v_toMonadRef_1727_ = lean_ctor_get(v___x_1725_, 0);
v_haveInfo_1728_ = lean_ctor_get(v_info_1678_, 0);
v_body_1729_ = lean_ctor_get(v_info_1678_, 3);
v_bodyType_1730_ = lean_ctor_get(v_info_1678_, 4);
v_level_1731_ = lean_ctor_get(v_info_1678_, 5);
v_toBind_1732_ = lean_ctor_get(v_inst_1674_, 1);
lean_inc(v_toBind_1732_);
v_toPure_1733_ = lean_ctor_get(v_toApplicative_1726_, 1);
lean_inc(v_toPure_1733_);
v___x_1734_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1735_ = lean_array_get_size(v_haveInfo_1728_);
v___x_1736_ = lean_nat_dec_lt(v_i_1682_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v_cls_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_inc(v_level_1731_);
lean_inc_ref(v_bodyType_1730_);
lean_inc_ref_n(v_body_1729_, 2);
lean_dec(v_i_1682_);
lean_dec_ref(v_used_1680_);
lean_dec_ref(v_fixed_1679_);
lean_dec_ref(v_info_1678_);
lean_dec_ref(v_inst_1676_);
lean_dec_ref(v_inst_1674_);
v___x_1737_ = lean_box(v___x_1736_);
lean_inc(v_toBind_1732_);
v___f_1738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1738_, 0, v_inst_1677_);
lean_closure_set(v___f_1738_, 1, v_bodyType_1730_);
lean_closure_set(v___f_1738_, 2, v_xs_1683_);
lean_closure_set(v___f_1738_, 3, v_level_1731_);
lean_closure_set(v___f_1738_, 4, v_e_1681_);
lean_closure_set(v___f_1738_, 5, v___x_1737_);
lean_closure_set(v___f_1738_, 6, v_toPure_1733_);
lean_closure_set(v___f_1738_, 7, v_body_1729_);
lean_closure_set(v___f_1738_, 8, v_toBind_1732_);
v_cls_1739_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1727_);
v___f_1740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1740_, 0, v_cls_1739_);
lean_closure_set(v___f_1740_, 1, v_body_1729_);
lean_closure_set(v___f_1740_, 2, v___x_1723_);
lean_closure_set(v___f_1740_, 3, v___x_1724_);
lean_closure_set(v___f_1740_, 4, v_toMonadRef_1727_);
lean_closure_set(v___f_1740_, 5, v___x_1734_);
v___x_1741_ = lean_apply_2(v_inst_1675_, lean_box(0), v___f_1740_);
v___x_1742_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1741_, v___f_1738_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
lean_inc_ref(v_inst_1674_);
v___x_1744_ = l_instInhabitedOfMonad___redArg(v_inst_1674_, v___x_1743_);
if (lean_obj_tag(v_e_1681_) == 8)
{
uint8_t v_nondep_1748_; 
v_nondep_1748_ = lean_ctor_get_uint8(v_e_1681_, sizeof(void*)*4 + 8);
if (v_nondep_1748_ == 1)
{
lean_object* v_declName_1749_; lean_object* v_type_1750_; lean_object* v_value_1751_; lean_object* v_body_1752_; lean_object* v_hinfo_1753_; lean_object* v_decl_1754_; lean_object* v_level_1755_; lean_object* v_x_1756_; lean_object* v_val_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_us_1760_; uint8_t v___y_1762_; uint8_t v___y_1763_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_declName_1749_ = lean_ctor_get(v_e_1681_, 0);
lean_inc(v_declName_1749_);
v_type_1750_ = lean_ctor_get(v_e_1681_, 1);
lean_inc_ref(v_type_1750_);
v_value_1751_ = lean_ctor_get(v_e_1681_, 2);
lean_inc_ref(v_value_1751_);
v_body_1752_ = lean_ctor_get(v_e_1681_, 3);
lean_inc_ref(v_body_1752_);
lean_dec_ref_known(v_e_1681_, 4);
v_hinfo_1753_ = lean_array_fget_borrowed(v_haveInfo_1728_, v_i_1682_);
v_decl_1754_ = lean_ctor_get(v_hinfo_1753_, 2);
v_level_1755_ = lean_ctor_get(v_hinfo_1753_, 3);
lean_inc_ref(v_decl_1754_);
v_x_1756_ = l_Lean_LocalDecl_toExpr(v_decl_1754_);
v_val_1757_ = l_Lean_LocalDecl_value(v_decl_1754_, v___x_1736_);
v___x_1758_ = lean_box(0);
lean_inc(v_level_1731_);
v___x_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_level_1731_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
lean_inc_ref(v___x_1759_);
lean_inc(v_level_1755_);
v_us_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1760_, 0, v_level_1755_);
lean_ctor_set(v_us_1760_, 1, v___x_1759_);
v___x_1788_ = lean_array_get_size(v_used_1680_);
v___x_1789_ = lean_nat_dec_lt(v_i_1682_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_inc_ref(v_decl_1754_);
goto v___jp_1772_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_array_fget_borrowed(v_used_1680_, v_i_1682_);
v___x_1791_ = lean_unbox(v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v_cls_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v_x_1756_);
lean_dec(v___x_1744_);
v___x_1792_ = lean_box(v___x_1736_);
lean_inc(v_toBind_1732_);
lean_inc(v_inst_1675_);
lean_inc(v_declName_1749_);
v___f_1793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1793_, 0, v___x_1758_);
lean_closure_set(v___f_1793_, 1, v_declName_1749_);
lean_closure_set(v___f_1793_, 2, v_type_1750_);
lean_closure_set(v___f_1793_, 3, v_value_1751_);
lean_closure_set(v___f_1793_, 4, v_us_1760_);
lean_closure_set(v___f_1793_, 5, v___x_1759_);
lean_closure_set(v___f_1793_, 6, v___x_1792_);
lean_closure_set(v___f_1793_, 7, v_toPure_1733_);
lean_closure_set(v___f_1793_, 8, v_i_1682_);
lean_closure_set(v___f_1793_, 9, v_xs_1683_);
lean_closure_set(v___f_1793_, 10, v_inst_1674_);
lean_closure_set(v___f_1793_, 11, v_inst_1675_);
lean_closure_set(v___f_1793_, 12, v_inst_1676_);
lean_closure_set(v___f_1793_, 13, v_inst_1677_);
lean_closure_set(v___f_1793_, 14, v_info_1678_);
lean_closure_set(v___f_1793_, 15, v_fixed_1679_);
lean_closure_set(v___f_1793_, 16, v_used_1680_);
lean_closure_set(v___f_1793_, 17, v_body_1752_);
lean_closure_set(v___f_1793_, 18, v_toBind_1732_);
v_cls_1794_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1727_);
v___f_1795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1795_, 0, v_cls_1794_);
lean_closure_set(v___f_1795_, 1, v_declName_1749_);
lean_closure_set(v___f_1795_, 2, v_val_1757_);
lean_closure_set(v___f_1795_, 3, v___x_1723_);
lean_closure_set(v___f_1795_, 4, v___x_1724_);
lean_closure_set(v___f_1795_, 5, v_toMonadRef_1727_);
lean_closure_set(v___f_1795_, 6, v___x_1734_);
v___x_1796_ = lean_apply_2(v_inst_1675_, lean_box(0), v___f_1795_);
v___x_1797_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1796_, v___f_1793_);
return v___x_1797_;
}
else
{
lean_inc_ref(v_decl_1754_);
goto v___jp_1772_;
}
}
v___jp_1761_:
{
lean_object* v_withNewLemmas_1764_; lean_object* v_dsimp_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_withNewLemmas_1764_ = lean_ctor_get(v_inst_1677_, 0);
lean_inc(v_withNewLemmas_1764_);
v_dsimp_1765_ = lean_ctor_get(v_inst_1677_, 1);
lean_inc(v_dsimp_1765_);
v___x_1766_ = lean_box(v___y_1763_);
v___x_1767_ = lean_box(v___x_1736_);
v___x_1768_ = lean_box(v___y_1762_);
lean_inc_ref(v_toMonadRef_1727_);
lean_inc_ref(v_val_1757_);
lean_inc(v_toBind_1732_);
v___f_1769_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 29, 28);
lean_closure_set(v___f_1769_, 0, v_declName_1749_);
lean_closure_set(v___f_1769_, 1, v_type_1750_);
lean_closure_set(v___f_1769_, 2, v_value_1751_);
lean_closure_set(v___f_1769_, 3, v___x_1766_);
lean_closure_set(v___f_1769_, 4, v___x_1759_);
lean_closure_set(v___f_1769_, 5, v_toPure_1733_);
lean_closure_set(v___f_1769_, 6, v_us_1760_);
lean_closure_set(v___f_1769_, 7, v___x_1767_);
lean_closure_set(v___f_1769_, 8, v_decl_1754_);
lean_closure_set(v___f_1769_, 9, v_x_1756_);
lean_closure_set(v___f_1769_, 10, v_i_1682_);
lean_closure_set(v___f_1769_, 11, v_xs_1683_);
lean_closure_set(v___f_1769_, 12, v_inst_1674_);
lean_closure_set(v___f_1769_, 13, v_inst_1675_);
lean_closure_set(v___f_1769_, 14, v_inst_1676_);
lean_closure_set(v___f_1769_, 15, v_inst_1677_);
lean_closure_set(v___f_1769_, 16, v_info_1678_);
lean_closure_set(v___f_1769_, 17, v_fixed_1679_);
lean_closure_set(v___f_1769_, 18, v_used_1680_);
lean_closure_set(v___f_1769_, 19, v_body_1752_);
lean_closure_set(v___f_1769_, 20, v_toBind_1732_);
lean_closure_set(v___f_1769_, 21, v_withNewLemmas_1764_);
lean_closure_set(v___f_1769_, 22, v_val_1757_);
lean_closure_set(v___f_1769_, 23, v___x_1768_);
lean_closure_set(v___f_1769_, 24, v___x_1723_);
lean_closure_set(v___f_1769_, 25, v___x_1724_);
lean_closure_set(v___f_1769_, 26, v_toMonadRef_1727_);
lean_closure_set(v___f_1769_, 27, v___x_1734_);
v___x_1770_ = lean_apply_1(v_dsimp_1765_, v_val_1757_);
v___x_1771_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1770_, v___f_1769_);
return v___x_1771_;
}
v___jp_1772_:
{
uint8_t v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = 0;
v___x_1774_ = lean_array_get_size(v_fixed_1679_);
v___x_1775_ = lean_nat_dec_lt(v_i_1682_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_dec(v___x_1744_);
v___y_1762_ = v___x_1773_;
v___y_1763_ = v___x_1736_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_array_fget_borrowed(v_fixed_1679_, v_i_1682_);
v___x_1777_ = lean_unbox(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v_withNewLemmas_1778_; lean_object* v_simp_1779_; lean_object* v___x_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_inc_n(v___x_1776_, 2);
lean_inc(v_level_1755_);
v_withNewLemmas_1778_ = lean_ctor_get(v_inst_1677_, 0);
lean_inc(v_withNewLemmas_1778_);
v_simp_1779_ = lean_ctor_get(v_inst_1677_, 2);
lean_inc(v_simp_1779_);
v___x_1780_ = lean_box(v___x_1736_);
lean_inc_n(v_toBind_1732_, 2);
lean_inc(v_inst_1675_);
lean_inc_ref(v_xs_1683_);
lean_inc(v_toPure_1733_);
lean_inc_ref(v_value_1751_);
lean_inc_ref(v_type_1750_);
lean_inc(v_declName_1749_);
v___f_1781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 24, 23);
lean_closure_set(v___f_1781_, 0, v_decl_1754_);
lean_closure_set(v___f_1781_, 1, v_declName_1749_);
lean_closure_set(v___f_1781_, 2, v_type_1750_);
lean_closure_set(v___f_1781_, 3, v_value_1751_);
lean_closure_set(v___f_1781_, 4, v___x_1780_);
lean_closure_set(v___f_1781_, 5, v___x_1759_);
lean_closure_set(v___f_1781_, 6, v___x_1776_);
lean_closure_set(v___f_1781_, 7, v_toPure_1733_);
lean_closure_set(v___f_1781_, 8, v_us_1760_);
lean_closure_set(v___f_1781_, 9, v___x_1744_);
lean_closure_set(v___f_1781_, 10, v_x_1756_);
lean_closure_set(v___f_1781_, 11, v_i_1682_);
lean_closure_set(v___f_1781_, 12, v_xs_1683_);
lean_closure_set(v___f_1781_, 13, v_inst_1674_);
lean_closure_set(v___f_1781_, 14, v_inst_1675_);
lean_closure_set(v___f_1781_, 15, v_inst_1676_);
lean_closure_set(v___f_1781_, 16, v_inst_1677_);
lean_closure_set(v___f_1781_, 17, v_info_1678_);
lean_closure_set(v___f_1781_, 18, v_fixed_1679_);
lean_closure_set(v___f_1781_, 19, v_used_1680_);
lean_closure_set(v___f_1781_, 20, v_body_1752_);
lean_closure_set(v___f_1781_, 21, v_toBind_1732_);
lean_closure_set(v___f_1781_, 22, v_withNewLemmas_1778_);
v___f_1782_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1782_, 0, v___f_1781_);
v___x_1783_ = lean_box(v___x_1736_);
lean_inc_ref(v_toMonadRef_1727_);
lean_inc_ref(v_val_1757_);
lean_inc_ref(v___f_1782_);
v___f_1784_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_1784_, 0, v_level_1755_);
lean_closure_set(v___f_1784_, 1, v___x_1758_);
lean_closure_set(v___f_1784_, 2, v_type_1750_);
lean_closure_set(v___f_1784_, 3, v_value_1751_);
lean_closure_set(v___f_1784_, 4, v___x_1776_);
lean_closure_set(v___f_1784_, 5, v_toPure_1733_);
lean_closure_set(v___f_1784_, 6, v_toBind_1732_);
lean_closure_set(v___f_1784_, 7, v___f_1782_);
lean_closure_set(v___f_1784_, 8, v_xs_1683_);
lean_closure_set(v___f_1784_, 9, v___x_1783_);
lean_closure_set(v___f_1784_, 10, v___f_1782_);
lean_closure_set(v___f_1784_, 11, v_declName_1749_);
lean_closure_set(v___f_1784_, 12, v_val_1757_);
lean_closure_set(v___f_1784_, 13, v___x_1723_);
lean_closure_set(v___f_1784_, 14, v___x_1724_);
lean_closure_set(v___f_1784_, 15, v_toMonadRef_1727_);
lean_closure_set(v___f_1784_, 16, v___x_1734_);
lean_closure_set(v___f_1784_, 17, v_inst_1675_);
v___x_1785_ = lean_apply_1(v_simp_1779_, v_val_1757_);
v___x_1786_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1785_, v___f_1784_);
return v___x_1786_;
}
else
{
uint8_t v___x_1787_; 
lean_dec(v___x_1744_);
v___x_1787_ = lean_unbox(v___x_1776_);
v___y_1762_ = v___x_1773_;
v___y_1763_ = v___x_1787_;
goto v___jp_1761_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1681_, 4);
lean_dec(v_toPure_1733_);
lean_dec(v_toBind_1732_);
lean_dec_ref(v___x_1723_);
lean_dec_ref(v_xs_1683_);
lean_dec(v_i_1682_);
lean_dec_ref(v_used_1680_);
lean_dec_ref(v_fixed_1679_);
lean_dec_ref(v_info_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec_ref(v_inst_1676_);
lean_dec(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
goto v___jp_1745_;
}
}
else
{
lean_dec(v_toPure_1733_);
lean_dec(v_toBind_1732_);
lean_dec_ref(v___x_1723_);
lean_dec_ref(v_xs_1683_);
lean_dec(v_i_1682_);
lean_dec_ref(v_e_1681_);
lean_dec_ref(v_used_1680_);
lean_dec_ref(v_fixed_1679_);
lean_dec_ref(v_info_1678_);
lean_dec_ref(v_inst_1677_);
lean_dec_ref(v_inst_1676_);
lean_dec(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
goto v___jp_1745_;
}
v___jp_1745_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15);
v___x_1747_ = l_panic___redArg(v___x_1744_, v___x_1746_);
lean_dec(v___x_1744_);
return v___x_1747_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1804_, lean_object* v_declName_1805_, lean_object* v_type_1806_, lean_object* v_value_1807_, lean_object* v_us_1808_, lean_object* v___x_1809_, uint8_t v___x_1810_, lean_object* v_toPure_1811_, lean_object* v_i_1812_, lean_object* v_xs_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_info_1818_, lean_object* v_fixed_1819_, lean_object* v_used_1820_, lean_object* v_body_1821_, lean_object* v_toBind_1822_, lean_object* v_____r_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v_x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1824_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1825_ = l_Lean_mkConst(v___x_1824_, v___x_1804_);
v___x_1826_ = lean_unsigned_to_nat(1u);
v___x_1827_ = lean_box(v___x_1810_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1828_, 0, v___x_1826_);
lean_closure_set(v___f_1828_, 1, v_declName_1805_);
lean_closure_set(v___f_1828_, 2, v_type_1806_);
lean_closure_set(v___f_1828_, 3, v_value_1807_);
lean_closure_set(v___f_1828_, 4, v_us_1808_);
lean_closure_set(v___f_1828_, 5, v___x_1809_);
lean_closure_set(v___f_1828_, 6, v___x_1827_);
lean_closure_set(v___f_1828_, 7, v_toPure_1811_);
v___x_1829_ = lean_nat_add(v_i_1812_, v___x_1826_);
v___x_1830_ = lean_array_push(v_xs_1813_, v_x_1825_);
v___x_1831_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1814_, v_inst_1815_, v_inst_1816_, v_inst_1817_, v_info_1818_, v_fixed_1819_, v_used_1820_, v_body_1821_, v___x_1829_, v___x_1830_);
v___x_1832_ = lean_apply_4(v_toBind_1822_, lean_box(0), lean_box(0), v___x_1831_, v___f_1828_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_info_1838_, lean_object* v_fixed_1839_, lean_object* v_used_1840_, lean_object* v_e_1841_, lean_object* v_i_1842_, lean_object* v_xs_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_info_1838_, v_fixed_1839_, v_used_1840_, v_e_1841_, v_i_1842_, v_xs_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_1845_){
_start:
{
switch(v_x_1845_)
{
case 0:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
return v___x_1846_;
}
case 1:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
return v___x_1847_;
}
default: 
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_unsigned_to_nat(2u);
return v___x_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_1849_){
_start:
{
uint8_t v_x_boxed_1850_; lean_object* v_res_1851_; 
v_x_boxed_1850_ = lean_unbox(v_x_1849_);
v_res_1851_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_1850_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_1852_){
_start:
{
lean_inc(v_k_1852_);
return v_k_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_1853_);
lean_dec(v_k_1853_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_1855_, lean_object* v_ctorIdx_1856_, uint8_t v_t_1857_, lean_object* v_h_1858_, lean_object* v_k_1859_){
_start:
{
lean_inc(v_k_1859_);
return v_k_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_1860_, lean_object* v_ctorIdx_1861_, lean_object* v_t_1862_, lean_object* v_h_1863_, lean_object* v_k_1864_){
_start:
{
uint8_t v_t_boxed_1865_; lean_object* v_res_1866_; 
v_t_boxed_1865_ = lean_unbox(v_t_1862_);
v_res_1866_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_1860_, v_ctorIdx_1861_, v_t_boxed_1865_, v_h_1863_, v_k_1864_);
lean_dec(v_k_1864_);
lean_dec(v_ctorIdx_1861_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_1867_){
_start:
{
lean_inc(v_no_1867_);
return v_no_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_1868_);
lean_dec(v_no_1868_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_1870_, uint8_t v_t_1871_, lean_object* v_h_1872_, lean_object* v_no_1873_){
_start:
{
lean_inc(v_no_1873_);
return v_no_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_1874_, lean_object* v_t_1875_, lean_object* v_h_1876_, lean_object* v_no_1877_){
_start:
{
uint8_t v_t_boxed_1878_; lean_object* v_res_1879_; 
v_t_boxed_1878_ = lean_unbox(v_t_1875_);
v_res_1879_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_1874_, v_t_boxed_1878_, v_h_1876_, v_no_1877_);
lean_dec(v_no_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_1880_){
_start:
{
lean_inc(v_singlePass_1880_);
return v_singlePass_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_1881_);
lean_dec(v_singlePass_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_1883_, uint8_t v_t_1884_, lean_object* v_h_1885_, lean_object* v_singlePass_1886_){
_start:
{
lean_inc(v_singlePass_1886_);
return v_singlePass_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_1887_, lean_object* v_t_1888_, lean_object* v_h_1889_, lean_object* v_singlePass_1890_){
_start:
{
uint8_t v_t_boxed_1891_; lean_object* v_res_1892_; 
v_t_boxed_1891_ = lean_unbox(v_t_1888_);
v_res_1892_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_1887_, v_t_boxed_1891_, v_h_1889_, v_singlePass_1890_);
lean_dec(v_singlePass_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_1893_){
_start:
{
lean_inc(v_twoPasses_1893_);
return v_twoPasses_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_1894_);
lean_dec(v_twoPasses_1894_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_1896_, uint8_t v_t_1897_, lean_object* v_h_1898_, lean_object* v_twoPasses_1899_){
_start:
{
lean_inc(v_twoPasses_1899_);
return v_twoPasses_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_1900_, lean_object* v_t_1901_, lean_object* v_h_1902_, lean_object* v_twoPasses_1903_){
_start:
{
uint8_t v_t_boxed_1904_; lean_object* v_res_1905_; 
v_t_boxed_1904_ = lean_unbox(v_t_1901_);
v_res_1905_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_1900_, v_t_boxed_1904_, v_h_1902_, v_twoPasses_1903_);
lean_dec(v_twoPasses_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_1906_, lean_object* v_b_1907_, lean_object* v_c_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
v___x_1914_ = lean_apply_7(v_k_1906_, v_b_1907_, v_c_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, lean_box(0));
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_1915_, lean_object* v_b_1916_, lean_object* v_c_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_1915_, v_b_1916_, v_c_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_1924_, lean_object* v_k_1925_, uint8_t v_cleanupAnnotations_1926_, uint8_t v_preserveNondepLet_1927_, uint8_t v_nondepLetOnly_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___f_1934_; uint8_t v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1934_, 0, v_k_1925_);
v___x_1935_ = 0;
v___x_1936_ = 1;
v___x_1937_ = lean_box(0);
v___x_1938_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1924_, v___x_1935_, v___x_1936_, v_preserveNondepLet_1927_, v_nondepLetOnly_1928_, v___x_1937_, v___f_1934_, v_cleanupAnnotations_1926_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1938_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1938_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_1955_, lean_object* v_k_1956_, lean_object* v_cleanupAnnotations_1957_, lean_object* v_preserveNondepLet_1958_, lean_object* v_nondepLetOnly_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1965_; uint8_t v_preserveNondepLet_boxed_1966_; uint8_t v_nondepLetOnly_boxed_1967_; lean_object* v_res_1968_; 
v_cleanupAnnotations_boxed_1965_ = lean_unbox(v_cleanupAnnotations_1957_);
v_preserveNondepLet_boxed_1966_ = lean_unbox(v_preserveNondepLet_1958_);
v_nondepLetOnly_boxed_1967_ = lean_unbox(v_nondepLetOnly_1959_);
v_res_1968_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1955_, v_k_1956_, v_cleanupAnnotations_boxed_1965_, v_preserveNondepLet_boxed_1966_, v_nondepLetOnly_boxed_1967_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_1969_, lean_object* v_e_1970_, lean_object* v_k_1971_, uint8_t v_cleanupAnnotations_1972_, uint8_t v_preserveNondepLet_1973_, uint8_t v_nondepLetOnly_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1970_, v_k_1971_, v_cleanupAnnotations_1972_, v_preserveNondepLet_1973_, v_nondepLetOnly_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_e_1982_, lean_object* v_k_1983_, lean_object* v_cleanupAnnotations_1984_, lean_object* v_preserveNondepLet_1985_, lean_object* v_nondepLetOnly_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1992_; uint8_t v_preserveNondepLet_boxed_1993_; uint8_t v_nondepLetOnly_boxed_1994_; lean_object* v_res_1995_; 
v_cleanupAnnotations_boxed_1992_ = lean_unbox(v_cleanupAnnotations_1984_);
v_preserveNondepLet_boxed_1993_ = lean_unbox(v_preserveNondepLet_1985_);
v_nondepLetOnly_boxed_1994_ = lean_unbox(v_nondepLetOnly_1986_);
v_res_1995_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_1981_, v_e_1982_, v_k_1983_, v_cleanupAnnotations_boxed_1992_, v_preserveNondepLet_boxed_1993_, v_nondepLetOnly_boxed_1994_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_1996_, lean_object* v_a_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_snd_2002_; lean_object* v_fst_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2058_; 
v_snd_2002_ = lean_ctor_get(v_a_1997_, 1);
v_fst_2003_ = lean_ctor_get(v_a_1997_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_a_1997_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2005_ = v_a_1997_;
v_isShared_2006_ = v_isSharedCheck_2058_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2002_);
lean_inc(v_fst_2003_);
lean_dec(v_a_1997_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2058_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2057_; 
v_fst_2007_ = lean_ctor_get(v_snd_2002_, 0);
v_snd_2008_ = lean_ctor_get(v_snd_2002_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_snd_2002_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2010_ = v_snd_2002_;
v_isShared_2011_ = v_isSharedCheck_2057_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_snd_2002_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2057_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = lean_nat_dec_lt(v___x_2012_, v_snd_2008_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2015_; 
if (v_isShared_2011_ == 0)
{
v___x_2015_ = v___x_2010_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_fst_2007_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_snd_2008_);
v___x_2015_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2015_);
v___x_2017_ = v___x_2005_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_fst_2003_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
}
}
else
{
lean_object* v_fvarSet_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_fvarSet_2021_ = lean_ctor_get(v_fst_2003_, 1);
v___x_2022_ = l_Lean_instInhabitedExpr;
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_sub(v_snd_2008_, v___x_2023_);
lean_dec(v_snd_2008_);
v___x_2025_ = lean_array_get_borrowed(v___x_2022_, v_xs_1996_, v___x_2024_);
v___x_2026_ = l_Lean_Expr_fvarId_x21(v___x_2025_);
v___x_2027_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2026_, v_fvarSet_2021_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2029_; 
lean_dec(v___x_2026_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2024_);
v___x_2029_ = v___x_2010_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_fst_2007_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2024_);
v___x_2029_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2031_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2029_);
v___x_2031_ = v___x_2005_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_fst_2003_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v_a_1997_ = v___x_2031_;
goto _start;
}
}
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_FVarId_getDecl___redArg(v___x_2026_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l_Lean_LocalDecl_type(v_a_2036_);
v___x_2038_ = l_Lean_collectFVars(v_fst_2003_, v___x_2037_);
v___x_2039_ = l_Lean_LocalDecl_value(v_a_2036_, v___x_2013_);
lean_dec(v_a_2036_);
v___x_2040_ = l_Lean_collectFVars(v___x_2038_, v___x_2039_);
lean_inc(v___x_2025_);
v___x_2041_ = lean_array_push(v_fst_2007_, v___x_2025_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2024_);
lean_ctor_set(v___x_2010_, 0, v___x_2041_);
v___x_2043_ = v___x_2010_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2024_);
v___x_2043_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2043_);
lean_ctor_set(v___x_2005_, 0, v___x_2040_);
v___x_2045_ = v___x_2005_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v_a_1997_ = v___x_2045_;
goto _start;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_2024_);
lean_del_object(v___x_2010_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_2005_);
lean_dec(v_fst_2003_);
v_a_2049_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2035_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2035_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2059_, lean_object* v_a_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2059_, v_a_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec_ref(v_xs_2059_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2066_, lean_object* v_e_2067_, lean_object* v_xs_2068_, lean_object* v_body_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_s_2078_; lean_object* v_i_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2075_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2076_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2066_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
lean_inc_ref(v_body_2069_);
v_s_2078_ = l_Lean_collectFVars(v___x_2077_, v_body_2069_);
v_i_2079_ = lean_array_get_size(v_xs_2068_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2076_);
lean_ctor_set(v___x_2080_, 1, v_i_2079_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_s_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2068_, v___x_2081_, v___y_2070_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2098_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2098_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2098_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_snd_2087_; lean_object* v_fst_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_snd_2087_ = lean_ctor_get(v_a_2083_, 1);
lean_inc(v_snd_2087_);
lean_dec(v_a_2083_);
v_fst_2088_ = lean_ctor_get(v_snd_2087_, 0);
lean_inc(v_fst_2088_);
lean_dec(v_snd_2087_);
v___x_2089_ = lean_array_get_size(v_fst_2088_);
v___x_2090_ = lean_nat_dec_eq(v___x_2089_, v_i_2079_);
if (v___x_2090_ == 0)
{
uint8_t v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; 
lean_del_object(v___x_2085_);
lean_dec_ref(v_e_2067_);
v___x_2091_ = 1;
v___x_2092_ = l_Array_reverse___redArg(v_fst_2088_);
v___x_2093_ = 1;
v___x_2094_ = l_Lean_Meta_mkLetFVars(v___x_2092_, v_body_2069_, v___x_2091_, v___x_2090_, v___x_2093_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec_ref(v___x_2092_);
return v___x_2094_;
}
else
{
lean_object* v___x_2096_; 
lean_dec(v_fst_2088_);
lean_dec_ref(v_body_2069_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_e_2067_);
v___x_2096_ = v___x_2085_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_e_2067_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_body_2069_);
lean_dec_ref(v_e_2067_);
v_a_2099_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2082_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2082_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2107_, lean_object* v_e_2108_, lean_object* v_xs_2109_, lean_object* v_body_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2107_, v_e_2108_, v_xs_2109_, v_body_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v_xs_2109_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v___f_2124_; uint8_t v___x_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; 
v___x_2123_ = lean_box(1);
lean_inc_ref(v_e_2117_);
v___f_2124_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2124_, 0, v___x_2123_);
lean_closure_set(v___f_2124_, 1, v_e_2117_);
v___x_2125_ = 0;
v___x_2126_ = 1;
v___x_2127_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2117_, v___f_2124_, v___x_2125_, v___x_2126_, v___x_2125_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_zetaUnused(v_e_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2135_, lean_object* v_inst_2136_, lean_object* v_a_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2135_, v_a_2137_, v___y_2138_, v___y_2140_, v___y_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2144_, lean_object* v_inst_2145_, lean_object* v_a_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2144_, v_inst_2145_, v_a_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_xs_2144_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2157_, lean_object* v_source_2158_, lean_object* v_result_2159_, uint8_t v_keepUnused_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
uint8_t v_modified_2166_; 
v_modified_2166_ = lean_ctor_get_uint8(v_result_2159_, sizeof(void*)*5);
if (v_modified_2166_ == 0)
{
if (v_keepUnused_2160_ == 0)
{
lean_object* v_exprType_2167_; lean_object* v___x_2168_; 
v_exprType_2167_ = lean_ctor_get(v_result_2159_, 1);
lean_inc_ref(v_exprType_2167_);
lean_dec_ref(v_result_2159_);
lean_inc_ref(v_source_2158_);
v___x_2168_ = l_Lean_Meta_zetaUnused(v_source_2158_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2187_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2187_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2187_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_expr_eqv(v_a_2169_, v_source_2158_);
lean_dec_ref(v_source_2158_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_u_2157_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_mkConst(v___x_2174_, v___x_2176_);
lean_inc(v_a_2169_);
v___x_2178_ = l_Lean_mkAppB(v___x_2177_, v_exprType_2167_, v_a_2169_);
v___x_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2179_, 0, v_a_2169_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2179_);
v___x_2181_ = v___x_2171_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec(v_a_2169_);
lean_dec_ref(v_exprType_2167_);
lean_dec(v_u_2157_);
v___x_2183_ = lean_box(0);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2183_);
v___x_2185_ = v___x_2171_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_exprType_2167_);
lean_dec_ref(v_source_2158_);
lean_dec(v_u_2157_);
v_a_2188_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2168_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2168_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v_result_2159_);
lean_dec_ref(v_source_2158_);
lean_dec(v_u_2157_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
}
else
{
lean_object* v_expr_2198_; lean_object* v_exprType_2199_; lean_object* v_exprInit_2200_; lean_object* v_exprResult_2201_; lean_object* v_proof_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v_proof_2210_; 
v_expr_2198_ = lean_ctor_get(v_result_2159_, 0);
lean_inc_ref(v_expr_2198_);
v_exprType_2199_ = lean_ctor_get(v_result_2159_, 1);
lean_inc_ref_n(v_exprType_2199_, 3);
v_exprInit_2200_ = lean_ctor_get(v_result_2159_, 2);
lean_inc_ref(v_exprInit_2200_);
v_exprResult_2201_ = lean_ctor_get(v_result_2159_, 3);
lean_inc_ref_n(v_exprResult_2201_, 2);
v_proof_2202_ = lean_ctor_get(v_result_2159_, 4);
lean_inc_ref(v_proof_2202_);
lean_dec_ref(v_result_2159_);
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_u_2157_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
lean_inc_ref(v___x_2205_);
v___x_2206_ = l_Lean_mkConst(v___x_2203_, v___x_2205_);
lean_inc_ref(v___x_2206_);
v___x_2207_ = l_Lean_mkApp3(v___x_2206_, v_exprType_2199_, v_exprInit_2200_, v_expr_2198_);
v___x_2208_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2202_, v___x_2207_);
lean_inc_ref(v_source_2158_);
v___x_2209_ = l_Lean_mkApp3(v___x_2206_, v_exprType_2199_, v_source_2158_, v_exprResult_2201_);
v_proof_2210_ = l_Lean_Meta_mkExpectedPropHint(v___x_2208_, v___x_2209_);
if (v_keepUnused_2160_ == 0)
{
lean_object* v___x_2211_; 
lean_inc_ref(v_exprResult_2201_);
v___x_2211_ = l_Lean_Meta_zetaUnused(v_exprResult_2201_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2231_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2231_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2231_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_expr_eqv(v_a_2212_, v_exprResult_2201_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2205_);
v___x_2218_ = l_Lean_mkConst(v___x_2217_, v___x_2205_);
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2220_ = l_Lean_mkConst(v___x_2219_, v___x_2205_);
lean_inc_n(v_a_2212_, 2);
lean_inc_ref(v_exprType_2199_);
v___x_2221_ = l_Lean_mkAppB(v___x_2220_, v_exprType_2199_, v_a_2212_);
v___x_2222_ = l_Lean_mkApp6(v___x_2218_, v_exprType_2199_, v_source_2158_, v_exprResult_2201_, v_a_2212_, v_proof_2210_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v_a_2212_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2223_);
v___x_2225_ = v___x_2214_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_dec(v_a_2212_);
lean_dec_ref_known(v___x_2205_, 2);
lean_dec_ref(v_exprType_2199_);
lean_dec_ref(v_source_2158_);
v___x_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_exprResult_2201_);
lean_ctor_set(v___x_2227_, 1, v_proof_2210_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2227_);
v___x_2229_ = v___x_2214_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
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
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_proof_2210_);
lean_dec_ref_known(v___x_2205_, 2);
lean_dec_ref(v_exprResult_2201_);
lean_dec_ref(v_exprType_2199_);
lean_dec_ref(v_source_2158_);
v_a_2232_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2211_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2211_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec_ref_known(v___x_2205_, 2);
lean_dec_ref(v_exprType_2199_);
lean_dec_ref(v_source_2158_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_exprResult_2201_);
lean_ctor_set(v___x_2240_, 1, v_proof_2210_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2242_, lean_object* v_source_2243_, lean_object* v_result_2244_, lean_object* v_keepUnused_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
uint8_t v_keepUnused_boxed_2251_; lean_object* v_res_2252_; 
v_keepUnused_boxed_2251_ = lean_unbox(v_keepUnused_2245_);
v_res_2252_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2242_, v_source_2243_, v_result_2244_, v_keepUnused_boxed_2251_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2253_, lean_object* v_e_2254_, lean_object* v_inst_2255_, uint8_t v_zetaUnusedMode_2256_, uint8_t v___x_2257_, uint8_t v___x_2258_, lean_object* v_r_2259_){
_start:
{
uint8_t v___y_2261_; 
switch(v_zetaUnusedMode_2256_)
{
case 0:
{
v___y_2261_ = v___x_2257_;
goto v___jp_2260_;
}
case 1:
{
v___y_2261_ = v___x_2257_;
goto v___jp_2260_;
}
default: 
{
v___y_2261_ = v___x_2258_;
goto v___jp_2260_;
}
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_box(v___y_2261_);
v___x_2263_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2263_, 0, v_level_2253_);
lean_closure_set(v___x_2263_, 1, v_e_2254_);
lean_closure_set(v___x_2263_, 2, v_r_2259_);
lean_closure_set(v___x_2263_, 3, v___x_2262_);
v___x_2264_ = lean_apply_2(v_inst_2255_, lean_box(0), v___x_2263_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2265_, lean_object* v_e_2266_, lean_object* v_inst_2267_, lean_object* v_zetaUnusedMode_2268_, lean_object* v___x_2269_, lean_object* v___x_2270_, lean_object* v_r_2271_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2272_; uint8_t v___x_286__boxed_2273_; uint8_t v___x_287__boxed_2274_; lean_object* v_res_2275_; 
v_zetaUnusedMode_boxed_2272_ = lean_unbox(v_zetaUnusedMode_2268_);
v___x_286__boxed_2273_ = lean_unbox(v___x_2269_);
v___x_287__boxed_2274_ = lean_unbox(v___x_2270_);
v_res_2275_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2265_, v_e_2266_, v_inst_2267_, v_zetaUnusedMode_boxed_2272_, v___x_286__boxed_2273_, v___x_287__boxed_2274_, v_r_2271_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_info_2281_, lean_object* v_e_2282_, lean_object* v___x_2283_, lean_object* v_toBind_2284_, lean_object* v___f_2285_, lean_object* v_____x_2286_){
_start:
{
lean_object* v_fst_2287_; lean_object* v_snd_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_fst_2287_ = lean_ctor_get(v_____x_2286_, 0);
lean_inc(v_fst_2287_);
v_snd_2288_ = lean_ctor_get(v_____x_2286_, 1);
lean_inc(v_snd_2288_);
lean_dec_ref(v_____x_2286_);
v___x_2289_ = lean_mk_empty_array_with_capacity(v___x_2276_);
v___x_2290_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2277_, v_inst_2278_, v_inst_2279_, v_inst_2280_, v_info_2281_, v_fst_2287_, v_snd_2288_, v_e_2282_, v___x_2283_, v___x_2289_);
v___x_2291_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2290_, v___f_2285_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_info_2297_, lean_object* v_e_2298_, lean_object* v___x_2299_, lean_object* v_toBind_2300_, lean_object* v___f_2301_, lean_object* v_____x_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2292_, v_inst_2293_, v_inst_2294_, v_inst_2295_, v_inst_2296_, v_info_2297_, v_e_2298_, v___x_2299_, v_toBind_2300_, v___f_2301_, v_____x_2302_);
lean_dec(v___x_2292_);
return v_res_2303_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2306_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2307_ = lean_unsigned_to_nat(2u);
v___x_2308_ = lean_unsigned_to_nat(456u);
v___x_2309_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2311_ = l_mkPanicMessageWithDecl(v___x_2310_, v___x_2309_, v___x_2308_, v___x_2307_, v___x_2306_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2312_, lean_object* v_inst_2313_, uint8_t v_zetaUnusedMode_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_toBind_2318_, lean_object* v___x_2319_, lean_object* v_info_2320_){
_start:
{
lean_object* v_haveInfo_2321_; lean_object* v_level_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_haveInfo_2321_ = lean_ctor_get(v_info_2320_, 0);
v_level_2322_ = lean_ctor_get(v_info_2320_, 5);
v___x_2323_ = lean_array_get_size(v_haveInfo_2321_);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_nat_dec_eq(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___f_2331_; uint8_t v___y_2333_; 
v___x_2326_ = 1;
v___x_2327_ = lean_box(v_zetaUnusedMode_2314_);
v___x_2328_ = lean_box(v___x_2326_);
v___x_2329_ = lean_box(v___x_2325_);
lean_inc_n(v_inst_2313_, 2);
lean_inc_ref(v_e_2312_);
lean_inc(v_level_2322_);
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2330_, 0, v_level_2322_);
lean_closure_set(v___f_2330_, 1, v_e_2312_);
lean_closure_set(v___f_2330_, 2, v_inst_2313_);
lean_closure_set(v___f_2330_, 3, v___x_2327_);
lean_closure_set(v___f_2330_, 4, v___x_2328_);
lean_closure_set(v___f_2330_, 5, v___x_2329_);
lean_inc(v_toBind_2318_);
lean_inc_ref(v_info_2320_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2331_, 0, v___x_2323_);
lean_closure_set(v___f_2331_, 1, v_inst_2315_);
lean_closure_set(v___f_2331_, 2, v_inst_2313_);
lean_closure_set(v___f_2331_, 3, v_inst_2316_);
lean_closure_set(v___f_2331_, 4, v_inst_2317_);
lean_closure_set(v___f_2331_, 5, v_info_2320_);
lean_closure_set(v___f_2331_, 6, v_e_2312_);
lean_closure_set(v___f_2331_, 7, v___x_2324_);
lean_closure_set(v___f_2331_, 8, v_toBind_2318_);
lean_closure_set(v___f_2331_, 9, v___f_2330_);
switch(v_zetaUnusedMode_2314_)
{
case 0:
{
v___y_2333_ = v___x_2326_;
goto v___jp_2332_;
}
case 2:
{
v___y_2333_ = v___x_2326_;
goto v___jp_2332_;
}
default: 
{
v___y_2333_ = v___x_2325_;
goto v___jp_2332_;
}
}
v___jp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = lean_box(v___y_2333_);
v___x_2335_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2335_, 0, v_info_2320_);
lean_closure_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_apply_2(v_inst_2313_, lean_box(0), v___x_2335_);
v___x_2337_ = lean_apply_4(v_toBind_2318_, lean_box(0), lean_box(0), v___x_2336_, v___f_2331_);
return v___x_2337_;
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v_info_2320_);
lean_dec(v_toBind_2318_);
lean_dec_ref(v_inst_2317_);
lean_dec_ref(v_inst_2316_);
lean_dec_ref(v_inst_2315_);
lean_dec(v_inst_2313_);
lean_dec_ref(v_e_2312_);
v___x_2338_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2339_ = l_panic___redArg(v___x_2319_, v___x_2338_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2340_, lean_object* v_inst_2341_, lean_object* v_zetaUnusedMode_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_toBind_2346_, lean_object* v___x_2347_, lean_object* v_info_2348_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2349_; lean_object* v_res_2350_; 
v_zetaUnusedMode_boxed_2349_ = lean_unbox(v_zetaUnusedMode_2342_);
v_res_2350_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2340_, v_inst_2341_, v_zetaUnusedMode_boxed_2349_, v_inst_2343_, v_inst_2344_, v_inst_2345_, v_toBind_2346_, v___x_2347_, v_info_2348_);
lean_dec(v___x_2347_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_e_2355_, uint8_t v_zetaUnusedMode_2356_){
_start:
{
lean_object* v_toBind_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; 
v_toBind_2357_ = lean_ctor_get(v_inst_2351_, 1);
lean_inc_n(v_toBind_2357_, 2);
v___x_2358_ = lean_box(0);
lean_inc_ref(v_e_2355_);
v___x_2359_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2359_, 0, v_e_2355_);
lean_inc(v_inst_2352_);
v___x_2360_ = lean_apply_2(v_inst_2352_, lean_box(0), v___x_2359_);
lean_inc_ref(v_inst_2351_);
v___x_2361_ = l_instInhabitedOfMonad___redArg(v_inst_2351_, v___x_2358_);
v___x_2362_ = lean_box(v_zetaUnusedMode_2356_);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2363_, 0, v_e_2355_);
lean_closure_set(v___f_2363_, 1, v_inst_2352_);
lean_closure_set(v___f_2363_, 2, v___x_2362_);
lean_closure_set(v___f_2363_, 3, v_inst_2351_);
lean_closure_set(v___f_2363_, 4, v_inst_2353_);
lean_closure_set(v___f_2363_, 5, v_inst_2354_);
lean_closure_set(v___f_2363_, 6, v_toBind_2357_);
lean_closure_set(v___f_2363_, 7, v___x_2361_);
v___x_2364_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2360_, v___f_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_e_2369_, lean_object* v_zetaUnusedMode_2370_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2371_; lean_object* v_res_2372_; 
v_zetaUnusedMode_boxed_2371_ = lean_unbox(v_zetaUnusedMode_2370_);
v_res_2372_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2365_, v_inst_2366_, v_inst_2367_, v_inst_2368_, v_e_2369_, v_zetaUnusedMode_boxed_2371_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2373_, lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_e_2378_, uint8_t v_zetaUnusedMode_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2374_, v_inst_2375_, v_inst_2376_, v_inst_2377_, v_e_2378_, v_zetaUnusedMode_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_e_2386_, lean_object* v_zetaUnusedMode_2387_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2388_; lean_object* v_res_2389_; 
v_zetaUnusedMode_boxed_2388_ = lean_unbox(v_zetaUnusedMode_2387_);
v_res_2389_ = l_Lean_Meta_simpHaveTelescope(v_m_2381_, v_inst_2382_, v_inst_2383_, v_inst_2384_, v_inst_2385_, v_e_2386_, v_zetaUnusedMode_boxed_2388_);
return v_res_2389_;
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
