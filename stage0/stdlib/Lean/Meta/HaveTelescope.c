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
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
static const lean_array_object l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0));
v___x_266_ = lean_box(1);
v___x_267_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_266_, v___x_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_268_, lean_object* v_fvars_269_, lean_object* v_info_270_, lean_object* v_bodyDeps_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; 
lean_inc(v___y_275_);
lean_inc_ref(v___y_274_);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc_ref(v_body_268_);
v___x_277_ = lean_infer_type(v_body_268_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_279_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_n(v_a_278_, 2);
lean_dec_ref_known(v___x_277_, 1);
v___x_279_ = l_Lean_Meta_getLevel(v_a_278_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_306_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_306_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_306_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_306_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_fvarSet_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_haveInfo_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v___x_284_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
lean_inc(v_a_278_);
v___x_285_ = l_Lean_collectFVars(v___x_284_, v_a_278_);
v_fvarSet_286_ = lean_ctor_get(v___x_285_, 1);
lean_inc(v_fvarSet_286_);
lean_dec_ref(v___x_285_);
v___x_287_ = lean_array_get_size(v_fvars_269_);
v___x_288_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveInfo_default___closed__1, &l_Lean_Meta_instInhabitedHaveInfo_default___closed__1_once, _init_l_Lean_Meta_instInhabitedHaveInfo_default___closed__1);
v___x_289_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_269_, v_fvarSet_286_, v___x_287_, v___x_287_, v___x_288_);
lean_dec(v_fvarSet_286_);
v_haveInfo_290_ = lean_ctor_get(v_info_270_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_info_270_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_301_ = lean_ctor_get(v_info_270_, 5);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_info_270_, 4);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_info_270_, 3);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_info_270_, 2);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_info_270_, 1);
lean_dec(v_unused_305_);
v___x_292_ = v_info_270_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_haveInfo_290_);
lean_dec(v_info_270_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 5, v_a_280_);
lean_ctor_set(v___x_292_, 4, v_a_278_);
lean_ctor_set(v___x_292_, 3, v_body_268_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
lean_ctor_set(v___x_292_, 1, v_bodyDeps_271_);
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_haveInfo_290_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_bodyDeps_271_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_body_268_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_a_278_);
lean_ctor_set(v_reuseFailAlloc_299_, 5, v_a_280_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_295_);
v___x_297_ = v___x_282_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v_a_278_);
lean_dec_ref(v_bodyDeps_271_);
lean_dec_ref(v_info_270_);
lean_dec_ref(v_body_268_);
v_a_307_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_279_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_279_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_bodyDeps_271_);
lean_dec_ref(v_info_270_);
lean_dec_ref(v_body_268_);
v_a_315_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_277_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_277_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_323_, lean_object* v_fvars_324_, lean_object* v_info_325_, lean_object* v_bodyDeps_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_323_, v_fvars_324_, v_info_325_, v_bodyDeps_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec_ref(v_fvars_324_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; lean_object* v_ngen_336_; lean_object* v_namePrefix_337_; lean_object* v_idx_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_368_; 
v___x_335_ = lean_st_ref_get(v___y_333_);
v_ngen_336_ = lean_ctor_get(v___x_335_, 2);
lean_inc_ref(v_ngen_336_);
lean_dec(v___x_335_);
v_namePrefix_337_ = lean_ctor_get(v_ngen_336_, 0);
v_idx_338_ = lean_ctor_get(v_ngen_336_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_ngen_336_);
if (v_isSharedCheck_368_ == 0)
{
v___x_340_ = v_ngen_336_;
v_isShared_341_ = v_isSharedCheck_368_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_idx_338_);
lean_inc(v_namePrefix_337_);
lean_dec(v_ngen_336_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_368_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_r_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
lean_inc(v_idx_338_);
lean_inc(v_namePrefix_337_);
v_r_342_ = l_Lean_Name_num___override(v_namePrefix_337_, v_idx_338_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_idx_338_, v___x_343_);
lean_dec(v_idx_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_namePrefix_337_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_367_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_auxDeclNGen_350_; lean_object* v_traceState_351_; lean_object* v_cache_352_; lean_object* v_recordedDeps_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
v___x_347_ = lean_st_ref_take(v___y_333_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_347_, 1);
v_auxDeclNGen_350_ = lean_ctor_get(v___x_347_, 3);
v_traceState_351_ = lean_ctor_get(v___x_347_, 4);
v_cache_352_ = lean_ctor_get(v___x_347_, 5);
v_recordedDeps_353_ = lean_ctor_get(v___x_347_, 6);
v_messages_354_ = lean_ctor_get(v___x_347_, 7);
v_infoState_355_ = lean_ctor_get(v___x_347_, 8);
v_snapshotTasks_356_ = lean_ctor_get(v___x_347_, 9);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_347_, 2);
lean_dec(v_unused_366_);
v___x_358_ = v___x_347_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_recordedDeps_353_);
lean_inc(v_cache_352_);
lean_inc(v_traceState_351_);
lean_inc(v_auxDeclNGen_350_);
lean_inc(v_nextMacroScope_349_);
lean_inc(v_env_348_);
lean_dec(v___x_347_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 2, v___x_346_);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_env_348_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_auxDeclNGen_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_traceState_351_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v_cache_352_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_recordedDeps_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 9, v_snapshotTasks_356_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_st_ref_put(v___y_333_, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_r_342_);
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg___boxed(lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_369_);
lean_dec(v___y_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v___x_377_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_375_);
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_392_, lean_object* v_numHaves_393_, lean_object* v_info_394_, lean_object* v_lctx_395_, lean_object* v_fvars_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; 
if (lean_obj_tag(v_e_392_) == 8)
{
uint8_t v_nondep_411_; 
v_nondep_411_ = lean_ctor_get_uint8(v_e_392_, sizeof(void*)*4 + 8);
if (v_nondep_411_ == 1)
{
lean_object* v_declName_412_; lean_object* v_type_413_; lean_object* v_value_414_; lean_object* v_body_415_; lean_object* v_typeBackDeps_416_; lean_object* v_valueBackDeps_417_; lean_object* v_t_418_; lean_object* v_v_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_declName_412_ = lean_ctor_get(v_e_392_, 0);
lean_inc(v_declName_412_);
v_type_413_ = lean_ctor_get(v_e_392_, 1);
lean_inc_ref_n(v_type_413_, 2);
v_value_414_ = lean_ctor_get(v_e_392_, 2);
lean_inc_ref_n(v_value_414_, 2);
v_body_415_ = lean_ctor_get(v_e_392_, 3);
lean_inc_ref(v_body_415_);
lean_dec_ref_known(v_e_392_, 4);
v_typeBackDeps_416_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_393_, v_type_413_);
v_valueBackDeps_417_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_393_, v_value_414_);
v_t_418_ = lean_expr_instantiate_rev(v_type_413_, v_fvars_396_);
lean_dec_ref(v_type_413_);
v_v_419_ = lean_expr_instantiate_rev(v_value_414_, v_fvars_396_);
lean_dec_ref(v_value_414_);
lean_inc_ref(v_t_418_);
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_420_, 0, v_t_418_);
lean_inc_ref(v_lctx_395_);
v___x_421_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_395_, v___x_420_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_haveInfo_425_; lean_object* v_bodyDeps_426_; lean_object* v_bodyTypeDeps_427_; lean_object* v_body_428_; lean_object* v_bodyType_429_; lean_object* v_level_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_448_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v_haveInfo_425_ = lean_ctor_get(v_info_394_, 0);
v_bodyDeps_426_ = lean_ctor_get(v_info_394_, 1);
v_bodyTypeDeps_427_ = lean_ctor_get(v_info_394_, 2);
v_body_428_ = lean_ctor_get(v_info_394_, 3);
v_bodyType_429_ = lean_ctor_get(v_info_394_, 4);
v_level_430_ = lean_ctor_get(v_info_394_, 5);
v_isSharedCheck_448_ = !lean_is_exclusive(v_info_394_);
if (v_isSharedCheck_448_ == 0)
{
v___x_432_ = v_info_394_;
v_isShared_433_ = v_isSharedCheck_448_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_level_430_);
lean_inc(v_bodyType_429_);
lean_inc(v_body_428_);
lean_inc(v_bodyTypeDeps_427_);
lean_inc(v_bodyDeps_426_);
lean_inc(v_haveInfo_425_);
lean_dec(v_info_394_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_448_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = 0;
lean_inc(v_a_424_);
v___x_436_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v_a_424_);
lean_ctor_set(v___x_436_, 2, v_declName_412_);
lean_ctor_set(v___x_436_, 3, v_t_418_);
lean_ctor_set(v___x_436_, 4, v_v_419_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*5, v_nondep_411_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*5 + 1, v___x_435_);
lean_inc_ref(v___x_436_);
v___x_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_437_, 0, v_typeBackDeps_416_);
lean_ctor_set(v___x_437_, 1, v_valueBackDeps_417_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
lean_ctor_set(v___x_437_, 3, v_a_422_);
v___x_438_ = lean_array_push(v_haveInfo_425_, v___x_437_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_438_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_bodyDeps_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_bodyTypeDeps_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_body_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_bodyType_429_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v_level_430_);
v___x_440_ = v_reuseFailAlloc_447_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = l_Lean_LocalContext_addDecl(v_lctx_395_, v___x_436_);
v___x_442_ = l_Lean_mkFVar(v_a_424_);
v___x_443_ = lean_array_push(v_fvars_396_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_numHaves_393_, v___x_444_);
lean_dec(v_numHaves_393_);
v_e_392_ = v_body_415_;
v_numHaves_393_ = v___x_445_;
v_info_394_ = v___x_440_;
v_lctx_395_ = v___x_441_;
v_fvars_396_ = v___x_443_;
goto _start;
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_a_422_);
lean_dec_ref(v_v_419_);
lean_dec_ref(v_t_418_);
lean_dec_ref(v_valueBackDeps_417_);
lean_dec_ref(v_typeBackDeps_416_);
lean_dec_ref(v_body_415_);
lean_dec(v_declName_412_);
lean_dec_ref(v_fvars_396_);
lean_dec_ref(v_lctx_395_);
lean_dec_ref(v_info_394_);
lean_dec(v_numHaves_393_);
v_a_449_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_423_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_423_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_v_419_);
lean_dec_ref(v_t_418_);
lean_dec_ref(v_valueBackDeps_417_);
lean_dec_ref(v_typeBackDeps_416_);
lean_dec_ref(v_body_415_);
lean_dec(v_declName_412_);
lean_dec_ref(v_fvars_396_);
lean_dec_ref(v_lctx_395_);
lean_dec_ref(v_info_394_);
lean_dec(v_numHaves_393_);
v_a_457_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_421_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_421_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
v___y_403_ = v_a_397_;
v___y_404_ = v_a_398_;
v___y_405_ = v_a_399_;
v___y_406_ = v_a_400_;
goto v___jp_402_;
}
}
else
{
v___y_403_ = v_a_397_;
v___y_404_ = v_a_398_;
v___y_405_ = v_a_399_;
v___y_406_ = v_a_400_;
goto v___jp_402_;
}
v___jp_402_:
{
lean_object* v_bodyDeps_407_; lean_object* v_body_408_; lean_object* v___f_409_; lean_object* v___x_410_; 
lean_inc_ref(v_e_392_);
v_bodyDeps_407_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_393_, v_e_392_);
lean_dec(v_numHaves_393_);
v_body_408_ = lean_expr_instantiate_rev(v_e_392_, v_fvars_396_);
lean_dec_ref(v_e_392_);
v___f_409_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 9, 4);
lean_closure_set(v___f_409_, 0, v_body_408_);
lean_closure_set(v___f_409_, 1, v_fvars_396_);
lean_closure_set(v___f_409_, 2, v_info_394_);
lean_closure_set(v___f_409_, 3, v_bodyDeps_407_);
v___x_410_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_395_, v___f_409_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_465_, lean_object* v_numHaves_466_, lean_object* v_info_467_, lean_object* v_lctx_468_, lean_object* v_fvars_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_465_, v_numHaves_466_, v_info_467_, v_lctx_468_, v_fvars_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_476_, lean_object* v_m_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_477_, v_a_478_, v_b_479_);
return v___x_480_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_481_, lean_object* v_k_482_, lean_object* v_t_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_482_, v_t_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_485_, lean_object* v_k_486_, lean_object* v_t_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_485_, v_k_486_, v_t_487_);
lean_dec(v_t_487_);
lean_dec(v_k_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_490_, lean_object* v___x_491_, lean_object* v_n_492_, lean_object* v_j_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_490_, v___x_491_, v_n_492_, v_j_493_, v_a_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_497_, lean_object* v___x_498_, lean_object* v_n_499_, lean_object* v_j_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_497_, v___x_498_, v_n_499_, v_j_500_, v_a_501_, v_a_502_);
lean_dec(v_n_499_);
lean_dec(v___x_498_);
lean_dec_ref(v_fvars_497_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_515_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_516_, lean_object* v_a_517_, lean_object* v_x_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_520_, v_a_521_, v_x_522_);
lean_dec(v_x_522_);
lean_dec(v_a_521_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_525_, lean_object* v_data_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_528_, lean_object* v_i_529_, lean_object* v_source_530_, lean_object* v_target_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_529_, v_source_530_, v_target_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_lctx_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_lctx_543_ = lean_ctor_get(v_a_538_, 2);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_546_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_543_);
v___x_547_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_537_, v___x_544_, v___x_546_, v_lctx_543_, v___x_545_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
if (lean_obj_tag(v_x_556_) == 0)
{
return v_x_555_;
}
else
{
lean_object* v_key_557_; lean_object* v_tail_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_key_557_ = lean_ctor_get(v_x_556_, 0);
v_tail_558_ = lean_ctor_get(v_x_556_, 2);
v___x_559_ = 1;
v___x_560_ = lean_box(v___x_559_);
v___x_561_ = lean_array_set(v_x_555_, v_key_557_, v___x_560_);
v_x_555_ = v___x_561_;
v_x_556_ = v_tail_558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_563_, v_x_564_);
lean_dec(v_x_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_, lean_object* v_b_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; size_t v___x_573_; size_t v___x_574_; 
v___x_571_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v___x_572_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_569_, v___x_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_567_, v___x_573_);
v_i_567_ = v___x_574_;
v_b_569_ = v___x_572_;
goto _start;
}
else
{
return v_b_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_576_, lean_object* v_i_577_, lean_object* v_stop_578_, lean_object* v_b_579_){
_start:
{
size_t v_i_boxed_580_; size_t v_stop_boxed_581_; lean_object* v_res_582_; 
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_stop_boxed_581_ = lean_unbox_usize(v_stop_578_);
lean_dec(v_stop_578_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_576_, v_i_boxed_580_, v_stop_boxed_581_, v_b_579_);
lean_dec_ref(v_as_576_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_583_, lean_object* v_s_584_){
_start:
{
lean_object* v_buckets_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_buckets_585_ = lean_ctor_get(v_s_584_, 1);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_get_size(v_buckets_585_);
v___x_588_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
return v_arr_583_;
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_587_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_585_, v___x_589_, v___x_590_, v_arr_583_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_592_, lean_object* v_s_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_592_, v_s_593_);
lean_dec_ref(v_s_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_595_, lean_object* v_numHaves_596_, lean_object* v___x_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v_a_602_; uint8_t v___x_606_; 
v___x_606_ = lean_nat_dec_lt(v_a_598_, v_upperBound_595_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_dec(v_a_598_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_b_599_);
return v___x_607_;
}
else
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_608_ = 0;
v___x_609_ = lean_nat_sub(v_numHaves_596_, v_a_598_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_sub(v___x_609_, v___x_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(v___x_608_);
v___x_613_ = lean_array_get(v___x_612_, v_b_599_, v___x_611_);
lean_dec(v___x_612_);
v___x_614_ = lean_unbox(v___x_613_);
lean_dec(v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v___x_611_);
v_a_602_ = v_b_599_;
goto v___jp_601_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_typeBackDeps_617_; lean_object* v_valueBackDeps_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_616_ = lean_array_get_borrowed(v___x_615_, v___x_597_, v___x_611_);
lean_dec(v___x_611_);
v_typeBackDeps_617_ = lean_ctor_get(v___x_616_, 0);
v_valueBackDeps_618_ = lean_ctor_get(v___x_616_, 1);
v___x_619_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_599_, v_typeBackDeps_617_);
v___x_620_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_619_, v_valueBackDeps_618_);
v_a_602_ = v___x_620_;
goto v___jp_601_;
}
}
v___jp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_a_598_, v___x_603_);
lean_dec(v_a_598_);
v_a_598_ = v___x_604_;
v_b_599_ = v_a_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_621_, lean_object* v_numHaves_622_, lean_object* v___x_623_, lean_object* v_a_624_, lean_object* v_b_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_621_, v_numHaves_622_, v___x_623_, v_a_624_, v_b_625_);
lean_dec_ref(v___x_623_);
lean_dec(v_numHaves_622_);
lean_dec(v_upperBound_621_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_628_, lean_object* v_init_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_haveInfo_635_; lean_object* v_numHaves_636_; uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v_used_639_; lean_object* v___x_640_; lean_object* v_used_641_; lean_object* v___x_642_; 
v_haveInfo_635_ = lean_ctor_get(v_info_628_, 0);
v_numHaves_636_ = lean_array_get_size(v_haveInfo_635_);
v___x_637_ = 0;
v___x_638_ = lean_box(v___x_637_);
v_used_639_ = lean_mk_array(v_numHaves_636_, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(0u);
v_used_641_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_639_, v_init_629_);
v___x_642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_636_, v_numHaves_636_, v_haveInfo_635_, v___x_640_, v_used_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_643_, lean_object* v_init_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_643_, v_init_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_init_644_);
lean_dec_ref(v_info_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_651_, lean_object* v_numHaves_652_, lean_object* v___x_653_, lean_object* v_inst_654_, lean_object* v_R_655_, lean_object* v_a_656_, lean_object* v_b_657_, lean_object* v_c_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_651_, v_numHaves_652_, v___x_653_, v_a_656_, v_b_657_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_665_, lean_object* v_numHaves_666_, lean_object* v___x_667_, lean_object* v_inst_668_, lean_object* v_R_669_, lean_object* v_a_670_, lean_object* v_b_671_, lean_object* v_c_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_665_, v_numHaves_666_, v___x_667_, v_inst_668_, v_R_669_, v_a_670_, v_b_671_, v_c_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v___x_667_);
lean_dec(v_numHaves_666_);
lean_dec(v_upperBound_665_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_681_, uint8_t v_keepUnused_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_bodyDeps_688_; lean_object* v_bodyTypeDeps_689_; lean_object* v___x_690_; 
v_bodyDeps_688_ = lean_ctor_get(v_info_681_, 1);
v_bodyTypeDeps_689_ = lean_ctor_get(v_info_681_, 2);
v___x_690_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_681_, v_bodyTypeDeps_689_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_690_) == 0)
{
if (v_keepUnused_682_ == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_681_, v_bodyDeps_688_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_691_);
lean_ctor_set(v___x_697_, 1, v_a_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_a_691_);
v_a_702_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_692_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_692_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v_a_710_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v___x_690_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_690_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_a_710_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v_a_720_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_690_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_690_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_728_, lean_object* v_keepUnused_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
uint8_t v_keepUnused_boxed_735_; lean_object* v_res_736_; 
v_keepUnused_boxed_735_ = lean_unbox(v_keepUnused_729_);
v_res_736_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_728_, v_keepUnused_boxed_735_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec_ref(v_info_728_);
return v_res_736_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_box(0);
v___x_741_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_742_ = l_Lean_Expr_const___override(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = 0;
v___x_744_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_745_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_ctor_set(v___x_745_, 2, v___x_744_);
lean_ctor_set(v___x_745_, 3, v___x_744_);
lean_ctor_set(v___x_745_, 4, v___x_744_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*5, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_746_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_level_764_, lean_object* v_exprType_765_, lean_object* v_e_766_, uint8_t v___x_767_, lean_object* v_toPure_768_, lean_object* v_xs_769_, lean_object* v_____do__lift_770_){
_start:
{
if (lean_obj_tag(v_____do__lift_770_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_proof_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_772_ = lean_box(0);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v_level_764_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_mkConst(v___x_771_, v___x_773_);
lean_inc_ref_n(v_e_766_, 3);
lean_inc_ref(v_exprType_765_);
v_proof_775_ = l_Lean_mkAppB(v___x_774_, v_exprType_765_, v_e_766_);
v___x_776_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_776_, 0, v_e_766_);
lean_ctor_set(v___x_776_, 1, v_exprType_765_);
lean_ctor_set(v___x_776_, 2, v_e_766_);
lean_ctor_set(v___x_776_, 3, v_e_766_);
lean_ctor_set(v___x_776_, 4, v_proof_775_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*5, v___x_767_);
v___x_777_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_776_);
return v___x_777_;
}
else
{
lean_object* v_e_778_; lean_object* v_h_779_; lean_object* v_expr_780_; lean_object* v_proof_781_; lean_object* v___x_786_; uint8_t v___x_787_; 
lean_dec(v_level_764_);
v_e_778_ = lean_ctor_get(v_____do__lift_770_, 0);
v_h_779_ = lean_ctor_get(v_____do__lift_770_, 1);
v_expr_780_ = lean_expr_abstract(v_e_778_, v_xs_769_);
v_proof_781_ = lean_expr_abstract(v_h_779_, v_xs_769_);
v___x_786_ = l_Lean_Expr_cleanupAnnotations(v_proof_781_);
v___x_787_ = l_Lean_Expr_isApp(v___x_786_);
if (v___x_787_ == 0)
{
lean_dec_ref(v___x_786_);
goto v___jp_782_;
}
else
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_786_);
v___x_789_ = l_Lean_Expr_isApp(v___x_788_);
if (v___x_789_ == 0)
{
lean_dec_ref(v___x_788_);
lean_dec_ref(v___x_786_);
goto v___jp_782_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = l_Lean_Expr_appFnCleanup___redArg(v___x_788_);
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_792_ = l_Lean_Expr_isConstOf(v___x_790_, v___x_791_);
lean_dec_ref(v___x_790_);
if (v___x_792_ == 0)
{
lean_dec_ref(v___x_788_);
lean_dec_ref(v___x_786_);
goto v___jp_782_;
}
else
{
lean_object* v_arg_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_arg_793_ = lean_ctor_get(v___x_788_, 1);
lean_inc_ref(v_arg_793_);
lean_dec_ref(v___x_788_);
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_795_ = lean_unsigned_to_nat(3u);
v___x_796_ = l_Lean_Expr_isAppOfArity(v_arg_793_, v___x_794_, v___x_795_);
lean_dec_ref(v_arg_793_);
if (v___x_796_ == 0)
{
lean_dec_ref(v___x_786_);
goto v___jp_782_;
}
else
{
lean_object* v_arg_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_arg_797_ = lean_ctor_get(v___x_786_, 1);
lean_inc_ref(v_arg_797_);
lean_dec_ref(v___x_786_);
v___x_798_ = l_Lean_Expr_cleanupAnnotations(v_arg_797_);
lean_dec_ref(v_arg_797_);
v___x_799_ = l_Lean_Expr_isApp(v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_798_);
v___x_801_ = l_Lean_Expr_isApp(v___x_800_);
if (v___x_801_ == 0)
{
lean_dec_ref(v___x_800_);
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_800_);
v___x_803_ = l_Lean_Expr_isConstOf(v___x_802_, v___x_791_);
lean_dec_ref(v___x_802_);
if (v___x_803_ == 0)
{
lean_dec_ref(v___x_800_);
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v_arg_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_arg_804_ = lean_ctor_get(v___x_800_, 1);
lean_inc_ref(v_arg_804_);
lean_dec_ref(v___x_800_);
v___x_805_ = l_Lean_Expr_cleanupAnnotations(v_arg_804_);
lean_dec_ref(v_arg_804_);
v___x_806_ = l_Lean_Expr_isApp(v___x_805_);
if (v___x_806_ == 0)
{
lean_dec_ref(v___x_805_);
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_805_);
v___x_808_ = l_Lean_Expr_isApp(v___x_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v___x_805_);
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_807_);
v___x_810_ = l_Lean_Expr_isApp(v___x_809_);
if (v___x_810_ == 0)
{
lean_dec_ref(v___x_809_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v___x_805_);
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_809_);
lean_dec_ref(v___x_809_);
v___x_812_ = l_Lean_Expr_isConstOf(v___x_811_, v___x_794_);
lean_dec_ref(v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v___x_805_);
lean_dec_ref(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v_arg_813_; lean_object* v___x_814_; 
v_arg_813_ = lean_ctor_get(v___x_798_, 1);
lean_inc_ref(v_arg_813_);
lean_dec_ref(v___x_798_);
v___x_814_ = l_Lean_Expr_getAppFn(v_arg_813_);
if (lean_obj_tag(v___x_814_) == 4)
{
lean_object* v_declName_815_; 
v_declName_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_declName_815_);
lean_dec_ref_known(v___x_814_, 2);
if (lean_obj_tag(v_declName_815_) == 1)
{
lean_object* v_pre_816_; 
v_pre_816_ = lean_ctor_get(v_declName_815_, 0);
if (lean_obj_tag(v_pre_816_) == 0)
{
lean_object* v_str_817_; lean_object* v_arg_818_; lean_object* v_arg_819_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_str_817_ = lean_ctor_get(v_declName_815_, 1);
lean_inc_ref(v_str_817_);
lean_dec_ref_known(v_declName_815_, 2);
v_arg_818_ = lean_ctor_get(v___x_805_, 1);
lean_inc_ref(v_arg_818_);
lean_dec_ref(v___x_805_);
v_arg_819_ = lean_ctor_get(v___x_807_, 1);
lean_inc_ref(v_arg_819_);
lean_dec_ref(v___x_807_);
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_824_ = lean_string_dec_eq(v_str_817_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_826_ = lean_string_dec_eq(v_str_817_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_828_ = lean_string_dec_eq(v_str_817_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_830_ = lean_string_dec_eq(v_str_817_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_832_ = lean_string_dec_eq(v_str_817_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_834_ = lean_string_dec_eq(v_str_817_, v___x_833_);
lean_dec_ref(v_str_817_);
if (v___x_834_ == 0)
{
lean_dec_ref(v_arg_819_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_813_);
goto v___jp_782_;
}
else
{
lean_dec_ref(v_proof_781_);
lean_dec_ref(v_e_766_);
goto v___jp_820_;
}
}
else
{
lean_dec_ref(v_str_817_);
lean_dec_ref(v_proof_781_);
lean_dec_ref(v_e_766_);
goto v___jp_820_;
}
}
else
{
lean_dec_ref(v_str_817_);
lean_dec_ref(v_proof_781_);
lean_dec_ref(v_e_766_);
goto v___jp_820_;
}
}
else
{
lean_dec_ref(v_str_817_);
lean_dec_ref(v_proof_781_);
lean_dec_ref(v_e_766_);
goto v___jp_820_;
}
}
else
{
lean_dec_ref(v_str_817_);
lean_dec_ref(v_proof_781_);
lean_dec_ref(v_e_766_);
goto v___jp_820_;
}
}
else
{
lean_dec_ref(v_str_817_);
lean_dec_ref(v_proof_781_);
lean_dec_ref(v_e_766_);
goto v___jp_820_;
}
v___jp_820_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_821_, 0, v_arg_818_);
lean_ctor_set(v___x_821_, 1, v_exprType_765_);
lean_ctor_set(v___x_821_, 2, v_arg_819_);
lean_ctor_set(v___x_821_, 3, v_expr_780_);
lean_ctor_set(v___x_821_, 4, v_arg_813_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*5, v___x_792_);
v___x_822_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_821_);
return v___x_822_;
}
}
else
{
lean_dec_ref_known(v_declName_815_, 2);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v___x_805_);
goto v___jp_782_;
}
}
else
{
lean_dec(v_declName_815_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v___x_805_);
goto v___jp_782_;
}
}
else
{
lean_dec_ref(v___x_814_);
lean_dec_ref(v_arg_813_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v___x_805_);
goto v___jp_782_;
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
v___jp_782_:
{
uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = 1;
lean_inc_ref(v_expr_780_);
v___x_784_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_784_, 0, v_expr_780_);
lean_ctor_set(v___x_784_, 1, v_exprType_765_);
lean_ctor_set(v___x_784_, 2, v_e_766_);
lean_ctor_set(v___x_784_, 3, v_expr_780_);
lean_ctor_set(v___x_784_, 4, v_proof_781_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*5, v___x_783_);
v___x_785_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_784_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_level_835_, lean_object* v_exprType_836_, lean_object* v_e_837_, lean_object* v___x_838_, lean_object* v_toPure_839_, lean_object* v_xs_840_, lean_object* v_____do__lift_841_){
_start:
{
uint8_t v___x_7855__boxed_842_; lean_object* v_res_843_; 
v___x_7855__boxed_842_ = lean_unbox(v___x_838_);
v_res_843_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_level_835_, v_exprType_836_, v_e_837_, v___x_7855__boxed_842_, v_toPure_839_, v_xs_840_, v_____do__lift_841_);
lean_dec(v_____do__lift_841_);
lean_dec_ref(v_xs_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_844_, lean_object* v_bodyType_845_, lean_object* v_xs_846_, lean_object* v_level_847_, lean_object* v_e_848_, uint8_t v___x_849_, lean_object* v_toPure_850_, lean_object* v_body_851_, lean_object* v_toBind_852_, lean_object* v_____r_853_){
_start:
{
lean_object* v_simp_854_; lean_object* v_exprType_855_; lean_object* v___x_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_simp_854_ = lean_ctor_get(v_inst_844_, 2);
lean_inc(v_simp_854_);
lean_dec_ref(v_inst_844_);
v_exprType_855_ = lean_expr_abstract(v_bodyType_845_, v_xs_846_);
v___x_856_ = lean_box(v___x_849_);
v___f_857_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_857_, 0, v_level_847_);
lean_closure_set(v___f_857_, 1, v_exprType_855_);
lean_closure_set(v___f_857_, 2, v_e_848_);
lean_closure_set(v___f_857_, 3, v___x_856_);
lean_closure_set(v___f_857_, 4, v_toPure_850_);
lean_closure_set(v___f_857_, 5, v_xs_846_);
v___x_858_ = lean_apply_1(v_simp_854_, v_body_851_);
v___x_859_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v___x_858_, v___f_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_860_, lean_object* v_bodyType_861_, lean_object* v_xs_862_, lean_object* v_level_863_, lean_object* v_e_864_, lean_object* v___x_865_, lean_object* v_toPure_866_, lean_object* v_body_867_, lean_object* v_toBind_868_, lean_object* v_____r_869_){
_start:
{
uint8_t v___x_8005__boxed_870_; lean_object* v_res_871_; 
v___x_8005__boxed_870_ = lean_unbox(v___x_865_);
v_res_871_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_860_, v_bodyType_861_, v_xs_862_, v_level_863_, v_e_864_, v___x_8005__boxed_870_, v_toPure_866_, v_body_867_, v_toBind_868_, v_____r_869_);
lean_dec_ref(v_bodyType_861_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_878_, lean_object* v_body_879_, lean_object* v___x_880_, lean_object* v___x_881_, lean_object* v_toMonadRef_882_, lean_object* v___x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_toCold_892_; lean_object* v_options_893_; uint8_t v_hasTrace_894_; 
v_toCold_892_ = lean_ctor_get(v___y_886_, 0);
v_options_893_ = lean_ctor_get(v_toCold_892_, 2);
v_hasTrace_894_ = lean_ctor_get_uint8(v_options_893_, sizeof(void*)*1);
if (v_hasTrace_894_ == 0)
{
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v___x_883_);
lean_dec_ref(v_toMonadRef_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v_body_879_);
lean_dec(v_cls_878_);
goto v___jp_889_;
}
else
{
lean_object* v_inheritedTraceOptions_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_inheritedTraceOptions_895_ = lean_ctor_get(v_toCold_892_, 11);
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_878_);
v___x_897_ = l_Lean_Name_append(v___x_896_, v_cls_878_);
v___x_898_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_895_, v_options_893_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v___x_883_);
lean_dec_ref(v_toMonadRef_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v_body_879_);
lean_dec(v_cls_878_);
goto v___jp_889_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_7477__overap_902_; lean_object* v___x_903_; 
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3);
v___x_900_ = l_Lean_MessageData_ofExpr(v_body_879_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_7477__overap_902_ = l_Lean_addTrace___redArg(v___x_880_, v___x_881_, v_toMonadRef_882_, v___x_883_, v_cls_878_, v___x_901_);
v___x_903_ = lean_apply_5(v___x_7477__overap_902_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, lean_box(0));
return v___x_903_;
}
}
v___jp_889_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_904_, lean_object* v_body_905_, lean_object* v___x_906_, lean_object* v___x_907_, lean_object* v_toMonadRef_908_, lean_object* v___x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_904_, v_body_905_, v___x_906_, v___x_907_, v_toMonadRef_908_, v___x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_918_, lean_object* v_type_919_, lean_object* v___y_920_, lean_object* v_value_921_, uint8_t v___y_922_, lean_object* v___x_923_, uint8_t v___y_924_, lean_object* v_toPure_925_, lean_object* v_us_926_, uint8_t v___x_927_, lean_object* v_rb_928_){
_start:
{
lean_object* v_expr_929_; lean_object* v_exprType_930_; lean_object* v_exprInit_931_; lean_object* v_exprResult_932_; lean_object* v_proof_933_; uint8_t v_modified_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_961_; 
v_expr_929_ = lean_ctor_get(v_rb_928_, 0);
v_exprType_930_ = lean_ctor_get(v_rb_928_, 1);
v_exprInit_931_ = lean_ctor_get(v_rb_928_, 2);
v_exprResult_932_ = lean_ctor_get(v_rb_928_, 3);
v_proof_933_ = lean_ctor_get(v_rb_928_, 4);
v_modified_934_ = lean_ctor_get_uint8(v_rb_928_, sizeof(void*)*5);
v_isSharedCheck_961_ = !lean_is_exclusive(v_rb_928_);
if (v_isSharedCheck_961_ == 0)
{
v___x_936_ = v_rb_928_;
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_proof_933_);
lean_inc(v_exprResult_932_);
lean_inc(v_exprInit_931_);
lean_inc(v_exprType_930_);
lean_inc(v_expr_929_);
lean_dec(v_rb_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_961_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v_expr_940_; lean_object* v___x_941_; lean_object* v_exprType_942_; lean_object* v___x_943_; lean_object* v_exprInit_944_; lean_object* v_exprResult_945_; 
v___x_938_ = 0;
lean_inc_ref_n(v_type_919_, 4);
lean_inc_n(v_declName_918_, 4);
v___x_939_ = l_Lean_mkLambda(v_declName_918_, v___x_938_, v_type_919_, v_expr_929_);
lean_inc_ref_n(v___y_920_, 3);
lean_inc_ref(v___x_939_);
v_expr_940_ = l_Lean_Expr_app___override(v___x_939_, v___y_920_);
v___x_941_ = l_Lean_mkLambda(v_declName_918_, v___x_938_, v_type_919_, v_exprType_930_);
lean_inc_ref(v___x_941_);
v_exprType_942_ = l_Lean_Expr_app___override(v___x_941_, v___y_920_);
v___x_943_ = l_Lean_mkLambda(v_declName_918_, v___x_938_, v_type_919_, v_exprInit_931_);
lean_inc_ref(v___x_943_);
v_exprInit_944_ = l_Lean_Expr_app___override(v___x_943_, v_value_921_);
v_exprResult_945_ = l_Lean_Expr_letE___override(v_declName_918_, v_type_919_, v___y_920_, v_exprResult_932_, v___y_922_);
if (v_modified_934_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_proof_948_; lean_object* v___x_950_; 
lean_dec_ref(v___x_943_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v_proof_933_);
lean_dec(v_us_926_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v_type_919_);
lean_dec(v_declName_918_);
v___x_946_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_947_ = l_Lean_mkConst(v___x_946_, v___x_923_);
lean_inc_ref(v_expr_940_);
lean_inc_ref(v_exprType_942_);
v_proof_948_ = l_Lean_mkAppB(v___x_947_, v_exprType_942_, v_expr_940_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 4, v_proof_948_);
lean_ctor_set(v___x_936_, 3, v_exprResult_945_);
lean_ctor_set(v___x_936_, 2, v_exprInit_944_);
lean_ctor_set(v___x_936_, 1, v_exprType_942_);
lean_ctor_set(v___x_936_, 0, v_expr_940_);
v___x_950_ = v___x_936_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_expr_940_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_exprType_942_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_exprInit_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_exprResult_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_proof_948_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*5, v___y_924_);
v___x_951_ = lean_apply_2(v_toPure_925_, lean_box(0), v___x_950_);
return v___x_951_;
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_proof_956_; lean_object* v___x_958_; 
lean_dec(v___x_923_);
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_954_ = l_Lean_mkConst(v___x_953_, v_us_926_);
lean_inc_ref(v_type_919_);
v___x_955_ = l_Lean_mkLambda(v_declName_918_, v___x_938_, v_type_919_, v_proof_933_);
v_proof_956_ = l_Lean_mkApp6(v___x_954_, v_type_919_, v___x_941_, v___y_920_, v___x_943_, v___x_939_, v___x_955_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 4, v_proof_956_);
lean_ctor_set(v___x_936_, 3, v_exprResult_945_);
lean_ctor_set(v___x_936_, 2, v_exprInit_944_);
lean_ctor_set(v___x_936_, 1, v_exprType_942_);
lean_ctor_set(v___x_936_, 0, v_expr_940_);
v___x_958_ = v___x_936_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_expr_940_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_exprType_942_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_exprInit_944_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_exprResult_945_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_proof_956_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*5, v___x_927_);
v___x_959_ = lean_apply_2(v_toPure_925_, lean_box(0), v___x_958_);
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_962_, lean_object* v_type_963_, lean_object* v___y_964_, lean_object* v_value_965_, lean_object* v___y_966_, lean_object* v___x_967_, lean_object* v___y_968_, lean_object* v_toPure_969_, lean_object* v_us_970_, lean_object* v___x_971_, lean_object* v_rb_972_){
_start:
{
uint8_t v___y_8100__boxed_973_; uint8_t v___y_8102__boxed_974_; uint8_t v___x_8103__boxed_975_; lean_object* v_res_976_; 
v___y_8100__boxed_973_ = lean_unbox(v___y_966_);
v___y_8102__boxed_974_ = lean_unbox(v___y_968_);
v___x_8103__boxed_975_ = lean_unbox(v___x_971_);
v_res_976_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_962_, v_type_963_, v___y_964_, v_value_965_, v___y_8100__boxed_973_, v___x_967_, v___y_8102__boxed_974_, v_toPure_969_, v_us_970_, v___x_8103__boxed_975_, v_rb_972_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_977_, lean_object* v_____x_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_apply_1(v___f_977_, v_____x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_984_, lean_object* v_declName_985_, lean_object* v_type_986_, lean_object* v_value_987_, lean_object* v_us_988_, lean_object* v___x_989_, uint8_t v___x_990_, lean_object* v_toPure_991_, lean_object* v_rb_992_){
_start:
{
lean_object* v_expr_993_; lean_object* v_exprType_994_; lean_object* v_exprInit_995_; lean_object* v_exprResult_996_; lean_object* v_proof_997_; uint8_t v_modified_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1026_; 
v_expr_993_ = lean_ctor_get(v_rb_992_, 0);
v_exprType_994_ = lean_ctor_get(v_rb_992_, 1);
v_exprInit_995_ = lean_ctor_get(v_rb_992_, 2);
v_exprResult_996_ = lean_ctor_get(v_rb_992_, 3);
v_proof_997_ = lean_ctor_get(v_rb_992_, 4);
v_modified_998_ = lean_ctor_get_uint8(v_rb_992_, sizeof(void*)*5);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_rb_992_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1000_ = v_rb_992_;
v_isShared_1001_ = v_isSharedCheck_1026_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_proof_997_);
lean_inc(v_exprResult_996_);
lean_inc(v_exprInit_995_);
lean_inc(v_exprType_994_);
lean_inc(v_expr_993_);
lean_dec(v_rb_992_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1026_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_expr_1002_; lean_object* v_exprType_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v_exprInit_1006_; lean_object* v_exprResult_1007_; 
v_expr_1002_ = lean_expr_lower_loose_bvars(v_expr_993_, v___x_984_, v___x_984_);
lean_dec_ref(v_expr_993_);
v_exprType_1003_ = lean_expr_lower_loose_bvars(v_exprType_994_, v___x_984_, v___x_984_);
lean_dec_ref(v_exprType_994_);
v___x_1004_ = 0;
lean_inc_ref(v_type_986_);
lean_inc(v_declName_985_);
v___x_1005_ = l_Lean_mkLambda(v_declName_985_, v___x_1004_, v_type_986_, v_exprInit_995_);
lean_inc_ref(v_value_987_);
lean_inc_ref(v___x_1005_);
v_exprInit_1006_ = l_Lean_Expr_app___override(v___x_1005_, v_value_987_);
v_exprResult_1007_ = lean_expr_lower_loose_bvars(v_exprResult_996_, v___x_984_, v___x_984_);
lean_dec_ref(v_exprResult_996_);
if (v_modified_998_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_proof_1013_; lean_object* v___x_1015_; 
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_proof_997_);
lean_dec(v_declName_985_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1009_ = l_Lean_mkConst(v___x_1008_, v_us_988_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1011_ = l_Lean_mkConst(v___x_1010_, v___x_989_);
lean_inc_ref_n(v_expr_1002_, 3);
lean_inc_ref_n(v_exprType_1003_, 2);
v___x_1012_ = l_Lean_mkAppB(v___x_1011_, v_exprType_1003_, v_expr_1002_);
v_proof_1013_ = l_Lean_mkApp6(v___x_1009_, v_type_986_, v_exprType_1003_, v_value_987_, v_expr_1002_, v_expr_1002_, v___x_1012_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 4, v_proof_1013_);
lean_ctor_set(v___x_1000_, 3, v_exprResult_1007_);
lean_ctor_set(v___x_1000_, 2, v_exprInit_1006_);
lean_ctor_set(v___x_1000_, 1, v_exprType_1003_);
lean_ctor_set(v___x_1000_, 0, v_expr_1002_);
v___x_1015_ = v___x_1000_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_expr_1002_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_exprType_1003_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_exprInit_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_exprResult_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_proof_1013_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; 
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*5, v___x_990_);
v___x_1016_ = lean_apply_2(v_toPure_991_, lean_box(0), v___x_1015_);
return v___x_1016_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_proof_1021_; lean_object* v___x_1023_; 
lean_dec(v___x_989_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1019_ = l_Lean_mkConst(v___x_1018_, v_us_988_);
lean_inc_ref(v_type_986_);
v___x_1020_ = l_Lean_mkLambda(v_declName_985_, v___x_1004_, v_type_986_, v_proof_997_);
lean_inc_ref(v_expr_1002_);
lean_inc_ref(v_exprType_1003_);
v_proof_1021_ = l_Lean_mkApp6(v___x_1019_, v_type_986_, v_exprType_1003_, v_value_987_, v___x_1005_, v_expr_1002_, v___x_1020_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 4, v_proof_1021_);
lean_ctor_set(v___x_1000_, 3, v_exprResult_1007_);
lean_ctor_set(v___x_1000_, 2, v_exprInit_1006_);
lean_ctor_set(v___x_1000_, 1, v_exprType_1003_);
lean_ctor_set(v___x_1000_, 0, v_expr_1002_);
v___x_1023_ = v___x_1000_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_expr_1002_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_exprType_1003_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_exprInit_1006_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_exprResult_1007_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_proof_1021_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*5, v___x_990_);
v___x_1024_ = lean_apply_2(v_toPure_991_, lean_box(0), v___x_1023_);
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1027_, lean_object* v_declName_1028_, lean_object* v_type_1029_, lean_object* v_value_1030_, lean_object* v_us_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_toPure_1034_, lean_object* v_rb_1035_){
_start:
{
uint8_t v___x_8190__boxed_1036_; lean_object* v_res_1037_; 
v___x_8190__boxed_1036_ = lean_unbox(v___x_1033_);
v_res_1037_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1027_, v_declName_1028_, v_type_1029_, v_value_1030_, v_us_1031_, v___x_1032_, v___x_8190__boxed_1036_, v_toPure_1034_, v_rb_1035_);
lean_dec(v___x_1027_);
return v_res_1037_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1044_, lean_object* v_declName_1045_, lean_object* v_val_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_toMonadRef_1049_, lean_object* v___x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_toCold_1059_; lean_object* v_options_1060_; uint8_t v_hasTrace_1061_; 
v_toCold_1059_ = lean_ctor_get(v___y_1053_, 0);
v_options_1060_ = lean_ctor_get(v_toCold_1059_, 2);
v_hasTrace_1061_ = lean_ctor_get_uint8(v_options_1060_, sizeof(void*)*1);
if (v_hasTrace_1061_ == 0)
{
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_toMonadRef_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_val_1046_);
lean_dec(v_declName_1045_);
lean_dec(v_cls_1044_);
goto v___jp_1056_;
}
else
{
lean_object* v_inheritedTraceOptions_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_inheritedTraceOptions_1062_ = lean_ctor_get(v_toCold_1059_, 11);
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1044_);
v___x_1064_ = l_Lean_Name_append(v___x_1063_, v_cls_1044_);
v___x_1065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1062_, v_options_1060_, v___x_1064_);
lean_dec(v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_toMonadRef_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_val_1046_);
lean_dec(v_declName_1045_);
lean_dec(v_cls_1044_);
goto v___jp_1056_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_7821__overap_1073_; lean_object* v___x_1074_; 
v___x_1066_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1067_ = l_Lean_MessageData_ofName(v_declName_1045_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_MessageData_ofExpr(v_val_1046_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_7821__overap_1073_ = l_Lean_addTrace___redArg(v___x_1047_, v___x_1048_, v_toMonadRef_1049_, v___x_1050_, v_cls_1044_, v___x_1072_);
v___x_1074_ = lean_apply_5(v___x_7821__overap_1073_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
return v___x_1074_;
}
}
v___jp_1056_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1075_, lean_object* v_declName_1076_, lean_object* v_val_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_toMonadRef_1080_, lean_object* v___x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1075_, v_declName_1076_, v_val_1077_, v___x_1078_, v___x_1079_, v_toMonadRef_1080_, v___x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
return v_res_1087_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1094_, lean_object* v_declName_1095_, lean_object* v_val_1096_, lean_object* v_val_x27_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_toMonadRef_1100_, lean_object* v___x_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_toCold_1110_; lean_object* v_options_1111_; uint8_t v_hasTrace_1112_; 
v_toCold_1110_ = lean_ctor_get(v___y_1104_, 0);
v_options_1111_ = lean_ctor_get(v_toCold_1110_, 2);
v_hasTrace_1112_ = lean_ctor_get_uint8(v_options_1111_, sizeof(void*)*1);
if (v_hasTrace_1112_ == 0)
{
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_toMonadRef_1100_);
lean_dec_ref(v___x_1099_);
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_val_x27_1097_);
lean_dec_ref(v_val_1096_);
lean_dec(v_declName_1095_);
lean_dec(v_cls_1094_);
goto v___jp_1107_;
}
else
{
lean_object* v_inheritedTraceOptions_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_inheritedTraceOptions_1113_ = lean_ctor_get(v_toCold_1110_, 11);
v___x_1114_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1094_);
v___x_1115_ = l_Lean_Name_append(v___x_1114_, v_cls_1094_);
v___x_1116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1113_, v_options_1111_, v___x_1115_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_toMonadRef_1100_);
lean_dec_ref(v___x_1099_);
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_val_x27_1097_);
lean_dec_ref(v_val_1096_);
lean_dec(v_declName_1095_);
lean_dec(v_cls_1094_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_7565__overap_1128_; lean_object* v___x_1129_; 
v___x_1117_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1118_ = l_Lean_MessageData_ofName(v_declName_1095_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_MessageData_ofExpr(v_val_1096_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_MessageData_ofExpr(v_val_x27_1097_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_7565__overap_1128_ = l_Lean_addTrace___redArg(v___x_1098_, v___x_1099_, v_toMonadRef_1100_, v___x_1101_, v_cls_1094_, v___x_1127_);
v___x_1129_ = lean_apply_5(v___x_7565__overap_1128_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, lean_box(0));
return v___x_1129_;
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1130_, lean_object* v_declName_1131_, lean_object* v_val_1132_, lean_object* v_val_x27_1133_, lean_object* v___x_1134_, lean_object* v___x_1135_, lean_object* v_toMonadRef_1136_, lean_object* v___x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1130_, v_declName_1131_, v_val_1132_, v_val_x27_1133_, v___x_1134_, v___x_1135_, v_toMonadRef_1136_, v___x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_e_1144_, lean_object* v_xs_1145_, lean_object* v_h_1146_, uint8_t v___x_1147_, lean_object* v_toPure_1148_, lean_object* v_toBind_1149_, lean_object* v___f_1150_, lean_object* v_____r_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1152_ = lean_expr_abstract(v_e_1144_, v_xs_1145_);
v___x_1153_ = lean_expr_abstract(v_h_1146_, v_xs_1145_);
v___x_1154_ = lean_box(v___x_1147_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1152_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_apply_2(v_toPure_1148_, lean_box(0), v___x_1156_);
v___x_1158_ = lean_apply_4(v_toBind_1149_, lean_box(0), lean_box(0), v___x_1157_, v___f_1150_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_e_1159_, lean_object* v_xs_1160_, lean_object* v_h_1161_, lean_object* v___x_1162_, lean_object* v_toPure_1163_, lean_object* v_toBind_1164_, lean_object* v___f_1165_, lean_object* v_____r_1166_){
_start:
{
uint8_t v___x_8422__boxed_1167_; lean_object* v_res_1168_; 
v___x_8422__boxed_1167_ = lean_unbox(v___x_1162_);
v_res_1168_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_e_1159_, v_xs_1160_, v_h_1161_, v___x_8422__boxed_1167_, v_toPure_1163_, v_toBind_1164_, v___f_1165_, v_____r_1166_);
lean_dec_ref(v_h_1161_);
lean_dec_ref(v_xs_1160_);
lean_dec_ref(v_e_1159_);
return v_res_1168_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1172_, lean_object* v_declName_1173_, lean_object* v_val_1174_, lean_object* v_e_1175_, lean_object* v___x_1176_, lean_object* v___x_1177_, lean_object* v_toMonadRef_1178_, lean_object* v___x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_toCold_1188_; lean_object* v_options_1189_; uint8_t v_hasTrace_1190_; 
v_toCold_1188_ = lean_ctor_get(v___y_1182_, 0);
v_options_1189_ = lean_ctor_get(v_toCold_1188_, 2);
v_hasTrace_1190_ = lean_ctor_get_uint8(v_options_1189_, sizeof(void*)*1);
if (v_hasTrace_1190_ == 0)
{
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_toMonadRef_1178_);
lean_dec_ref(v___x_1177_);
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1175_);
lean_dec_ref(v_val_1174_);
lean_dec(v_declName_1173_);
lean_dec(v_cls_1172_);
goto v___jp_1185_;
}
else
{
lean_object* v_inheritedTraceOptions_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_inheritedTraceOptions_1191_ = lean_ctor_get(v_toCold_1188_, 11);
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1172_);
v___x_1193_ = l_Lean_Name_append(v___x_1192_, v_cls_1172_);
v___x_1194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1191_, v_options_1189_, v___x_1193_);
lean_dec(v___x_1193_);
if (v___x_1194_ == 0)
{
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_toMonadRef_1178_);
lean_dec_ref(v___x_1177_);
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1175_);
lean_dec_ref(v_val_1174_);
lean_dec(v_declName_1173_);
lean_dec(v_cls_1172_);
goto v___jp_1185_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_7715__overap_1206_; lean_object* v___x_1207_; 
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1196_ = l_Lean_MessageData_ofName(v_declName_1173_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_MessageData_ofExpr(v_val_1174_);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_MessageData_ofExpr(v_e_1175_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_7715__overap_1206_ = l_Lean_addTrace___redArg(v___x_1176_, v___x_1177_, v_toMonadRef_1178_, v___x_1179_, v_cls_1172_, v___x_1205_);
v___x_1207_ = lean_apply_5(v___x_7715__overap_1206_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, lean_box(0));
return v___x_1207_;
}
}
v___jp_1185_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1208_, lean_object* v_declName_1209_, lean_object* v_val_1210_, lean_object* v_e_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v_toMonadRef_1214_, lean_object* v___x_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1208_, v_declName_1209_, v_val_1210_, v_e_1211_, v___x_1212_, v___x_1213_, v_toMonadRef_1214_, v___x_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_level_1231_, lean_object* v___x_1232_, lean_object* v_type_1233_, lean_object* v_value_1234_, uint8_t v___x_1235_, lean_object* v_toPure_1236_, lean_object* v_toBind_1237_, lean_object* v___f_1238_, lean_object* v_xs_1239_, uint8_t v___x_1240_, lean_object* v___f_1241_, lean_object* v_declName_1242_, lean_object* v_val_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v_toMonadRef_1246_, lean_object* v___x_1247_, lean_object* v_inst_1248_, lean_object* v_____do__lift_1249_){
_start:
{
if (lean_obj_tag(v_____do__lift_1249_) == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v_inst_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v_toMonadRef_1246_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_val_1243_);
lean_dec(v_declName_1242_);
lean_dec(v___f_1241_);
lean_dec_ref(v_xs_1239_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_level_1231_);
lean_ctor_set(v___x_1251_, 1, v___x_1232_);
v___x_1252_ = l_Lean_mkConst(v___x_1250_, v___x_1251_);
lean_inc_ref(v_value_1234_);
v___x_1253_ = l_Lean_mkAppB(v___x_1252_, v_type_1233_, v_value_1234_);
v___x_1254_ = lean_box(v___x_1235_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1253_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_value_1234_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_apply_2(v_toPure_1236_, lean_box(0), v___x_1256_);
v___x_1258_ = lean_apply_4(v_toBind_1237_, lean_box(0), lean_box(0), v___x_1257_, v___f_1238_);
return v___x_1258_;
}
else
{
lean_object* v_e_1259_; lean_object* v_h_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v_cls_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v___f_1238_);
lean_dec_ref(v_value_1234_);
lean_dec_ref(v_type_1233_);
lean_dec(v___x_1232_);
lean_dec(v_level_1231_);
v_e_1259_ = lean_ctor_get(v_____do__lift_1249_, 0);
lean_inc_ref_n(v_e_1259_, 2);
v_h_1260_ = lean_ctor_get(v_____do__lift_1249_, 1);
lean_inc_ref(v_h_1260_);
lean_dec_ref_known(v_____do__lift_1249_, 2);
v___x_1261_ = lean_box(v___x_1240_);
lean_inc(v_toBind_1237_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1262_, 0, v_e_1259_);
lean_closure_set(v___f_1262_, 1, v_xs_1239_);
lean_closure_set(v___f_1262_, 2, v_h_1260_);
lean_closure_set(v___f_1262_, 3, v___x_1261_);
lean_closure_set(v___f_1262_, 4, v_toPure_1236_);
lean_closure_set(v___f_1262_, 5, v_toBind_1237_);
lean_closure_set(v___f_1262_, 6, v___f_1241_);
v_cls_1263_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1264_, 0, v_cls_1263_);
lean_closure_set(v___f_1264_, 1, v_declName_1242_);
lean_closure_set(v___f_1264_, 2, v_val_1243_);
lean_closure_set(v___f_1264_, 3, v_e_1259_);
lean_closure_set(v___f_1264_, 4, v___x_1244_);
lean_closure_set(v___f_1264_, 5, v___x_1245_);
lean_closure_set(v___f_1264_, 6, v_toMonadRef_1246_);
lean_closure_set(v___f_1264_, 7, v___x_1247_);
v___x_1265_ = lean_apply_2(v_inst_1248_, lean_box(0), v___f_1264_);
v___x_1266_ = lean_apply_4(v_toBind_1237_, lean_box(0), lean_box(0), v___x_1265_, v___f_1262_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_level_1267_ = _args[0];
lean_object* v___x_1268_ = _args[1];
lean_object* v_type_1269_ = _args[2];
lean_object* v_value_1270_ = _args[3];
lean_object* v___x_1271_ = _args[4];
lean_object* v_toPure_1272_ = _args[5];
lean_object* v_toBind_1273_ = _args[6];
lean_object* v___f_1274_ = _args[7];
lean_object* v_xs_1275_ = _args[8];
lean_object* v___x_1276_ = _args[9];
lean_object* v___f_1277_ = _args[10];
lean_object* v_declName_1278_ = _args[11];
lean_object* v_val_1279_ = _args[12];
lean_object* v___x_1280_ = _args[13];
lean_object* v___x_1281_ = _args[14];
lean_object* v_toMonadRef_1282_ = _args[15];
lean_object* v___x_1283_ = _args[16];
lean_object* v_inst_1284_ = _args[17];
lean_object* v_____do__lift_1285_ = _args[18];
_start:
{
uint8_t v___x_8562__boxed_1286_; uint8_t v___x_8564__boxed_1287_; lean_object* v_res_1288_; 
v___x_8562__boxed_1286_ = lean_unbox(v___x_1271_);
v___x_8564__boxed_1287_ = lean_unbox(v___x_1276_);
v_res_1288_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_level_1267_, v___x_1268_, v_type_1269_, v_value_1270_, v___x_8562__boxed_1286_, v_toPure_1272_, v_toBind_1273_, v___f_1274_, v_xs_1275_, v___x_8564__boxed_1287_, v___f_1277_, v_declName_1278_, v_val_1279_, v___x_1280_, v___x_1281_, v_toMonadRef_1282_, v___x_1283_, v_inst_1284_, v_____do__lift_1285_);
return v_res_1288_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1299_ = lean_unsigned_to_nat(8u);
v___x_1300_ = lean_unsigned_to_nat(287u);
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1302_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1303_ = l_mkPanicMessageWithDecl(v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_, v___x_1298_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1304_, lean_object* v_type_1305_, lean_object* v_fst_1306_, lean_object* v___x_1307_, lean_object* v_value_1308_, uint8_t v___x_1309_, uint8_t v_fst_1310_, lean_object* v___x_1311_, uint8_t v___x_1312_, lean_object* v_toPure_1313_, lean_object* v_us_1314_, lean_object* v_snd_1315_, lean_object* v___x_1316_, lean_object* v_rb_1317_){
_start:
{
lean_object* v_expr_1318_; lean_object* v_exprType_1319_; lean_object* v_exprInit_1320_; lean_object* v_exprResult_1321_; lean_object* v_proof_1322_; uint8_t v_modified_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1368_; 
v_expr_1318_ = lean_ctor_get(v_rb_1317_, 0);
v_exprType_1319_ = lean_ctor_get(v_rb_1317_, 1);
v_exprInit_1320_ = lean_ctor_get(v_rb_1317_, 2);
v_exprResult_1321_ = lean_ctor_get(v_rb_1317_, 3);
v_proof_1322_ = lean_ctor_get(v_rb_1317_, 4);
v_modified_1323_ = lean_ctor_get_uint8(v_rb_1317_, sizeof(void*)*5);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_rb_1317_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1325_ = v_rb_1317_;
v_isShared_1326_ = v_isSharedCheck_1368_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_proof_1322_);
lean_inc(v_exprResult_1321_);
lean_inc(v_exprInit_1320_);
lean_inc(v_exprType_1319_);
lean_inc(v_expr_1318_);
lean_dec(v_rb_1317_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1368_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_expr_has_loose_bvar(v_exprType_1319_, v___x_1327_);
if (v___x_1328_ == 0)
{
uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v_expr_1331_; lean_object* v_exprType_1332_; lean_object* v___x_1333_; lean_object* v_exprInit_1334_; lean_object* v_exprResult_1335_; 
v___x_1329_ = 0;
lean_inc_ref_n(v_type_1305_, 3);
lean_inc_n(v_declName_1304_, 3);
v___x_1330_ = l_Lean_mkLambda(v_declName_1304_, v___x_1329_, v_type_1305_, v_expr_1318_);
lean_inc_ref_n(v_fst_1306_, 2);
lean_inc_ref(v___x_1330_);
v_expr_1331_ = l_Lean_Expr_app___override(v___x_1330_, v_fst_1306_);
v_exprType_1332_ = lean_expr_lower_loose_bvars(v_exprType_1319_, v___x_1307_, v___x_1307_);
lean_dec_ref(v_exprType_1319_);
v___x_1333_ = l_Lean_mkLambda(v_declName_1304_, v___x_1329_, v_type_1305_, v_exprInit_1320_);
lean_inc_ref(v_value_1308_);
lean_inc_ref(v___x_1333_);
v_exprInit_1334_ = l_Lean_Expr_app___override(v___x_1333_, v_value_1308_);
v_exprResult_1335_ = l_Lean_Expr_letE___override(v_declName_1304_, v_type_1305_, v_fst_1306_, v_exprResult_1321_, v___x_1309_);
if (v_fst_1310_ == 0)
{
lean_dec_ref(v_snd_1315_);
lean_dec_ref(v_fst_1306_);
if (v_modified_1323_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_proof_1338_; lean_object* v___x_1340_; 
lean_dec_ref(v___x_1333_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_proof_1322_);
lean_dec(v_us_1314_);
lean_dec_ref(v_value_1308_);
lean_dec_ref(v_type_1305_);
lean_dec(v_declName_1304_);
v___x_1336_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1337_ = l_Lean_mkConst(v___x_1336_, v___x_1311_);
lean_inc_ref(v_expr_1331_);
lean_inc_ref(v_exprType_1332_);
v_proof_1338_ = l_Lean_mkAppB(v___x_1337_, v_exprType_1332_, v_expr_1331_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 4, v_proof_1338_);
lean_ctor_set(v___x_1325_, 3, v_exprResult_1335_);
lean_ctor_set(v___x_1325_, 2, v_exprInit_1334_);
lean_ctor_set(v___x_1325_, 1, v_exprType_1332_);
lean_ctor_set(v___x_1325_, 0, v_expr_1331_);
v___x_1340_ = v___x_1325_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_expr_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_exprType_1332_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_exprInit_1334_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_exprResult_1335_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_proof_1338_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5, v___x_1312_);
v___x_1341_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_proof_1346_; lean_object* v___x_1348_; 
lean_dec(v___x_1311_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1344_ = l_Lean_mkConst(v___x_1343_, v_us_1314_);
lean_inc_ref(v_type_1305_);
v___x_1345_ = l_Lean_mkLambda(v_declName_1304_, v___x_1329_, v_type_1305_, v_proof_1322_);
lean_inc_ref(v_exprType_1332_);
v_proof_1346_ = l_Lean_mkApp6(v___x_1344_, v_type_1305_, v_exprType_1332_, v_value_1308_, v___x_1333_, v___x_1330_, v___x_1345_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 4, v_proof_1346_);
lean_ctor_set(v___x_1325_, 3, v_exprResult_1335_);
lean_ctor_set(v___x_1325_, 2, v_exprInit_1334_);
lean_ctor_set(v___x_1325_, 1, v_exprType_1332_);
lean_ctor_set(v___x_1325_, 0, v_expr_1331_);
v___x_1348_ = v___x_1325_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_expr_1331_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_exprType_1332_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_exprInit_1334_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_exprResult_1335_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_proof_1346_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5, v___x_1309_);
v___x_1349_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1348_);
return v___x_1349_;
}
}
}
else
{
lean_dec(v___x_1311_);
if (v_modified_1323_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_proof_1353_; lean_object* v___x_1355_; 
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_proof_1322_);
lean_dec(v_declName_1304_);
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1352_ = l_Lean_mkConst(v___x_1351_, v_us_1314_);
lean_inc_ref(v_exprType_1332_);
v_proof_1353_ = l_Lean_mkApp6(v___x_1352_, v_type_1305_, v_exprType_1332_, v_value_1308_, v_fst_1306_, v___x_1333_, v_snd_1315_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 4, v_proof_1353_);
lean_ctor_set(v___x_1325_, 3, v_exprResult_1335_);
lean_ctor_set(v___x_1325_, 2, v_exprInit_1334_);
lean_ctor_set(v___x_1325_, 1, v_exprType_1332_);
lean_ctor_set(v___x_1325_, 0, v_expr_1331_);
v___x_1355_ = v___x_1325_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_expr_1331_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_exprType_1332_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_exprInit_1334_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_exprResult_1335_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_proof_1353_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*5, v___x_1309_);
v___x_1356_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1355_);
return v___x_1356_;
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_proof_1361_; lean_object* v___x_1363_; 
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1359_ = l_Lean_mkConst(v___x_1358_, v_us_1314_);
lean_inc_ref(v_type_1305_);
v___x_1360_ = l_Lean_mkLambda(v_declName_1304_, v___x_1329_, v_type_1305_, v_proof_1322_);
lean_inc_ref(v_exprType_1332_);
v_proof_1361_ = l_Lean_mkApp8(v___x_1359_, v_type_1305_, v_exprType_1332_, v_value_1308_, v_fst_1306_, v___x_1333_, v___x_1330_, v_snd_1315_, v___x_1360_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 4, v_proof_1361_);
lean_ctor_set(v___x_1325_, 3, v_exprResult_1335_);
lean_ctor_set(v___x_1325_, 2, v_exprInit_1334_);
lean_ctor_set(v___x_1325_, 1, v_exprType_1332_);
lean_ctor_set(v___x_1325_, 0, v_expr_1331_);
v___x_1363_ = v___x_1325_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_expr_1331_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_exprType_1332_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_exprInit_1334_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_exprResult_1335_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_proof_1361_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*5, v___x_1309_);
v___x_1364_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1363_);
return v___x_1364_;
}
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_del_object(v___x_1325_);
lean_dec_ref(v_proof_1322_);
lean_dec_ref(v_exprResult_1321_);
lean_dec_ref(v_exprInit_1320_);
lean_dec_ref(v_exprType_1319_);
lean_dec_ref(v_expr_1318_);
lean_dec_ref(v_snd_1315_);
lean_dec(v_us_1314_);
lean_dec(v_toPure_1313_);
lean_dec(v___x_1311_);
lean_dec_ref(v_value_1308_);
lean_dec_ref(v_fst_1306_);
lean_dec_ref(v_type_1305_);
lean_dec(v_declName_1304_);
v___x_1366_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1367_ = l_panic___redArg(v___x_1316_, v___x_1366_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1369_, lean_object* v_type_1370_, lean_object* v_fst_1371_, lean_object* v___x_1372_, lean_object* v_value_1373_, lean_object* v___x_1374_, lean_object* v_fst_1375_, lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v_toPure_1378_, lean_object* v_us_1379_, lean_object* v_snd_1380_, lean_object* v___x_1381_, lean_object* v_rb_1382_){
_start:
{
uint8_t v___x_8684__boxed_1383_; uint8_t v_fst_8685__boxed_1384_; uint8_t v___x_8687__boxed_1385_; lean_object* v_res_1386_; 
v___x_8684__boxed_1383_ = lean_unbox(v___x_1374_);
v_fst_8685__boxed_1384_ = lean_unbox(v_fst_1375_);
v___x_8687__boxed_1385_ = lean_unbox(v___x_1377_);
v_res_1386_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1369_, v_type_1370_, v_fst_1371_, v___x_1372_, v_value_1373_, v___x_8684__boxed_1383_, v_fst_8685__boxed_1384_, v___x_1376_, v___x_8687__boxed_1385_, v_toPure_1378_, v_us_1379_, v_snd_1380_, v___x_1381_, v_rb_1382_);
lean_dec(v___x_1381_);
lean_dec(v___x_1372_);
return v_res_1386_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_instMonadEIO___redArg();
return v___x_1390_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0);
v___x_1392_ = l_StateRefT_x27_instMonad___redArg(v___x_1391_);
return v___x_1392_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1400_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1399_, v___x_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8);
v___f_1403_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___x_1404_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1403_, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1406_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1408_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11));
v___x_1409_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1408_, v___x_1407_, v___x_1406_);
return v___x_1409_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; 
v___x_1411_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12);
v___f_1412_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___f_1413_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10));
v___x_1414_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1413_, v___f_1412_, v___x_1411_);
return v___x_1414_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14));
v___x_1417_ = lean_unsigned_to_nat(34u);
v___x_1418_ = lean_unsigned_to_nat(217u);
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1420_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1421_ = l_mkPanicMessageWithDecl(v___x_1420_, v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1422_, lean_object* v_type_1423_, lean_object* v_value_1424_, uint8_t v___y_1425_, lean_object* v___x_1426_, lean_object* v_toPure_1427_, lean_object* v_us_1428_, uint8_t v___x_1429_, lean_object* v_decl_1430_, lean_object* v_x_1431_, lean_object* v_i_1432_, lean_object* v_xs_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_info_1438_, lean_object* v_fixed_1439_, lean_object* v_used_1440_, lean_object* v_body_1441_, lean_object* v_toBind_1442_, lean_object* v_withNewLemmas_1443_, lean_object* v_val_x27_1444_, lean_object* v_val_1445_, uint8_t v___x_1446_, lean_object* v_____r_1447_){
_start:
{
uint8_t v___y_1449_; lean_object* v___y_1450_; uint8_t v___y_1467_; uint8_t v___x_1469_; 
v___x_1469_ = lean_expr_eqv(v_val_1445_, v_val_x27_1444_);
if (v___x_1469_ == 0)
{
v___y_1467_ = v___y_1425_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___x_1446_;
goto v___jp_1466_;
}
v___jp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1451_ = lean_box(v___y_1425_);
v___x_1452_ = lean_box(v___y_1449_);
v___x_1453_ = lean_box(v___x_1429_);
v___f_1454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_1454_, 0, v_declName_1422_);
lean_closure_set(v___f_1454_, 1, v_type_1423_);
lean_closure_set(v___f_1454_, 2, v___y_1450_);
lean_closure_set(v___f_1454_, 3, v_value_1424_);
lean_closure_set(v___f_1454_, 4, v___x_1451_);
lean_closure_set(v___f_1454_, 5, v___x_1426_);
lean_closure_set(v___f_1454_, 6, v___x_1452_);
lean_closure_set(v___f_1454_, 7, v_toPure_1427_);
lean_closure_set(v___f_1454_, 8, v_us_1428_);
lean_closure_set(v___f_1454_, 9, v___x_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_decl_1430_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_mk_empty_array_with_capacity(v___x_1457_);
lean_inc_ref(v_x_1431_);
v___x_1459_ = lean_array_push(v___x_1458_, v_x_1431_);
v___x_1460_ = lean_nat_add(v_i_1432_, v___x_1457_);
v___x_1461_ = lean_array_push(v_xs_1433_, v_x_1431_);
lean_inc_ref(v_inst_1436_);
lean_inc_ref(v_inst_1434_);
v___x_1462_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1434_, v_inst_1435_, v_inst_1436_, v_inst_1437_, v_info_1438_, v_fixed_1439_, v_used_1440_, v_body_1441_, v___x_1460_, v___x_1461_);
v___x_1463_ = lean_apply_4(v_toBind_1442_, lean_box(0), lean_box(0), v___x_1462_, v___f_1454_);
v___x_1464_ = lean_apply_3(v_withNewLemmas_1443_, lean_box(0), v___x_1459_, v___x_1463_);
v___x_1465_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1436_, v_inst_1434_, v___x_1456_, v___x_1464_);
return v___x_1465_;
}
v___jp_1466_:
{
if (v___y_1467_ == 0)
{
lean_inc_ref(v_value_1424_);
v___y_1449_ = v___y_1467_;
v___y_1450_ = v_value_1424_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_expr_abstract(v_val_x27_1444_, v_xs_1433_);
v___y_1449_ = v___y_1467_;
v___y_1450_ = v___x_1468_;
goto v___jp_1448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1470_ = _args[0];
lean_object* v_type_1471_ = _args[1];
lean_object* v_value_1472_ = _args[2];
lean_object* v___y_1473_ = _args[3];
lean_object* v___x_1474_ = _args[4];
lean_object* v_toPure_1475_ = _args[5];
lean_object* v_us_1476_ = _args[6];
lean_object* v___x_1477_ = _args[7];
lean_object* v_decl_1478_ = _args[8];
lean_object* v_x_1479_ = _args[9];
lean_object* v_i_1480_ = _args[10];
lean_object* v_xs_1481_ = _args[11];
lean_object* v_inst_1482_ = _args[12];
lean_object* v_inst_1483_ = _args[13];
lean_object* v_inst_1484_ = _args[14];
lean_object* v_inst_1485_ = _args[15];
lean_object* v_info_1486_ = _args[16];
lean_object* v_fixed_1487_ = _args[17];
lean_object* v_used_1488_ = _args[18];
lean_object* v_body_1489_ = _args[19];
lean_object* v_toBind_1490_ = _args[20];
lean_object* v_withNewLemmas_1491_ = _args[21];
lean_object* v_val_x27_1492_ = _args[22];
lean_object* v_val_1493_ = _args[23];
lean_object* v___x_1494_ = _args[24];
lean_object* v_____r_1495_ = _args[25];
_start:
{
uint8_t v___y_8945__boxed_1496_; uint8_t v___x_8947__boxed_1497_; uint8_t v___x_8953__boxed_1498_; lean_object* v_res_1499_; 
v___y_8945__boxed_1496_ = lean_unbox(v___y_1473_);
v___x_8947__boxed_1497_ = lean_unbox(v___x_1477_);
v___x_8953__boxed_1498_ = lean_unbox(v___x_1494_);
v_res_1499_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1470_, v_type_1471_, v_value_1472_, v___y_8945__boxed_1496_, v___x_1474_, v_toPure_1475_, v_us_1476_, v___x_8947__boxed_1497_, v_decl_1478_, v_x_1479_, v_i_1480_, v_xs_1481_, v_inst_1482_, v_inst_1483_, v_inst_1484_, v_inst_1485_, v_info_1486_, v_fixed_1487_, v_used_1488_, v_body_1489_, v_toBind_1490_, v_withNewLemmas_1491_, v_val_x27_1492_, v_val_1493_, v___x_8953__boxed_1498_, v_____r_1495_);
lean_dec_ref(v_val_1493_);
lean_dec_ref(v_val_x27_1492_);
lean_dec(v_i_1480_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1500_, lean_object* v_type_1501_, lean_object* v_value_1502_, uint8_t v___y_1503_, lean_object* v___x_1504_, lean_object* v_toPure_1505_, lean_object* v_us_1506_, uint8_t v___x_1507_, lean_object* v_decl_1508_, lean_object* v_x_1509_, lean_object* v_i_1510_, lean_object* v_xs_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_info_1516_, lean_object* v_fixed_1517_, lean_object* v_used_1518_, lean_object* v_body_1519_, lean_object* v_toBind_1520_, lean_object* v_withNewLemmas_1521_, lean_object* v_val_1522_, uint8_t v___x_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_toMonadRef_1526_, lean_object* v___x_1527_, lean_object* v_val_x27_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___f_1532_; lean_object* v_cls_1533_; lean_object* v___f_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1529_ = lean_box(v___y_1503_);
v___x_1530_ = lean_box(v___x_1507_);
v___x_1531_ = lean_box(v___x_1523_);
lean_inc_ref(v_val_1522_);
lean_inc_ref(v_val_x27_1528_);
lean_inc(v_toBind_1520_);
lean_inc(v_inst_1513_);
lean_inc(v_declName_1500_);
v___f_1532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 26, 25);
lean_closure_set(v___f_1532_, 0, v_declName_1500_);
lean_closure_set(v___f_1532_, 1, v_type_1501_);
lean_closure_set(v___f_1532_, 2, v_value_1502_);
lean_closure_set(v___f_1532_, 3, v___x_1529_);
lean_closure_set(v___f_1532_, 4, v___x_1504_);
lean_closure_set(v___f_1532_, 5, v_toPure_1505_);
lean_closure_set(v___f_1532_, 6, v_us_1506_);
lean_closure_set(v___f_1532_, 7, v___x_1530_);
lean_closure_set(v___f_1532_, 8, v_decl_1508_);
lean_closure_set(v___f_1532_, 9, v_x_1509_);
lean_closure_set(v___f_1532_, 10, v_i_1510_);
lean_closure_set(v___f_1532_, 11, v_xs_1511_);
lean_closure_set(v___f_1532_, 12, v_inst_1512_);
lean_closure_set(v___f_1532_, 13, v_inst_1513_);
lean_closure_set(v___f_1532_, 14, v_inst_1514_);
lean_closure_set(v___f_1532_, 15, v_inst_1515_);
lean_closure_set(v___f_1532_, 16, v_info_1516_);
lean_closure_set(v___f_1532_, 17, v_fixed_1517_);
lean_closure_set(v___f_1532_, 18, v_used_1518_);
lean_closure_set(v___f_1532_, 19, v_body_1519_);
lean_closure_set(v___f_1532_, 20, v_toBind_1520_);
lean_closure_set(v___f_1532_, 21, v_withNewLemmas_1521_);
lean_closure_set(v___f_1532_, 22, v_val_x27_1528_);
lean_closure_set(v___f_1532_, 23, v_val_1522_);
lean_closure_set(v___f_1532_, 24, v___x_1531_);
v_cls_1533_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1534_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1534_, 0, v_cls_1533_);
lean_closure_set(v___f_1534_, 1, v_declName_1500_);
lean_closure_set(v___f_1534_, 2, v_val_1522_);
lean_closure_set(v___f_1534_, 3, v_val_x27_1528_);
lean_closure_set(v___f_1534_, 4, v___x_1524_);
lean_closure_set(v___f_1534_, 5, v___x_1525_);
lean_closure_set(v___f_1534_, 6, v_toMonadRef_1526_);
lean_closure_set(v___f_1534_, 7, v___x_1527_);
v___x_1535_ = lean_apply_2(v_inst_1513_, lean_box(0), v___f_1534_);
v___x_1536_ = lean_apply_4(v_toBind_1520_, lean_box(0), lean_box(0), v___x_1535_, v___f_1532_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1537_ = _args[0];
lean_object* v_type_1538_ = _args[1];
lean_object* v_value_1539_ = _args[2];
lean_object* v___y_1540_ = _args[3];
lean_object* v___x_1541_ = _args[4];
lean_object* v_toPure_1542_ = _args[5];
lean_object* v_us_1543_ = _args[6];
lean_object* v___x_1544_ = _args[7];
lean_object* v_decl_1545_ = _args[8];
lean_object* v_x_1546_ = _args[9];
lean_object* v_i_1547_ = _args[10];
lean_object* v_xs_1548_ = _args[11];
lean_object* v_inst_1549_ = _args[12];
lean_object* v_inst_1550_ = _args[13];
lean_object* v_inst_1551_ = _args[14];
lean_object* v_inst_1552_ = _args[15];
lean_object* v_info_1553_ = _args[16];
lean_object* v_fixed_1554_ = _args[17];
lean_object* v_used_1555_ = _args[18];
lean_object* v_body_1556_ = _args[19];
lean_object* v_toBind_1557_ = _args[20];
lean_object* v_withNewLemmas_1558_ = _args[21];
lean_object* v_val_1559_ = _args[22];
lean_object* v___x_1560_ = _args[23];
lean_object* v___x_1561_ = _args[24];
lean_object* v___x_1562_ = _args[25];
lean_object* v_toMonadRef_1563_ = _args[26];
lean_object* v___x_1564_ = _args[27];
lean_object* v_val_x27_1565_ = _args[28];
_start:
{
uint8_t v___y_8892__boxed_1566_; uint8_t v___x_8894__boxed_1567_; uint8_t v___x_8900__boxed_1568_; lean_object* v_res_1569_; 
v___y_8892__boxed_1566_ = lean_unbox(v___y_1540_);
v___x_8894__boxed_1567_ = lean_unbox(v___x_1544_);
v___x_8900__boxed_1568_ = lean_unbox(v___x_1560_);
v_res_1569_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1537_, v_type_1538_, v_value_1539_, v___y_8892__boxed_1566_, v___x_1541_, v_toPure_1542_, v_us_1543_, v___x_8894__boxed_1567_, v_decl_1545_, v_x_1546_, v_i_1547_, v_xs_1548_, v_inst_1549_, v_inst_1550_, v_inst_1551_, v_inst_1552_, v_info_1553_, v_fixed_1554_, v_used_1555_, v_body_1556_, v_toBind_1557_, v_withNewLemmas_1558_, v_val_1559_, v___x_8900__boxed_1568_, v___x_1561_, v___x_1562_, v_toMonadRef_1563_, v___x_1564_, v_val_x27_1565_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1570_, lean_object* v_declName_1571_, lean_object* v_type_1572_, lean_object* v_value_1573_, uint8_t v___x_1574_, lean_object* v___x_1575_, uint8_t v___x_1576_, lean_object* v_toPure_1577_, lean_object* v_us_1578_, lean_object* v___x_1579_, lean_object* v_x_1580_, lean_object* v_i_1581_, lean_object* v_xs_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_info_1587_, lean_object* v_fixed_1588_, lean_object* v_used_1589_, lean_object* v_body_1590_, lean_object* v_toBind_1591_, lean_object* v_withNewLemmas_1592_, lean_object* v_____x_1593_){
_start:
{
lean_object* v_snd_1594_; lean_object* v_fst_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1617_; 
v_snd_1594_ = lean_ctor_get(v_____x_1593_, 1);
lean_inc(v_snd_1594_);
v_fst_1595_ = lean_ctor_get(v_____x_1593_, 0);
lean_inc(v_fst_1595_);
lean_dec_ref(v_____x_1593_);
v_fst_1596_ = lean_ctor_get(v_snd_1594_, 0);
v_snd_1597_ = lean_ctor_get(v_snd_1594_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_snd_1594_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1599_ = v_snd_1594_;
v_isShared_1600_ = v_isSharedCheck_1617_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_inc(v_fst_1596_);
lean_dec(v_snd_1594_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1617_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_box(0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 1);
lean_ctor_set(v___x_1599_, 1, v___x_1601_);
lean_ctor_set(v___x_1599_, 0, v_decl_1570_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_decl_1570_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_box(v___x_1574_);
v___x_1606_ = lean_box(v___x_1576_);
v___f_1607_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 14, 13);
lean_closure_set(v___f_1607_, 0, v_declName_1571_);
lean_closure_set(v___f_1607_, 1, v_type_1572_);
lean_closure_set(v___f_1607_, 2, v_fst_1595_);
lean_closure_set(v___f_1607_, 3, v___x_1604_);
lean_closure_set(v___f_1607_, 4, v_value_1573_);
lean_closure_set(v___f_1607_, 5, v___x_1605_);
lean_closure_set(v___f_1607_, 6, v_fst_1596_);
lean_closure_set(v___f_1607_, 7, v___x_1575_);
lean_closure_set(v___f_1607_, 8, v___x_1606_);
lean_closure_set(v___f_1607_, 9, v_toPure_1577_);
lean_closure_set(v___f_1607_, 10, v_us_1578_);
lean_closure_set(v___f_1607_, 11, v_snd_1597_);
lean_closure_set(v___f_1607_, 12, v___x_1579_);
v___x_1608_ = lean_mk_empty_array_with_capacity(v___x_1604_);
lean_inc_ref(v_x_1580_);
v___x_1609_ = lean_array_push(v___x_1608_, v_x_1580_);
v___x_1610_ = lean_nat_add(v_i_1581_, v___x_1604_);
v___x_1611_ = lean_array_push(v_xs_1582_, v_x_1580_);
lean_inc_ref(v_inst_1585_);
lean_inc_ref(v_inst_1583_);
v___x_1612_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1583_, v_inst_1584_, v_inst_1585_, v_inst_1586_, v_info_1587_, v_fixed_1588_, v_used_1589_, v_body_1590_, v___x_1610_, v___x_1611_);
v___x_1613_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1612_, v___f_1607_);
v___x_1614_ = lean_apply_3(v_withNewLemmas_1592_, lean_box(0), v___x_1609_, v___x_1613_);
v___x_1615_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1585_, v_inst_1583_, v___x_1603_, v___x_1614_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1618_ = _args[0];
lean_object* v_declName_1619_ = _args[1];
lean_object* v_type_1620_ = _args[2];
lean_object* v_value_1621_ = _args[3];
lean_object* v___x_1622_ = _args[4];
lean_object* v___x_1623_ = _args[5];
lean_object* v___x_1624_ = _args[6];
lean_object* v_toPure_1625_ = _args[7];
lean_object* v_us_1626_ = _args[8];
lean_object* v___x_1627_ = _args[9];
lean_object* v_x_1628_ = _args[10];
lean_object* v_i_1629_ = _args[11];
lean_object* v_xs_1630_ = _args[12];
lean_object* v_inst_1631_ = _args[13];
lean_object* v_inst_1632_ = _args[14];
lean_object* v_inst_1633_ = _args[15];
lean_object* v_inst_1634_ = _args[16];
lean_object* v_info_1635_ = _args[17];
lean_object* v_fixed_1636_ = _args[18];
lean_object* v_used_1637_ = _args[19];
lean_object* v_body_1638_ = _args[20];
lean_object* v_toBind_1639_ = _args[21];
lean_object* v_withNewLemmas_1640_ = _args[22];
lean_object* v_____x_1641_ = _args[23];
_start:
{
uint8_t v___x_8916__boxed_1642_; uint8_t v___x_8918__boxed_1643_; lean_object* v_res_1644_; 
v___x_8916__boxed_1642_ = lean_unbox(v___x_1622_);
v___x_8918__boxed_1643_ = lean_unbox(v___x_1624_);
v_res_1644_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1618_, v_declName_1619_, v_type_1620_, v_value_1621_, v___x_8916__boxed_1642_, v___x_1623_, v___x_8918__boxed_1643_, v_toPure_1625_, v_us_1626_, v___x_1627_, v_x_1628_, v_i_1629_, v_xs_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_inst_1634_, v_info_1635_, v_fixed_1636_, v_used_1637_, v_body_1638_, v_toBind_1639_, v_withNewLemmas_1640_, v_____x_1641_);
lean_dec(v_i_1629_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1645_ = _args[0];
lean_object* v_declName_1646_ = _args[1];
lean_object* v_type_1647_ = _args[2];
lean_object* v_value_1648_ = _args[3];
lean_object* v_us_1649_ = _args[4];
lean_object* v___x_1650_ = _args[5];
lean_object* v___x_1651_ = _args[6];
lean_object* v_toPure_1652_ = _args[7];
lean_object* v_i_1653_ = _args[8];
lean_object* v_xs_1654_ = _args[9];
lean_object* v_inst_1655_ = _args[10];
lean_object* v_inst_1656_ = _args[11];
lean_object* v_inst_1657_ = _args[12];
lean_object* v_inst_1658_ = _args[13];
lean_object* v_info_1659_ = _args[14];
lean_object* v_fixed_1660_ = _args[15];
lean_object* v_used_1661_ = _args[16];
lean_object* v_body_1662_ = _args[17];
lean_object* v_toBind_1663_ = _args[18];
lean_object* v_____r_1664_ = _args[19];
_start:
{
uint8_t v___x_8875__boxed_1665_; lean_object* v_res_1666_; 
v___x_8875__boxed_1665_ = lean_unbox(v___x_1651_);
v_res_1666_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1645_, v_declName_1646_, v_type_1647_, v_value_1648_, v_us_1649_, v___x_1650_, v___x_8875__boxed_1665_, v_toPure_1652_, v_i_1653_, v_xs_1654_, v_inst_1655_, v_inst_1656_, v_inst_1657_, v_inst_1658_, v_info_1659_, v_fixed_1660_, v_used_1661_, v_body_1662_, v_toBind_1663_, v_____r_1664_);
lean_dec(v_i_1653_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_info_1671_, lean_object* v_fixed_1672_, lean_object* v_used_1673_, lean_object* v_e_1674_, lean_object* v_i_1675_, lean_object* v_xs_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v_toApplicative_1678_; lean_object* v_toFunctor_1679_; lean_object* v_toSeq_1680_; lean_object* v_toSeqLeft_1681_; lean_object* v_toSeqRight_1682_; lean_object* v___f_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v___f_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v_toApplicative_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1795_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v_toApplicative_1678_ = lean_ctor_get(v___x_1677_, 0);
v_toFunctor_1679_ = lean_ctor_get(v_toApplicative_1678_, 0);
v_toSeq_1680_ = lean_ctor_get(v_toApplicative_1678_, 2);
v_toSeqLeft_1681_ = lean_ctor_get(v_toApplicative_1678_, 3);
v_toSeqRight_1682_ = lean_ctor_get(v_toApplicative_1678_, 4);
v___f_1683_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2));
v___f_1684_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1679_, 2);
v___f_1685_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1685_, 0, v_toFunctor_1679_);
v___f_1686_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1686_, 0, v_toFunctor_1679_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___f_1685_);
lean_ctor_set(v___x_1687_, 1, v___f_1686_);
lean_inc(v_toSeqRight_1682_);
v___f_1688_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1688_, 0, v_toSeqRight_1682_);
lean_inc(v_toSeqLeft_1681_);
v___f_1689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1689_, 0, v_toSeqLeft_1681_);
lean_inc(v_toSeq_1680_);
v___f_1690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1690_, 0, v_toSeq_1680_);
v___x_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1687_);
lean_ctor_set(v___x_1691_, 1, v___f_1683_);
lean_ctor_set(v___x_1691_, 2, v___f_1690_);
lean_ctor_set(v___x_1691_, 3, v___f_1689_);
lean_ctor_set(v___x_1691_, 4, v___f_1688_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___f_1684_);
v___x_1693_ = l_StateRefT_x27_instMonad___redArg(v___x_1692_);
v_toApplicative_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v___x_1693_, 1);
lean_dec(v_unused_1796_);
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1795_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_toApplicative_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1795_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_toFunctor_1698_; lean_object* v_toSeq_1699_; lean_object* v_toSeqLeft_1700_; lean_object* v_toSeqRight_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1793_; 
v_toFunctor_1698_ = lean_ctor_get(v_toApplicative_1694_, 0);
v_toSeq_1699_ = lean_ctor_get(v_toApplicative_1694_, 2);
v_toSeqLeft_1700_ = lean_ctor_get(v_toApplicative_1694_, 3);
v_toSeqRight_1701_ = lean_ctor_get(v_toApplicative_1694_, 4);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_toApplicative_1694_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_toApplicative_1694_, 1);
lean_dec(v_unused_1794_);
v___x_1703_ = v_toApplicative_1694_;
v_isShared_1704_ = v_isSharedCheck_1793_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_toSeqRight_1701_);
lean_inc(v_toSeqLeft_1700_);
lean_inc(v_toSeq_1699_);
lean_inc(v_toFunctor_1698_);
lean_dec(v_toApplicative_1694_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1793_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___f_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___f_1711_; lean_object* v___f_1712_; lean_object* v___x_1714_; 
v___f_1705_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4));
v___f_1706_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5));
lean_inc_ref(v_toFunctor_1698_);
v___f_1707_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1707_, 0, v_toFunctor_1698_);
v___f_1708_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1708_, 0, v_toFunctor_1698_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___f_1707_);
lean_ctor_set(v___x_1709_, 1, v___f_1708_);
v___f_1710_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1710_, 0, v_toSeqRight_1701_);
v___f_1711_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1711_, 0, v_toSeqLeft_1700_);
v___f_1712_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1712_, 0, v_toSeq_1699_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___f_1710_);
lean_ctor_set(v___x_1703_, 3, v___f_1711_);
lean_ctor_set(v___x_1703_, 2, v___f_1712_);
lean_ctor_set(v___x_1703_, 1, v___f_1705_);
lean_ctor_set(v___x_1703_, 0, v___x_1709_);
v___x_1714_ = v___x_1703_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___f_1705_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___f_1712_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v___f_1711_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___f_1710_);
v___x_1714_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v___f_1706_);
lean_ctor_set(v___x_1696_, 0, v___x_1714_);
v___x_1716_ = v___x_1696_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___f_1706_);
v___x_1716_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_toApplicative_1719_; lean_object* v_toMonadRef_1720_; lean_object* v_haveInfo_1721_; lean_object* v_body_1722_; lean_object* v_bodyType_1723_; lean_object* v_level_1724_; lean_object* v_toBind_1725_; lean_object* v_toPure_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1717_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9);
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13);
v_toApplicative_1719_ = lean_ctor_get(v_inst_1667_, 0);
v_toMonadRef_1720_ = lean_ctor_get(v___x_1718_, 0);
v_haveInfo_1721_ = lean_ctor_get(v_info_1671_, 0);
v_body_1722_ = lean_ctor_get(v_info_1671_, 3);
v_bodyType_1723_ = lean_ctor_get(v_info_1671_, 4);
v_level_1724_ = lean_ctor_get(v_info_1671_, 5);
v_toBind_1725_ = lean_ctor_get(v_inst_1667_, 1);
lean_inc(v_toBind_1725_);
v_toPure_1726_ = lean_ctor_get(v_toApplicative_1719_, 1);
lean_inc(v_toPure_1726_);
v___x_1727_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1728_ = lean_array_get_size(v_haveInfo_1721_);
v___x_1729_ = lean_nat_dec_lt(v_i_1675_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___f_1731_; lean_object* v_cls_1732_; lean_object* v___f_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_inc(v_level_1724_);
lean_inc_ref(v_bodyType_1723_);
lean_inc_ref_n(v_body_1722_, 2);
lean_dec(v_i_1675_);
lean_dec_ref(v_used_1673_);
lean_dec_ref(v_fixed_1672_);
lean_dec_ref(v_info_1671_);
lean_dec_ref(v_inst_1669_);
lean_dec_ref(v_inst_1667_);
v___x_1730_ = lean_box(v___x_1729_);
lean_inc(v_toBind_1725_);
v___f_1731_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1731_, 0, v_inst_1670_);
lean_closure_set(v___f_1731_, 1, v_bodyType_1723_);
lean_closure_set(v___f_1731_, 2, v_xs_1676_);
lean_closure_set(v___f_1731_, 3, v_level_1724_);
lean_closure_set(v___f_1731_, 4, v_e_1674_);
lean_closure_set(v___f_1731_, 5, v___x_1730_);
lean_closure_set(v___f_1731_, 6, v_toPure_1726_);
lean_closure_set(v___f_1731_, 7, v_body_1722_);
lean_closure_set(v___f_1731_, 8, v_toBind_1725_);
v_cls_1732_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1720_);
v___f_1733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1733_, 0, v_cls_1732_);
lean_closure_set(v___f_1733_, 1, v_body_1722_);
lean_closure_set(v___f_1733_, 2, v___x_1716_);
lean_closure_set(v___f_1733_, 3, v___x_1717_);
lean_closure_set(v___f_1733_, 4, v_toMonadRef_1720_);
lean_closure_set(v___f_1733_, 5, v___x_1727_);
v___x_1734_ = lean_apply_2(v_inst_1668_, lean_box(0), v___f_1733_);
v___x_1735_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1734_, v___f_1731_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
lean_inc_ref(v_inst_1667_);
v___x_1737_ = l_instInhabitedOfMonad___redArg(v_inst_1667_, v___x_1736_);
if (lean_obj_tag(v_e_1674_) == 8)
{
uint8_t v_nondep_1741_; 
v_nondep_1741_ = lean_ctor_get_uint8(v_e_1674_, sizeof(void*)*4 + 8);
if (v_nondep_1741_ == 1)
{
lean_object* v_declName_1742_; lean_object* v_type_1743_; lean_object* v_value_1744_; lean_object* v_body_1745_; lean_object* v_hinfo_1746_; lean_object* v_decl_1747_; lean_object* v_level_1748_; lean_object* v_x_1749_; lean_object* v_val_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_us_1753_; uint8_t v___y_1755_; uint8_t v___y_1756_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_declName_1742_ = lean_ctor_get(v_e_1674_, 0);
lean_inc(v_declName_1742_);
v_type_1743_ = lean_ctor_get(v_e_1674_, 1);
lean_inc_ref(v_type_1743_);
v_value_1744_ = lean_ctor_get(v_e_1674_, 2);
lean_inc_ref(v_value_1744_);
v_body_1745_ = lean_ctor_get(v_e_1674_, 3);
lean_inc_ref(v_body_1745_);
lean_dec_ref_known(v_e_1674_, 4);
v_hinfo_1746_ = lean_array_fget_borrowed(v_haveInfo_1721_, v_i_1675_);
v_decl_1747_ = lean_ctor_get(v_hinfo_1746_, 2);
v_level_1748_ = lean_ctor_get(v_hinfo_1746_, 3);
lean_inc_ref(v_decl_1747_);
v_x_1749_ = l_Lean_LocalDecl_toExpr(v_decl_1747_);
v_val_1750_ = l_Lean_LocalDecl_value(v_decl_1747_, v___x_1729_);
v___x_1751_ = lean_box(0);
lean_inc(v_level_1724_);
v___x_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_level_1724_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
lean_inc_ref(v___x_1752_);
lean_inc(v_level_1748_);
v_us_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1753_, 0, v_level_1748_);
lean_ctor_set(v_us_1753_, 1, v___x_1752_);
v___x_1781_ = lean_array_get_size(v_used_1673_);
v___x_1782_ = lean_nat_dec_lt(v_i_1675_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_inc_ref(v_decl_1747_);
goto v___jp_1765_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_array_fget_borrowed(v_used_1673_, v_i_1675_);
v___x_1784_ = lean_unbox(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___f_1786_; lean_object* v_cls_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_x_1749_);
lean_dec(v___x_1737_);
v___x_1785_ = lean_box(v___x_1729_);
lean_inc(v_toBind_1725_);
lean_inc(v_inst_1668_);
lean_inc(v_declName_1742_);
v___f_1786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1786_, 0, v___x_1751_);
lean_closure_set(v___f_1786_, 1, v_declName_1742_);
lean_closure_set(v___f_1786_, 2, v_type_1743_);
lean_closure_set(v___f_1786_, 3, v_value_1744_);
lean_closure_set(v___f_1786_, 4, v_us_1753_);
lean_closure_set(v___f_1786_, 5, v___x_1752_);
lean_closure_set(v___f_1786_, 6, v___x_1785_);
lean_closure_set(v___f_1786_, 7, v_toPure_1726_);
lean_closure_set(v___f_1786_, 8, v_i_1675_);
lean_closure_set(v___f_1786_, 9, v_xs_1676_);
lean_closure_set(v___f_1786_, 10, v_inst_1667_);
lean_closure_set(v___f_1786_, 11, v_inst_1668_);
lean_closure_set(v___f_1786_, 12, v_inst_1669_);
lean_closure_set(v___f_1786_, 13, v_inst_1670_);
lean_closure_set(v___f_1786_, 14, v_info_1671_);
lean_closure_set(v___f_1786_, 15, v_fixed_1672_);
lean_closure_set(v___f_1786_, 16, v_used_1673_);
lean_closure_set(v___f_1786_, 17, v_body_1745_);
lean_closure_set(v___f_1786_, 18, v_toBind_1725_);
v_cls_1787_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1720_);
v___f_1788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1788_, 0, v_cls_1787_);
lean_closure_set(v___f_1788_, 1, v_declName_1742_);
lean_closure_set(v___f_1788_, 2, v_val_1750_);
lean_closure_set(v___f_1788_, 3, v___x_1716_);
lean_closure_set(v___f_1788_, 4, v___x_1717_);
lean_closure_set(v___f_1788_, 5, v_toMonadRef_1720_);
lean_closure_set(v___f_1788_, 6, v___x_1727_);
v___x_1789_ = lean_apply_2(v_inst_1668_, lean_box(0), v___f_1788_);
v___x_1790_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1789_, v___f_1786_);
return v___x_1790_;
}
else
{
lean_inc_ref(v_decl_1747_);
goto v___jp_1765_;
}
}
v___jp_1754_:
{
lean_object* v_withNewLemmas_1757_; lean_object* v_dsimp_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_withNewLemmas_1757_ = lean_ctor_get(v_inst_1670_, 0);
lean_inc(v_withNewLemmas_1757_);
v_dsimp_1758_ = lean_ctor_get(v_inst_1670_, 1);
lean_inc(v_dsimp_1758_);
v___x_1759_ = lean_box(v___y_1756_);
v___x_1760_ = lean_box(v___x_1729_);
v___x_1761_ = lean_box(v___y_1755_);
lean_inc_ref(v_toMonadRef_1720_);
lean_inc_ref(v_val_1750_);
lean_inc(v_toBind_1725_);
v___f_1762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 29, 28);
lean_closure_set(v___f_1762_, 0, v_declName_1742_);
lean_closure_set(v___f_1762_, 1, v_type_1743_);
lean_closure_set(v___f_1762_, 2, v_value_1744_);
lean_closure_set(v___f_1762_, 3, v___x_1759_);
lean_closure_set(v___f_1762_, 4, v___x_1752_);
lean_closure_set(v___f_1762_, 5, v_toPure_1726_);
lean_closure_set(v___f_1762_, 6, v_us_1753_);
lean_closure_set(v___f_1762_, 7, v___x_1760_);
lean_closure_set(v___f_1762_, 8, v_decl_1747_);
lean_closure_set(v___f_1762_, 9, v_x_1749_);
lean_closure_set(v___f_1762_, 10, v_i_1675_);
lean_closure_set(v___f_1762_, 11, v_xs_1676_);
lean_closure_set(v___f_1762_, 12, v_inst_1667_);
lean_closure_set(v___f_1762_, 13, v_inst_1668_);
lean_closure_set(v___f_1762_, 14, v_inst_1669_);
lean_closure_set(v___f_1762_, 15, v_inst_1670_);
lean_closure_set(v___f_1762_, 16, v_info_1671_);
lean_closure_set(v___f_1762_, 17, v_fixed_1672_);
lean_closure_set(v___f_1762_, 18, v_used_1673_);
lean_closure_set(v___f_1762_, 19, v_body_1745_);
lean_closure_set(v___f_1762_, 20, v_toBind_1725_);
lean_closure_set(v___f_1762_, 21, v_withNewLemmas_1757_);
lean_closure_set(v___f_1762_, 22, v_val_1750_);
lean_closure_set(v___f_1762_, 23, v___x_1761_);
lean_closure_set(v___f_1762_, 24, v___x_1716_);
lean_closure_set(v___f_1762_, 25, v___x_1717_);
lean_closure_set(v___f_1762_, 26, v_toMonadRef_1720_);
lean_closure_set(v___f_1762_, 27, v___x_1727_);
v___x_1763_ = lean_apply_1(v_dsimp_1758_, v_val_1750_);
v___x_1764_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1763_, v___f_1762_);
return v___x_1764_;
}
v___jp_1765_:
{
uint8_t v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = 0;
v___x_1767_ = lean_array_get_size(v_fixed_1672_);
v___x_1768_ = lean_nat_dec_lt(v_i_1675_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec(v___x_1737_);
v___y_1755_ = v___x_1766_;
v___y_1756_ = v___x_1729_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_array_fget_borrowed(v_fixed_1672_, v_i_1675_);
v___x_1770_ = lean_unbox(v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v_withNewLemmas_1771_; lean_object* v_simp_1772_; lean_object* v___x_1773_; lean_object* v___f_1774_; lean_object* v___f_1775_; lean_object* v___x_1776_; lean_object* v___f_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_inc_n(v___x_1769_, 2);
lean_inc(v_level_1748_);
v_withNewLemmas_1771_ = lean_ctor_get(v_inst_1670_, 0);
lean_inc(v_withNewLemmas_1771_);
v_simp_1772_ = lean_ctor_get(v_inst_1670_, 2);
lean_inc(v_simp_1772_);
v___x_1773_ = lean_box(v___x_1729_);
lean_inc_n(v_toBind_1725_, 2);
lean_inc(v_inst_1668_);
lean_inc_ref(v_xs_1676_);
lean_inc(v_toPure_1726_);
lean_inc_ref(v_value_1744_);
lean_inc_ref(v_type_1743_);
lean_inc(v_declName_1742_);
v___f_1774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 24, 23);
lean_closure_set(v___f_1774_, 0, v_decl_1747_);
lean_closure_set(v___f_1774_, 1, v_declName_1742_);
lean_closure_set(v___f_1774_, 2, v_type_1743_);
lean_closure_set(v___f_1774_, 3, v_value_1744_);
lean_closure_set(v___f_1774_, 4, v___x_1773_);
lean_closure_set(v___f_1774_, 5, v___x_1752_);
lean_closure_set(v___f_1774_, 6, v___x_1769_);
lean_closure_set(v___f_1774_, 7, v_toPure_1726_);
lean_closure_set(v___f_1774_, 8, v_us_1753_);
lean_closure_set(v___f_1774_, 9, v___x_1737_);
lean_closure_set(v___f_1774_, 10, v_x_1749_);
lean_closure_set(v___f_1774_, 11, v_i_1675_);
lean_closure_set(v___f_1774_, 12, v_xs_1676_);
lean_closure_set(v___f_1774_, 13, v_inst_1667_);
lean_closure_set(v___f_1774_, 14, v_inst_1668_);
lean_closure_set(v___f_1774_, 15, v_inst_1669_);
lean_closure_set(v___f_1774_, 16, v_inst_1670_);
lean_closure_set(v___f_1774_, 17, v_info_1671_);
lean_closure_set(v___f_1774_, 18, v_fixed_1672_);
lean_closure_set(v___f_1774_, 19, v_used_1673_);
lean_closure_set(v___f_1774_, 20, v_body_1745_);
lean_closure_set(v___f_1774_, 21, v_toBind_1725_);
lean_closure_set(v___f_1774_, 22, v_withNewLemmas_1771_);
v___f_1775_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1775_, 0, v___f_1774_);
v___x_1776_ = lean_box(v___x_1729_);
lean_inc_ref(v_toMonadRef_1720_);
lean_inc_ref(v_val_1750_);
lean_inc_ref(v___f_1775_);
v___f_1777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_1777_, 0, v_level_1748_);
lean_closure_set(v___f_1777_, 1, v___x_1751_);
lean_closure_set(v___f_1777_, 2, v_type_1743_);
lean_closure_set(v___f_1777_, 3, v_value_1744_);
lean_closure_set(v___f_1777_, 4, v___x_1769_);
lean_closure_set(v___f_1777_, 5, v_toPure_1726_);
lean_closure_set(v___f_1777_, 6, v_toBind_1725_);
lean_closure_set(v___f_1777_, 7, v___f_1775_);
lean_closure_set(v___f_1777_, 8, v_xs_1676_);
lean_closure_set(v___f_1777_, 9, v___x_1776_);
lean_closure_set(v___f_1777_, 10, v___f_1775_);
lean_closure_set(v___f_1777_, 11, v_declName_1742_);
lean_closure_set(v___f_1777_, 12, v_val_1750_);
lean_closure_set(v___f_1777_, 13, v___x_1716_);
lean_closure_set(v___f_1777_, 14, v___x_1717_);
lean_closure_set(v___f_1777_, 15, v_toMonadRef_1720_);
lean_closure_set(v___f_1777_, 16, v___x_1727_);
lean_closure_set(v___f_1777_, 17, v_inst_1668_);
v___x_1778_ = lean_apply_1(v_simp_1772_, v_val_1750_);
v___x_1779_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1778_, v___f_1777_);
return v___x_1779_;
}
else
{
uint8_t v___x_1780_; 
lean_dec(v___x_1737_);
v___x_1780_ = lean_unbox(v___x_1769_);
v___y_1755_ = v___x_1766_;
v___y_1756_ = v___x_1780_;
goto v___jp_1754_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1674_, 4);
lean_dec(v_toPure_1726_);
lean_dec(v_toBind_1725_);
lean_dec_ref(v___x_1716_);
lean_dec_ref(v_xs_1676_);
lean_dec(v_i_1675_);
lean_dec_ref(v_used_1673_);
lean_dec_ref(v_fixed_1672_);
lean_dec_ref(v_info_1671_);
lean_dec_ref(v_inst_1670_);
lean_dec_ref(v_inst_1669_);
lean_dec(v_inst_1668_);
lean_dec_ref(v_inst_1667_);
goto v___jp_1738_;
}
}
else
{
lean_dec(v_toPure_1726_);
lean_dec(v_toBind_1725_);
lean_dec_ref(v___x_1716_);
lean_dec_ref(v_xs_1676_);
lean_dec(v_i_1675_);
lean_dec_ref(v_e_1674_);
lean_dec_ref(v_used_1673_);
lean_dec_ref(v_fixed_1672_);
lean_dec_ref(v_info_1671_);
lean_dec_ref(v_inst_1670_);
lean_dec_ref(v_inst_1669_);
lean_dec(v_inst_1668_);
lean_dec_ref(v_inst_1667_);
goto v___jp_1738_;
}
v___jp_1738_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15);
v___x_1740_ = l_panic___redArg(v___x_1737_, v___x_1739_);
lean_dec(v___x_1737_);
return v___x_1740_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1797_, lean_object* v_declName_1798_, lean_object* v_type_1799_, lean_object* v_value_1800_, lean_object* v_us_1801_, lean_object* v___x_1802_, uint8_t v___x_1803_, lean_object* v_toPure_1804_, lean_object* v_i_1805_, lean_object* v_xs_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_info_1811_, lean_object* v_fixed_1812_, lean_object* v_used_1813_, lean_object* v_body_1814_, lean_object* v_toBind_1815_, lean_object* v_____r_1816_){
_start:
{
lean_object* v___x_1817_; lean_object* v_x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1818_ = l_Lean_mkConst(v___x_1817_, v___x_1797_);
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = lean_box(v___x_1803_);
v___f_1821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1821_, 0, v___x_1819_);
lean_closure_set(v___f_1821_, 1, v_declName_1798_);
lean_closure_set(v___f_1821_, 2, v_type_1799_);
lean_closure_set(v___f_1821_, 3, v_value_1800_);
lean_closure_set(v___f_1821_, 4, v_us_1801_);
lean_closure_set(v___f_1821_, 5, v___x_1802_);
lean_closure_set(v___f_1821_, 6, v___x_1820_);
lean_closure_set(v___f_1821_, 7, v_toPure_1804_);
v___x_1822_ = lean_nat_add(v_i_1805_, v___x_1819_);
v___x_1823_ = lean_array_push(v_xs_1806_, v_x_1818_);
v___x_1824_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1807_, v_inst_1808_, v_inst_1809_, v_inst_1810_, v_info_1811_, v_fixed_1812_, v_used_1813_, v_body_1814_, v___x_1822_, v___x_1823_);
v___x_1825_ = lean_apply_4(v_toBind_1815_, lean_box(0), lean_box(0), v___x_1824_, v___f_1821_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_info_1831_, lean_object* v_fixed_1832_, lean_object* v_used_1833_, lean_object* v_e_1834_, lean_object* v_i_1835_, lean_object* v_xs_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1827_, v_inst_1828_, v_inst_1829_, v_inst_1830_, v_info_1831_, v_fixed_1832_, v_used_1833_, v_e_1834_, v_i_1835_, v_xs_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl(uint8_t v_x_1838_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_box(v_x_1838_);
v___x_1840_ = lean_obj_tag_nat(v___x_1839_);
lean_dec(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl___boxed(lean_object* v_x_1841_){
_start:
{
uint8_t v_x_4__boxed_1842_; lean_object* v_res_1843_; 
v_x_4__boxed_1842_ = lean_unbox(v_x_1841_);
v_res_1843_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl(v_x_4__boxed_1842_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_1844_){
_start:
{
lean_inc(v_k_1844_);
return v_k_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_1845_);
lean_dec(v_k_1845_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_1847_, lean_object* v_ctorIdx_1848_, uint8_t v_t_1849_, lean_object* v_h_1850_, lean_object* v_k_1851_){
_start:
{
lean_inc(v_k_1851_);
return v_k_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_1852_, lean_object* v_ctorIdx_1853_, lean_object* v_t_1854_, lean_object* v_h_1855_, lean_object* v_k_1856_){
_start:
{
uint8_t v_t_boxed_1857_; lean_object* v_res_1858_; 
v_t_boxed_1857_ = lean_unbox(v_t_1854_);
v_res_1858_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_1852_, v_ctorIdx_1853_, v_t_boxed_1857_, v_h_1855_, v_k_1856_);
lean_dec(v_k_1856_);
lean_dec(v_ctorIdx_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_1859_){
_start:
{
lean_inc(v_no_1859_);
return v_no_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_1860_);
lean_dec(v_no_1860_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_1862_, uint8_t v_t_1863_, lean_object* v_h_1864_, lean_object* v_no_1865_){
_start:
{
lean_inc(v_no_1865_);
return v_no_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_1866_, lean_object* v_t_1867_, lean_object* v_h_1868_, lean_object* v_no_1869_){
_start:
{
uint8_t v_t_boxed_1870_; lean_object* v_res_1871_; 
v_t_boxed_1870_ = lean_unbox(v_t_1867_);
v_res_1871_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_1866_, v_t_boxed_1870_, v_h_1868_, v_no_1869_);
lean_dec(v_no_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_1872_){
_start:
{
lean_inc(v_singlePass_1872_);
return v_singlePass_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_1873_);
lean_dec(v_singlePass_1873_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_1875_, uint8_t v_t_1876_, lean_object* v_h_1877_, lean_object* v_singlePass_1878_){
_start:
{
lean_inc(v_singlePass_1878_);
return v_singlePass_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_1879_, lean_object* v_t_1880_, lean_object* v_h_1881_, lean_object* v_singlePass_1882_){
_start:
{
uint8_t v_t_boxed_1883_; lean_object* v_res_1884_; 
v_t_boxed_1883_ = lean_unbox(v_t_1880_);
v_res_1884_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_1879_, v_t_boxed_1883_, v_h_1881_, v_singlePass_1882_);
lean_dec(v_singlePass_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_1885_){
_start:
{
lean_inc(v_twoPasses_1885_);
return v_twoPasses_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_1886_);
lean_dec(v_twoPasses_1886_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_1888_, uint8_t v_t_1889_, lean_object* v_h_1890_, lean_object* v_twoPasses_1891_){
_start:
{
lean_inc(v_twoPasses_1891_);
return v_twoPasses_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_1892_, lean_object* v_t_1893_, lean_object* v_h_1894_, lean_object* v_twoPasses_1895_){
_start:
{
uint8_t v_t_boxed_1896_; lean_object* v_res_1897_; 
v_t_boxed_1896_ = lean_unbox(v_t_1893_);
v_res_1897_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_1892_, v_t_boxed_1896_, v_h_1894_, v_twoPasses_1895_);
lean_dec(v_twoPasses_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_1898_, lean_object* v_b_1899_, lean_object* v_c_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1901_);
v___x_1906_ = lean_apply_7(v_k_1898_, v_b_1899_, v_c_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, lean_box(0));
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_1907_, lean_object* v_b_1908_, lean_object* v_c_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_1907_, v_b_1908_, v_c_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_1916_, lean_object* v_k_1917_, uint8_t v_cleanupAnnotations_1918_, uint8_t v_preserveNondepLet_1919_, uint8_t v_nondepLetOnly_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___f_1926_; uint8_t v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1926_, 0, v_k_1917_);
v___x_1927_ = 0;
v___x_1928_ = 1;
v___x_1929_ = lean_box(0);
v___x_1930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1916_, v___x_1927_, v___x_1928_, v_preserveNondepLet_1919_, v_nondepLetOnly_1920_, v___x_1929_, v___f_1926_, v_cleanupAnnotations_1918_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1930_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1930_);
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
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_1947_, lean_object* v_k_1948_, lean_object* v_cleanupAnnotations_1949_, lean_object* v_preserveNondepLet_1950_, lean_object* v_nondepLetOnly_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1957_; uint8_t v_preserveNondepLet_boxed_1958_; uint8_t v_nondepLetOnly_boxed_1959_; lean_object* v_res_1960_; 
v_cleanupAnnotations_boxed_1957_ = lean_unbox(v_cleanupAnnotations_1949_);
v_preserveNondepLet_boxed_1958_ = lean_unbox(v_preserveNondepLet_1950_);
v_nondepLetOnly_boxed_1959_ = lean_unbox(v_nondepLetOnly_1951_);
v_res_1960_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1947_, v_k_1948_, v_cleanupAnnotations_boxed_1957_, v_preserveNondepLet_boxed_1958_, v_nondepLetOnly_boxed_1959_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_1961_, lean_object* v_e_1962_, lean_object* v_k_1963_, uint8_t v_cleanupAnnotations_1964_, uint8_t v_preserveNondepLet_1965_, uint8_t v_nondepLetOnly_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1962_, v_k_1963_, v_cleanupAnnotations_1964_, v_preserveNondepLet_1965_, v_nondepLetOnly_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_e_1974_, lean_object* v_k_1975_, lean_object* v_cleanupAnnotations_1976_, lean_object* v_preserveNondepLet_1977_, lean_object* v_nondepLetOnly_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1984_; uint8_t v_preserveNondepLet_boxed_1985_; uint8_t v_nondepLetOnly_boxed_1986_; lean_object* v_res_1987_; 
v_cleanupAnnotations_boxed_1984_ = lean_unbox(v_cleanupAnnotations_1976_);
v_preserveNondepLet_boxed_1985_ = lean_unbox(v_preserveNondepLet_1977_);
v_nondepLetOnly_boxed_1986_ = lean_unbox(v_nondepLetOnly_1978_);
v_res_1987_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_1973_, v_e_1974_, v_k_1975_, v_cleanupAnnotations_boxed_1984_, v_preserveNondepLet_boxed_1985_, v_nondepLetOnly_boxed_1986_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_1988_, lean_object* v_a_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_snd_1994_; lean_object* v_fst_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2050_; 
v_snd_1994_ = lean_ctor_get(v_a_1989_, 1);
v_fst_1995_ = lean_ctor_get(v_a_1989_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_a_1989_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_1997_ = v_a_1989_;
v_isShared_1998_ = v_isSharedCheck_2050_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1995_);
lean_dec(v_a_1989_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2050_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_fst_1999_; lean_object* v_snd_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2049_; 
v_fst_1999_ = lean_ctor_get(v_snd_1994_, 0);
v_snd_2000_ = lean_ctor_get(v_snd_1994_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_snd_1994_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2002_ = v_snd_1994_;
v_isShared_2003_ = v_isSharedCheck_2049_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_2000_);
lean_inc(v_fst_1999_);
lean_dec(v_snd_1994_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2049_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = lean_nat_dec_lt(v___x_2004_, v_snd_2000_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2007_; 
if (v_isShared_2003_ == 0)
{
v___x_2007_ = v___x_2002_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_fst_1999_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_snd_2000_);
v___x_2007_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2007_);
v___x_2009_ = v___x_1997_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_fst_1995_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
}
else
{
lean_object* v_fvarSet_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_fvarSet_2013_ = lean_ctor_get(v_fst_1995_, 1);
v___x_2014_ = l_Lean_instInhabitedExpr;
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_sub(v_snd_2000_, v___x_2015_);
lean_dec(v_snd_2000_);
v___x_2017_ = lean_array_get_borrowed(v___x_2014_, v_xs_1988_, v___x_2016_);
v___x_2018_ = l_Lean_Expr_fvarId_x21(v___x_2017_);
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2018_, v_fvarSet_2013_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v___x_2018_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2016_);
v___x_2021_ = v___x_2002_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_fst_1999_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2016_);
v___x_2021_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2021_);
v___x_2023_ = v___x_1997_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fst_1995_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
v_a_1989_ = v___x_2023_;
goto _start;
}
}
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_FVarId_getDecl___redArg(v___x_2018_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = l_Lean_LocalDecl_type(v_a_2028_);
v___x_2030_ = l_Lean_collectFVars(v_fst_1995_, v___x_2029_);
v___x_2031_ = l_Lean_LocalDecl_value(v_a_2028_, v___x_2005_);
lean_dec(v_a_2028_);
v___x_2032_ = l_Lean_collectFVars(v___x_2030_, v___x_2031_);
lean_inc(v___x_2017_);
v___x_2033_ = lean_array_push(v_fst_1999_, v___x_2017_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2016_);
lean_ctor_set(v___x_2002_, 0, v___x_2033_);
v___x_2035_ = v___x_2002_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2016_);
v___x_2035_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2035_);
lean_ctor_set(v___x_1997_, 0, v___x_2032_);
v___x_2037_ = v___x_1997_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v_a_1989_ = v___x_2037_;
goto _start;
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v___x_2016_);
lean_del_object(v___x_2002_);
lean_dec(v_fst_1999_);
lean_del_object(v___x_1997_);
lean_dec(v_fst_1995_);
v_a_2041_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2027_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2027_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2051_, lean_object* v_a_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2051_, v_a_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_xs_2051_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v_e_2058_, lean_object* v_xs_2059_, lean_object* v_body_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_s_2068_; lean_object* v_i_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0));
v___x_2067_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
lean_inc_ref(v_body_2060_);
v_s_2068_ = l_Lean_collectFVars(v___x_2067_, v_body_2060_);
v_i_2069_ = lean_array_get_size(v_xs_2059_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2066_);
lean_ctor_set(v___x_2070_, 1, v_i_2069_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_s_2068_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2059_, v___x_2071_, v___y_2061_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2088_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2088_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2088_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_snd_2077_; lean_object* v_fst_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_snd_2077_ = lean_ctor_get(v_a_2073_, 1);
lean_inc(v_snd_2077_);
lean_dec(v_a_2073_);
v_fst_2078_ = lean_ctor_get(v_snd_2077_, 0);
lean_inc(v_fst_2078_);
lean_dec(v_snd_2077_);
v___x_2079_ = lean_array_get_size(v_fst_2078_);
v___x_2080_ = lean_nat_dec_eq(v___x_2079_, v_i_2069_);
if (v___x_2080_ == 0)
{
uint8_t v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; 
lean_del_object(v___x_2075_);
lean_dec_ref(v_e_2058_);
v___x_2081_ = 1;
v___x_2082_ = l_Array_reverse___redArg(v_fst_2078_);
v___x_2083_ = 1;
v___x_2084_ = l_Lean_Meta_mkLetFVars(v___x_2082_, v_body_2060_, v___x_2081_, v___x_2080_, v___x_2083_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec_ref(v___x_2082_);
return v___x_2084_;
}
else
{
lean_object* v___x_2086_; 
lean_dec(v_fst_2078_);
lean_dec_ref(v_body_2060_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v_e_2058_);
v___x_2086_ = v___x_2075_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_e_2058_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_body_2060_);
lean_dec_ref(v_e_2058_);
v_a_2089_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2072_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2072_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v_e_2097_, lean_object* v_xs_2098_, lean_object* v_body_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Meta_zetaUnused___lam__0(v_e_2097_, v_xs_2098_, v_body_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec_ref(v_xs_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___f_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
lean_inc_ref(v_e_2106_);
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2112_, 0, v_e_2106_);
v___x_2113_ = 0;
v___x_2114_ = 1;
v___x_2115_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2106_, v___f_2112_, v___x_2113_, v___x_2114_, v___x_2113_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Meta_zetaUnused(v_e_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2123_, lean_object* v_inst_2124_, lean_object* v_a_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2123_, v_a_2125_, v___y_2126_, v___y_2128_, v___y_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2132_, lean_object* v_inst_2133_, lean_object* v_a_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2132_, v_inst_2133_, v_a_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v_xs_2132_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2145_, lean_object* v_source_2146_, lean_object* v_result_2147_, uint8_t v_keepUnused_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
uint8_t v_modified_2154_; 
v_modified_2154_ = lean_ctor_get_uint8(v_result_2147_, sizeof(void*)*5);
if (v_modified_2154_ == 0)
{
if (v_keepUnused_2148_ == 0)
{
lean_object* v_exprType_2155_; lean_object* v___x_2156_; 
v_exprType_2155_ = lean_ctor_get(v_result_2147_, 1);
lean_inc_ref(v_exprType_2155_);
lean_dec_ref(v_result_2147_);
lean_inc_ref(v_source_2146_);
v___x_2156_ = l_Lean_Meta_zetaUnused(v_source_2146_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2175_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2175_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2175_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_expr_eqv(v_a_2157_, v_source_2146_);
lean_dec_ref(v_source_2146_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_u_2145_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_mkConst(v___x_2162_, v___x_2164_);
lean_inc(v_a_2157_);
v___x_2166_ = l_Lean_mkAppB(v___x_2165_, v_exprType_2155_, v_a_2157_);
v___x_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_a_2157_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2167_);
v___x_2169_ = v___x_2159_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec(v_a_2157_);
lean_dec_ref(v_exprType_2155_);
lean_dec(v_u_2145_);
v___x_2171_ = lean_box(0);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2171_);
v___x_2173_ = v___x_2159_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_exprType_2155_);
lean_dec_ref(v_source_2146_);
lean_dec(v_u_2145_);
v_a_2176_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2156_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2156_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v_result_2147_);
lean_dec_ref(v_source_2146_);
lean_dec(v_u_2145_);
v___x_2184_ = lean_box(0);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
else
{
lean_object* v_expr_2186_; lean_object* v_exprType_2187_; lean_object* v_exprInit_2188_; lean_object* v_exprResult_2189_; lean_object* v_proof_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_proof_2198_; 
v_expr_2186_ = lean_ctor_get(v_result_2147_, 0);
lean_inc_ref(v_expr_2186_);
v_exprType_2187_ = lean_ctor_get(v_result_2147_, 1);
lean_inc_ref_n(v_exprType_2187_, 3);
v_exprInit_2188_ = lean_ctor_get(v_result_2147_, 2);
lean_inc_ref(v_exprInit_2188_);
v_exprResult_2189_ = lean_ctor_get(v_result_2147_, 3);
lean_inc_ref_n(v_exprResult_2189_, 2);
v_proof_2190_ = lean_ctor_get(v_result_2147_, 4);
lean_inc_ref(v_proof_2190_);
lean_dec_ref(v_result_2147_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_u_2145_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
lean_inc_ref(v___x_2193_);
v___x_2194_ = l_Lean_mkConst(v___x_2191_, v___x_2193_);
lean_inc_ref(v___x_2194_);
v___x_2195_ = l_Lean_mkApp3(v___x_2194_, v_exprType_2187_, v_exprInit_2188_, v_expr_2186_);
v___x_2196_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2190_, v___x_2195_);
lean_inc_ref(v_source_2146_);
v___x_2197_ = l_Lean_mkApp3(v___x_2194_, v_exprType_2187_, v_source_2146_, v_exprResult_2189_);
v_proof_2198_ = l_Lean_Meta_mkExpectedPropHint(v___x_2196_, v___x_2197_);
if (v_keepUnused_2148_ == 0)
{
lean_object* v___x_2199_; 
lean_inc_ref(v_exprResult_2189_);
v___x_2199_ = l_Lean_Meta_zetaUnused(v_exprResult_2189_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2219_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2219_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2219_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_expr_eqv(v_a_2200_, v_exprResult_2189_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2193_);
v___x_2206_ = l_Lean_mkConst(v___x_2205_, v___x_2193_);
v___x_2207_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2208_ = l_Lean_mkConst(v___x_2207_, v___x_2193_);
lean_inc_n(v_a_2200_, 2);
lean_inc_ref(v_exprType_2187_);
v___x_2209_ = l_Lean_mkAppB(v___x_2208_, v_exprType_2187_, v_a_2200_);
v___x_2210_ = l_Lean_mkApp6(v___x_2206_, v_exprType_2187_, v_source_2146_, v_exprResult_2189_, v_a_2200_, v_proof_2198_, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_a_2200_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2211_);
v___x_2213_ = v___x_2202_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec(v_a_2200_);
lean_dec_ref_known(v___x_2193_, 2);
lean_dec_ref(v_exprType_2187_);
lean_dec_ref(v_source_2146_);
v___x_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_exprResult_2189_);
lean_ctor_set(v___x_2215_, 1, v_proof_2198_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2215_);
v___x_2217_ = v___x_2202_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_proof_2198_);
lean_dec_ref_known(v___x_2193_, 2);
lean_dec_ref(v_exprResult_2189_);
lean_dec_ref(v_exprType_2187_);
lean_dec_ref(v_source_2146_);
v_a_2220_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2199_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2199_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref_known(v___x_2193_, 2);
lean_dec_ref(v_exprType_2187_);
lean_dec_ref(v_source_2146_);
v___x_2228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_exprResult_2189_);
lean_ctor_set(v___x_2228_, 1, v_proof_2198_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2230_, lean_object* v_source_2231_, lean_object* v_result_2232_, lean_object* v_keepUnused_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
uint8_t v_keepUnused_boxed_2239_; lean_object* v_res_2240_; 
v_keepUnused_boxed_2239_ = lean_unbox(v_keepUnused_2233_);
v_res_2240_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2230_, v_source_2231_, v_result_2232_, v_keepUnused_boxed_2239_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2241_, lean_object* v_e_2242_, lean_object* v_inst_2243_, uint8_t v_zetaUnusedMode_2244_, uint8_t v___x_2245_, uint8_t v___x_2246_, lean_object* v_r_2247_){
_start:
{
uint8_t v___y_2249_; 
switch(v_zetaUnusedMode_2244_)
{
case 0:
{
v___y_2249_ = v___x_2245_;
goto v___jp_2248_;
}
case 1:
{
v___y_2249_ = v___x_2245_;
goto v___jp_2248_;
}
default: 
{
v___y_2249_ = v___x_2246_;
goto v___jp_2248_;
}
}
v___jp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_box(v___y_2249_);
v___x_2251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2251_, 0, v_level_2241_);
lean_closure_set(v___x_2251_, 1, v_e_2242_);
lean_closure_set(v___x_2251_, 2, v_r_2247_);
lean_closure_set(v___x_2251_, 3, v___x_2250_);
v___x_2252_ = lean_apply_2(v_inst_2243_, lean_box(0), v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2253_, lean_object* v_e_2254_, lean_object* v_inst_2255_, lean_object* v_zetaUnusedMode_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v_r_2259_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2260_; uint8_t v___x_289__boxed_2261_; uint8_t v___x_290__boxed_2262_; lean_object* v_res_2263_; 
v_zetaUnusedMode_boxed_2260_ = lean_unbox(v_zetaUnusedMode_2256_);
v___x_289__boxed_2261_ = lean_unbox(v___x_2257_);
v___x_290__boxed_2262_ = lean_unbox(v___x_2258_);
v_res_2263_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2253_, v_e_2254_, v_inst_2255_, v_zetaUnusedMode_boxed_2260_, v___x_289__boxed_2261_, v___x_290__boxed_2262_, v_r_2259_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_info_2269_, lean_object* v_e_2270_, lean_object* v___x_2271_, lean_object* v_toBind_2272_, lean_object* v___f_2273_, lean_object* v_____x_2274_){
_start:
{
lean_object* v_fst_2275_; lean_object* v_snd_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_fst_2275_ = lean_ctor_get(v_____x_2274_, 0);
lean_inc(v_fst_2275_);
v_snd_2276_ = lean_ctor_get(v_____x_2274_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v_____x_2274_);
v___x_2277_ = lean_mk_empty_array_with_capacity(v___x_2264_);
v___x_2278_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2265_, v_inst_2266_, v_inst_2267_, v_inst_2268_, v_info_2269_, v_fst_2275_, v_snd_2276_, v_e_2270_, v___x_2271_, v___x_2277_);
v___x_2279_ = lean_apply_4(v_toBind_2272_, lean_box(0), lean_box(0), v___x_2278_, v___f_2273_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_info_2285_, lean_object* v_e_2286_, lean_object* v___x_2287_, lean_object* v_toBind_2288_, lean_object* v___f_2289_, lean_object* v_____x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2280_, v_inst_2281_, v_inst_2282_, v_inst_2283_, v_inst_2284_, v_info_2285_, v_e_2286_, v___x_2287_, v_toBind_2288_, v___f_2289_, v_____x_2290_);
lean_dec(v___x_2280_);
return v_res_2291_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2294_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2295_ = lean_unsigned_to_nat(2u);
v___x_2296_ = lean_unsigned_to_nat(456u);
v___x_2297_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2298_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2299_ = l_mkPanicMessageWithDecl(v___x_2298_, v___x_2297_, v___x_2296_, v___x_2295_, v___x_2294_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2300_, lean_object* v_inst_2301_, uint8_t v_zetaUnusedMode_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_toBind_2306_, lean_object* v___x_2307_, lean_object* v_info_2308_){
_start:
{
lean_object* v_haveInfo_2309_; lean_object* v_level_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_haveInfo_2309_ = lean_ctor_get(v_info_2308_, 0);
v_level_2310_ = lean_ctor_get(v_info_2308_, 5);
v___x_2311_ = lean_array_get_size(v_haveInfo_2309_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_nat_dec_eq(v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___f_2318_; lean_object* v___f_2319_; uint8_t v___y_2321_; 
v___x_2314_ = 1;
v___x_2315_ = lean_box(v_zetaUnusedMode_2302_);
v___x_2316_ = lean_box(v___x_2314_);
v___x_2317_ = lean_box(v___x_2313_);
lean_inc_n(v_inst_2301_, 2);
lean_inc_ref(v_e_2300_);
lean_inc(v_level_2310_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2318_, 0, v_level_2310_);
lean_closure_set(v___f_2318_, 1, v_e_2300_);
lean_closure_set(v___f_2318_, 2, v_inst_2301_);
lean_closure_set(v___f_2318_, 3, v___x_2315_);
lean_closure_set(v___f_2318_, 4, v___x_2316_);
lean_closure_set(v___f_2318_, 5, v___x_2317_);
lean_inc(v_toBind_2306_);
lean_inc_ref(v_info_2308_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2319_, 0, v___x_2311_);
lean_closure_set(v___f_2319_, 1, v_inst_2303_);
lean_closure_set(v___f_2319_, 2, v_inst_2301_);
lean_closure_set(v___f_2319_, 3, v_inst_2304_);
lean_closure_set(v___f_2319_, 4, v_inst_2305_);
lean_closure_set(v___f_2319_, 5, v_info_2308_);
lean_closure_set(v___f_2319_, 6, v_e_2300_);
lean_closure_set(v___f_2319_, 7, v___x_2312_);
lean_closure_set(v___f_2319_, 8, v_toBind_2306_);
lean_closure_set(v___f_2319_, 9, v___f_2318_);
switch(v_zetaUnusedMode_2302_)
{
case 0:
{
v___y_2321_ = v___x_2314_;
goto v___jp_2320_;
}
case 2:
{
v___y_2321_ = v___x_2314_;
goto v___jp_2320_;
}
default: 
{
v___y_2321_ = v___x_2313_;
goto v___jp_2320_;
}
}
v___jp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_box(v___y_2321_);
v___x_2323_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2323_, 0, v_info_2308_);
lean_closure_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = lean_apply_2(v_inst_2301_, lean_box(0), v___x_2323_);
v___x_2325_ = lean_apply_4(v_toBind_2306_, lean_box(0), lean_box(0), v___x_2324_, v___f_2319_);
return v___x_2325_;
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec_ref(v_info_2308_);
lean_dec(v_toBind_2306_);
lean_dec_ref(v_inst_2305_);
lean_dec_ref(v_inst_2304_);
lean_dec_ref(v_inst_2303_);
lean_dec(v_inst_2301_);
lean_dec_ref(v_e_2300_);
v___x_2326_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2327_ = l_panic___redArg(v___x_2307_, v___x_2326_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2328_, lean_object* v_inst_2329_, lean_object* v_zetaUnusedMode_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_toBind_2334_, lean_object* v___x_2335_, lean_object* v_info_2336_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2337_; lean_object* v_res_2338_; 
v_zetaUnusedMode_boxed_2337_ = lean_unbox(v_zetaUnusedMode_2330_);
v_res_2338_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2328_, v_inst_2329_, v_zetaUnusedMode_boxed_2337_, v_inst_2331_, v_inst_2332_, v_inst_2333_, v_toBind_2334_, v___x_2335_, v_info_2336_);
lean_dec(v___x_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_e_2343_, uint8_t v_zetaUnusedMode_2344_){
_start:
{
lean_object* v_toBind_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; 
v_toBind_2345_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2345_, 2);
v___x_2346_ = lean_box(0);
lean_inc_ref(v_e_2343_);
v___x_2347_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2347_, 0, v_e_2343_);
lean_inc(v_inst_2340_);
v___x_2348_ = lean_apply_2(v_inst_2340_, lean_box(0), v___x_2347_);
lean_inc_ref(v_inst_2339_);
v___x_2349_ = l_instInhabitedOfMonad___redArg(v_inst_2339_, v___x_2346_);
v___x_2350_ = lean_box(v_zetaUnusedMode_2344_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2351_, 0, v_e_2343_);
lean_closure_set(v___f_2351_, 1, v_inst_2340_);
lean_closure_set(v___f_2351_, 2, v___x_2350_);
lean_closure_set(v___f_2351_, 3, v_inst_2339_);
lean_closure_set(v___f_2351_, 4, v_inst_2341_);
lean_closure_set(v___f_2351_, 5, v_inst_2342_);
lean_closure_set(v___f_2351_, 6, v_toBind_2345_);
lean_closure_set(v___f_2351_, 7, v___x_2349_);
v___x_2352_ = lean_apply_4(v_toBind_2345_, lean_box(0), lean_box(0), v___x_2348_, v___f_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_e_2357_, lean_object* v_zetaUnusedMode_2358_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2359_; lean_object* v_res_2360_; 
v_zetaUnusedMode_boxed_2359_ = lean_unbox(v_zetaUnusedMode_2358_);
v_res_2360_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2353_, v_inst_2354_, v_inst_2355_, v_inst_2356_, v_e_2357_, v_zetaUnusedMode_boxed_2359_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_e_2366_, uint8_t v_zetaUnusedMode_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2362_, v_inst_2363_, v_inst_2364_, v_inst_2365_, v_e_2366_, v_zetaUnusedMode_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_e_2374_, lean_object* v_zetaUnusedMode_2375_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2376_; lean_object* v_res_2377_; 
v_zetaUnusedMode_boxed_2376_ = lean_unbox(v_zetaUnusedMode_2375_);
v_res_2377_ = l_Lean_Meta_simpHaveTelescope(v_m_2369_, v_inst_2370_, v_inst_2371_, v_inst_2372_, v_inst_2373_, v_e_2374_, v_zetaUnusedMode_boxed_2376_);
return v_res_2377_;
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
