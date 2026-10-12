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
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(lean_object* v_lctx_30_, lean_object* v_x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
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
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v___y_34_ = stack[4].m_obj;
lean_object* v___y_35_ = stack[5].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_30_, v_x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg___boxed(lean_object* v_lctx_50_, lean_object* v_x_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_50_, v_x_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_object* v_00_u03b1_58_, lean_object* v_lctx_59_, lean_object* v_x_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_59_ = stack[1].m_obj;
lean_object* v_x_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v___y_63_ = stack[5].m_obj;
lean_object* v___y_64_ = stack[6].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5(lean_box(0), v_lctx_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
stack->m_obj
 = v_res_67_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
return v_x_77_;
}
else
{
lean_object* v_key_79_; lean_object* v_value_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_104_; 
v_key_79_ = lean_ctor_get(v_x_78_, 0);
v_value_80_ = lean_ctor_get(v_x_78_, 1);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_104_ == 0)
{
v___x_83_ = v_x_78_;
v_isShared_84_ = v_isSharedCheck_104_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_value_80_);
lean_inc(v_key_79_);
lean_dec(v_x_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_104_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v_fold_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_85_ = lean_array_get_size(v_x_77_);
v___x_86_ = lean_uint64_of_nat(v_key_79_);
v___x_87_ = 32ULL;
v___x_88_ = lean_uint64_shift_right(v___x_86_, v___x_87_);
v_fold_89_ = lean_uint64_xor(v___x_86_, v___x_88_);
v___x_90_ = 16ULL;
v___x_91_ = lean_uint64_shift_right(v_fold_89_, v___x_90_);
v___x_92_ = lean_uint64_xor(v_fold_89_, v___x_91_);
v___x_93_ = lean_uint64_to_usize(v___x_92_);
v___x_94_ = lean_usize_of_nat(v___x_85_);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_sub(v___x_94_, v___x_95_);
v___x_97_ = lean_usize_land(v___x_93_, v___x_96_);
v___x_98_ = lean_array_uget_borrowed(v_x_77_, v___x_97_);
lean_inc(v___x_98_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 2, v___x_98_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_key_79_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_value_80_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v___x_98_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = lean_array_uset(v_x_77_, v___x_97_, v___x_100_);
v_x_77_ = v___x_101_;
v_x_78_ = v_tail_81_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(lean_object* v_i_105_, lean_object* v_source_106_, lean_object* v_target_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_array_get_size(v_source_106_);
v___x_109_ = lean_nat_dec_lt(v_i_105_, v___x_108_);
if (v___x_109_ == 0)
{
lean_dec_ref(v_source_106_);
lean_dec(v_i_105_);
return v_target_107_;
}
else
{
lean_object* v_es_110_; lean_object* v___x_111_; lean_object* v_source_112_; lean_object* v_target_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_es_110_ = lean_array_fget(v_source_106_, v_i_105_);
v___x_111_ = lean_box(0);
v_source_112_ = lean_array_fset(v_source_106_, v_i_105_, v___x_111_);
v_target_113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_target_107_, v_es_110_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_i_105_, v___x_114_);
lean_dec(v_i_105_);
v_i_105_ = v___x_115_;
v_source_106_ = v_source_112_;
v_target_107_ = v_target_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(lean_object* v_data_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_nbuckets_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_118_ = lean_array_get_size(v_data_117_);
v___x_119_ = lean_unsigned_to_nat(2u);
v_nbuckets_120_ = lean_nat_mul(v___x_118_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_box(0);
v___x_123_ = lean_mk_array(v_nbuckets_120_, v___x_122_);
v___x_124_ = lean_array_propagate_mark(v_data_117_, v___x_123_);
v___x_125_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v___x_121_, v_data_117_, v___x_124_);
return v___x_125_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(lean_object* v_a_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
else
{
lean_object* v_key_129_; lean_object* v_tail_130_; uint8_t v___x_131_; 
v_key_129_ = lean_ctor_get(v_x_127_, 0);
v_tail_130_ = lean_ctor_get(v_x_127_, 2);
v___x_131_ = lean_nat_dec_eq(v_key_129_, v_a_126_);
if (v___x_131_ == 0)
{
v_x_127_ = v_tail_130_;
goto _start;
}
else
{
return v___x_131_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_126_ = stack[0].m_obj;
lean_object* v_x_127_ = stack[1].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_126_, v_x_127_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg___boxed(lean_object* v_a_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_134_, v_x_135_);
lean_dec(v_x_135_);
lean_dec(v_a_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(lean_object* v_m_138_, lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
lean_object* v_size_141_; lean_object* v_buckets_142_; lean_object* v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v_fold_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; lean_object* v_bkt_156_; uint8_t v___x_157_; 
v_size_141_ = lean_ctor_get(v_m_138_, 0);
v_buckets_142_ = lean_ctor_get(v_m_138_, 1);
v___x_143_ = lean_array_get_size(v_buckets_142_);
v___x_144_ = lean_uint64_of_nat(v_a_139_);
v___x_145_ = 32ULL;
v___x_146_ = lean_uint64_shift_right(v___x_144_, v___x_145_);
v_fold_147_ = lean_uint64_xor(v___x_144_, v___x_146_);
v___x_148_ = 16ULL;
v___x_149_ = lean_uint64_shift_right(v_fold_147_, v___x_148_);
v___x_150_ = lean_uint64_xor(v_fold_147_, v___x_149_);
v___x_151_ = lean_uint64_to_usize(v___x_150_);
v___x_152_ = lean_usize_of_nat(v___x_143_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_sub(v___x_152_, v___x_153_);
v___x_155_ = lean_usize_land(v___x_151_, v___x_154_);
v_bkt_156_ = lean_array_uget_borrowed(v_buckets_142_, v___x_155_);
v___x_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_139_, v_bkt_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_178_; 
lean_inc_ref(v_buckets_142_);
lean_inc(v_size_141_);
v_isSharedCheck_178_ = !lean_is_exclusive(v_m_138_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_179_ = lean_ctor_get(v_m_138_, 1);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_m_138_, 0);
lean_dec(v_unused_180_);
v___x_159_ = v_m_138_;
v_isShared_160_ = v_isSharedCheck_178_;
goto v_resetjp_158_;
}
else
{
lean_dec(v_m_138_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_178_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v_size_x27_162_; lean_object* v___x_163_; lean_object* v_buckets_x27_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v_size_x27_162_ = lean_nat_add(v_size_141_, v___x_161_);
lean_dec(v_size_141_);
lean_inc(v_bkt_156_);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v_a_139_);
lean_ctor_set(v___x_163_, 1, v_b_140_);
lean_ctor_set(v___x_163_, 2, v_bkt_156_);
v_buckets_x27_164_ = lean_array_uset(v_buckets_142_, v___x_155_, v___x_163_);
v___x_165_ = lean_unsigned_to_nat(4u);
v___x_166_ = lean_nat_mul(v_size_x27_162_, v___x_165_);
v___x_167_ = lean_unsigned_to_nat(3u);
v___x_168_ = lean_nat_div(v___x_166_, v___x_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_array_get_size(v_buckets_x27_164_);
v___x_170_ = lean_nat_dec_le(v___x_168_, v___x_169_);
lean_dec(v___x_168_);
if (v___x_170_ == 0)
{
lean_object* v_val_171_; lean_object* v___x_173_; 
v_val_171_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_buckets_x27_164_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_val_171_);
lean_ctor_set(v___x_159_, 0, v_size_x27_162_);
v___x_173_ = v___x_159_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_size_x27_162_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_val_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
else
{
lean_object* v___x_176_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_buckets_x27_164_);
lean_ctor_set(v___x_159_, 0, v_size_x27_162_);
v___x_176_ = v___x_159_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_size_x27_162_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_buckets_x27_164_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_dec(v_b_140_);
lean_dec(v_a_139_);
return v_m_138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(lean_object* v_numHaves_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
return v_x_182_;
}
else
{
lean_object* v_key_184_; lean_object* v_tail_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_key_184_ = lean_ctor_get(v_x_183_, 0);
v_tail_185_ = lean_ctor_get(v_x_183_, 2);
v___x_186_ = lean_nat_sub(v_numHaves_181_, v_key_184_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_sub(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_x_182_, v___x_188_, v___x_189_);
v_x_182_ = v___x_190_;
v_x_183_ = v_tail_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1___boxed(lean_object* v_numHaves_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_192_, v_x_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec(v_numHaves_192_);
return v_res_195_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(lean_object* v_numHaves_196_, lean_object* v_as_197_, size_t v_i_198_, size_t v_stop_199_, lean_object* v_b_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = lean_usize_dec_eq(v_i_198_, v_stop_199_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; size_t v___x_204_; size_t v___x_205_; 
v___x_202_ = lean_array_uget_borrowed(v_as_197_, v_i_198_);
v___x_203_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__1(v_numHaves_196_, v_b_200_, v___x_202_);
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_i_198_, v___x_204_);
v_i_198_ = v___x_205_;
v_b_200_ = v___x_203_;
goto _start;
}
else
{
return v_b_200_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numHaves_196_ = stack[0].m_obj;
lean_object* v_as_197_ = stack[1].m_obj;
size_t v_i_198_ = stack[2].m_num;
size_t v_stop_199_ = stack[3].m_num;
lean_object* v_b_200_ = stack[4].m_obj;
lean_object* v_res_207_;
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_196_, v_as_197_, v_i_198_, v_stop_199_, v_b_200_);
stack->m_obj
 = v_res_207_;
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
size_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; 
v___x_224_ = ((size_t)0ULL);
v___x_225_ = lean_usize_of_nat(v___x_222_);
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__2(v_numHaves_216_, v_buckets_221_, v___x_224_, v___x_225_, v___x_219_);
lean_dec_ref(v_buckets_221_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0___boxed(lean_object* v_numHaves_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_227_, v_a_228_);
lean_dec(v_numHaves_227_);
return v_res_229_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(lean_object* v_k_230_, lean_object* v_t_231_){
_start:
{
if (lean_obj_tag(v_t_231_) == 0)
{
lean_object* v_k_232_; lean_object* v_l_233_; lean_object* v_r_234_; uint8_t v___x_235_; 
v_k_232_ = lean_ctor_get(v_t_231_, 1);
v_l_233_ = lean_ctor_get(v_t_231_, 3);
v_r_234_ = lean_ctor_get(v_t_231_, 4);
v___x_235_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_230_, v_k_232_);
switch(v___x_235_)
{
case 0:
{
v_t_231_ = v_l_233_;
goto _start;
}
case 1:
{
uint8_t v___x_237_; 
v___x_237_ = 1;
return v___x_237_;
}
default: 
{
v_t_231_ = v_r_234_;
goto _start;
}
}
}
else
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_230_ = stack[0].m_obj;
lean_object* v_t_231_ = stack[1].m_obj;
uint8_t v_res_240_;
v_res_240_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_230_, v_t_231_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg___boxed(lean_object* v_k_241_, lean_object* v_t_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_241_, v_t_242_);
lean_dec(v_t_242_);
lean_dec(v_k_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(lean_object* v_fvars_245_, lean_object* v___x_246_, lean_object* v_n_247_, lean_object* v_j_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_zero_250_; uint8_t v_isZero_251_; 
v_zero_250_ = lean_unsigned_to_nat(0u);
v_isZero_251_ = lean_nat_dec_eq(v_j_248_, v_zero_250_);
if (v_isZero_251_ == 1)
{
lean_dec(v_j_248_);
return v_a_249_;
}
else
{
lean_object* v_one_252_; lean_object* v_n_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_one_252_ = lean_unsigned_to_nat(1u);
v_n_253_ = lean_nat_sub(v_j_248_, v_one_252_);
v___x_254_ = lean_nat_sub(v_n_247_, v_j_248_);
lean_dec(v_j_248_);
v___x_255_ = lean_array_fget_borrowed(v_fvars_245_, v___x_254_);
v___x_256_ = l_Lean_Expr_fvarId_x21(v___x_255_);
v___x_257_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_256_, v___x_246_);
lean_dec(v___x_256_);
if (v___x_257_ == 0)
{
lean_dec(v___x_254_);
v_j_248_ = v_n_253_;
goto _start;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(0);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_a_249_, v___x_254_, v___x_259_);
v_j_248_ = v_n_253_;
v_a_249_ = v___x_260_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg___boxed(lean_object* v_fvars_262_, lean_object* v___x_263_, lean_object* v_n_264_, lean_object* v_j_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_262_, v___x_263_, v_n_264_, v_j_265_, v_a_266_);
lean_dec(v_n_264_);
lean_dec(v___x_263_);
lean_dec_ref(v_fvars_262_);
return v_res_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_unsigned_to_nat(16u);
v___x_270_ = lean_mk_array(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__0);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
return v___x_273_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(lean_object* v_body_276_, lean_object* v___x_277_, lean_object* v_fvars_278_, lean_object* v_info_279_, lean_object* v_bodyDeps_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc_ref(v_body_276_);
v___x_286_ = lean_infer_type(v_body_276_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_n(v_a_287_, 2);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_Meta_getLevel(v_a_287_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_316_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_316_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_316_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_316_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_fvarSet_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_haveInfo_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_277_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
lean_inc(v_a_287_);
v___x_296_ = l_Lean_collectFVars(v___x_295_, v_a_287_);
v_fvarSet_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_fvarSet_297_);
lean_dec_ref(v___x_296_);
v___x_298_ = lean_array_get_size(v_fvars_278_);
v___x_299_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_278_, v_fvarSet_297_, v___x_298_, v___x_298_, v___x_293_);
lean_dec(v_fvarSet_297_);
v_haveInfo_300_ = lean_ctor_get(v_info_279_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_info_279_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_311_ = lean_ctor_get(v_info_279_, 5);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_info_279_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_info_279_, 3);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_info_279_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_info_279_, 1);
lean_dec(v_unused_315_);
v___x_302_ = v_info_279_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_haveInfo_300_);
lean_dec(v_info_279_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 5, v_a_289_);
lean_ctor_set(v___x_302_, 4, v_a_287_);
lean_ctor_set(v___x_302_, 3, v_body_276_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
lean_ctor_set(v___x_302_, 1, v_bodyDeps_280_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_haveInfo_300_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_bodyDeps_280_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_body_276_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_a_287_);
lean_ctor_set(v_reuseFailAlloc_309_, 5, v_a_289_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_305_);
v___x_307_ = v___x_291_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_a_287_);
lean_dec_ref(v_bodyDeps_280_);
lean_dec_ref(v_info_279_);
lean_dec(v___x_277_);
lean_dec_ref(v_body_276_);
v_a_317_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_288_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_288_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec_ref(v_bodyDeps_280_);
lean_dec_ref(v_info_279_);
lean_dec(v___x_277_);
lean_dec_ref(v_body_276_);
v_a_325_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_286_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_286_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_276_ = stack[0].m_obj;
lean_object* v___x_277_ = stack[1].m_obj;
lean_object* v_fvars_278_ = stack[2].m_obj;
lean_object* v_info_279_ = stack[3].m_obj;
lean_object* v_bodyDeps_280_ = stack[4].m_obj;
lean_object* v___y_281_ = stack[5].m_obj;
lean_object* v___y_282_ = stack[6].m_obj;
lean_object* v___y_283_ = stack[7].m_obj;
lean_object* v___y_284_ = stack[8].m_obj;
lean_object* v_res_333_;
v_res_333_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_276_, v___x_277_, v_fvars_278_, v_info_279_, v_bodyDeps_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed(lean_object* v_body_334_, lean_object* v___x_335_, lean_object* v_fvars_336_, lean_object* v_info_337_, lean_object* v_bodyDeps_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1(v_body_334_, v___x_335_, v_fvars_336_, v_info_337_, v_bodyDeps_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec_ref(v_fvars_336_);
return v_res_344_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v_ngen_348_; lean_object* v_namePrefix_349_; lean_object* v_idx_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_380_; 
v___x_347_ = lean_st_ref_get(v___y_345_);
v_ngen_348_ = lean_ctor_get(v___x_347_, 2);
lean_inc_ref(v_ngen_348_);
lean_dec(v___x_347_);
v_namePrefix_349_ = lean_ctor_get(v_ngen_348_, 0);
v_idx_350_ = lean_ctor_get(v_ngen_348_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_ngen_348_);
if (v_isSharedCheck_380_ == 0)
{
v___x_352_ = v_ngen_348_;
v_isShared_353_ = v_isSharedCheck_380_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_idx_350_);
lean_inc(v_namePrefix_349_);
lean_dec(v_ngen_348_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_380_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_r_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
lean_inc(v_idx_350_);
lean_inc(v_namePrefix_349_);
v_r_354_ = l_Lean_Name_num___override(v_namePrefix_349_, v_idx_350_);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_idx_350_, v___x_355_);
lean_dec(v_idx_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_356_);
v___x_358_ = v___x_352_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_namePrefix_349_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_356_);
v___x_358_ = v_reuseFailAlloc_379_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v_env_360_; lean_object* v_nextMacroScope_361_; lean_object* v_auxDeclNGen_362_; lean_object* v_traceState_363_; lean_object* v_cache_364_; lean_object* v_recordedDeps_365_; lean_object* v_messages_366_; lean_object* v_infoState_367_; lean_object* v_snapshotTasks_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_377_; 
v___x_359_ = lean_st_ref_take(v___y_345_);
v_env_360_ = lean_ctor_get(v___x_359_, 0);
v_nextMacroScope_361_ = lean_ctor_get(v___x_359_, 1);
v_auxDeclNGen_362_ = lean_ctor_get(v___x_359_, 3);
v_traceState_363_ = lean_ctor_get(v___x_359_, 4);
v_cache_364_ = lean_ctor_get(v___x_359_, 5);
v_recordedDeps_365_ = lean_ctor_get(v___x_359_, 6);
v_messages_366_ = lean_ctor_get(v___x_359_, 7);
v_infoState_367_ = lean_ctor_get(v___x_359_, 8);
v_snapshotTasks_368_ = lean_ctor_get(v___x_359_, 9);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_359_, 2);
lean_dec(v_unused_378_);
v___x_370_ = v___x_359_;
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_snapshotTasks_368_);
lean_inc(v_infoState_367_);
lean_inc(v_messages_366_);
lean_inc(v_recordedDeps_365_);
lean_inc(v_cache_364_);
lean_inc(v_traceState_363_);
lean_inc(v_auxDeclNGen_362_);
lean_inc(v_nextMacroScope_361_);
lean_inc(v_env_360_);
lean_dec(v___x_359_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 2, v___x_358_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_env_360_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_nextMacroScope_361_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_auxDeclNGen_362_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_traceState_363_);
lean_ctor_set(v_reuseFailAlloc_376_, 5, v_cache_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_recordedDeps_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v_messages_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v_infoState_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 9, v_snapshotTasks_368_);
v___x_373_ = v_reuseFailAlloc_376_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_st_ref_put(v___y_345_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_r_354_);
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_345_ = stack[0].m_obj;
lean_object* v_res_381_;
v_res_381_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_345_);
stack->m_obj
 = v_res_381_;
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
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
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
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_385_ = stack[0].m_obj;
lean_object* v___y_386_ = stack[1].m_obj;
lean_object* v___y_387_ = stack[2].m_obj;
lean_object* v___y_388_ = stack[3].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_385_, v___y_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6___boxed(lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_405_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(lean_object* v_e_406_, lean_object* v_numHaves_407_, lean_object* v_info_408_, lean_object* v_lctx_409_, lean_object* v_fvars_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; 
v___x_416_ = lean_box(1);
if (lean_obj_tag(v_e_406_) == 8)
{
uint8_t v_nondep_426_; 
v_nondep_426_ = lean_ctor_get_uint8(v_e_406_, sizeof(void*)*4 + 8);
if (v_nondep_426_ == 1)
{
lean_object* v_declName_427_; lean_object* v_type_428_; lean_object* v_value_429_; lean_object* v_body_430_; lean_object* v_typeBackDeps_431_; lean_object* v_valueBackDeps_432_; lean_object* v_t_433_; lean_object* v_v_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_declName_427_ = lean_ctor_get(v_e_406_, 0);
lean_inc(v_declName_427_);
v_type_428_ = lean_ctor_get(v_e_406_, 1);
lean_inc_ref_n(v_type_428_, 2);
v_value_429_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref_n(v_value_429_, 2);
v_body_430_ = lean_ctor_get(v_e_406_, 3);
lean_inc_ref(v_body_430_);
lean_dec_ref_known(v_e_406_, 4);
v_typeBackDeps_431_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_407_, v_type_428_);
v_valueBackDeps_432_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_407_, v_value_429_);
v_t_433_ = lean_expr_instantiate_rev(v_type_428_, v_fvars_410_);
lean_dec_ref(v_type_428_);
v_v_434_ = lean_expr_instantiate_rev(v_value_429_, v_fvars_410_);
lean_dec_ref(v_value_429_);
lean_inc_ref(v_t_433_);
v___x_435_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_435_, 0, v_t_433_);
lean_inc_ref(v_lctx_409_);
v___x_436_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_409_, v___x_435_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6(v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_haveInfo_440_; lean_object* v_bodyDeps_441_; lean_object* v_bodyTypeDeps_442_; lean_object* v_body_443_; lean_object* v_bodyType_444_; lean_object* v_level_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_463_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v_haveInfo_440_ = lean_ctor_get(v_info_408_, 0);
v_bodyDeps_441_ = lean_ctor_get(v_info_408_, 1);
v_bodyTypeDeps_442_ = lean_ctor_get(v_info_408_, 2);
v_body_443_ = lean_ctor_get(v_info_408_, 3);
v_bodyType_444_ = lean_ctor_get(v_info_408_, 4);
v_level_445_ = lean_ctor_get(v_info_408_, 5);
v_isSharedCheck_463_ = !lean_is_exclusive(v_info_408_);
if (v_isSharedCheck_463_ == 0)
{
v___x_447_ = v_info_408_;
v_isShared_448_ = v_isSharedCheck_463_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_level_445_);
lean_inc(v_bodyType_444_);
lean_inc(v_body_443_);
lean_inc(v_bodyTypeDeps_442_);
lean_inc(v_bodyDeps_441_);
lean_inc(v_haveInfo_440_);
lean_dec(v_info_408_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_463_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = 0;
lean_inc(v_a_439_);
v___x_451_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v_a_439_);
lean_ctor_set(v___x_451_, 2, v_declName_427_);
lean_ctor_set(v___x_451_, 3, v_t_433_);
lean_ctor_set(v___x_451_, 4, v_v_434_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*5, v_nondep_426_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*5 + 1, v___x_450_);
lean_inc_ref(v___x_451_);
v___x_452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_452_, 0, v_typeBackDeps_431_);
lean_ctor_set(v___x_452_, 1, v_valueBackDeps_432_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
lean_ctor_set(v___x_452_, 3, v_a_437_);
v___x_453_ = lean_array_push(v_haveInfo_440_, v___x_452_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_453_);
v___x_455_ = v___x_447_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_bodyDeps_441_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_bodyTypeDeps_442_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_body_443_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_bodyType_444_);
lean_ctor_set(v_reuseFailAlloc_462_, 5, v_level_445_);
v___x_455_ = v_reuseFailAlloc_462_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = l_Lean_LocalContext_addDecl(v_lctx_409_, v___x_451_);
v___x_457_ = l_Lean_mkFVar(v_a_439_);
v___x_458_ = lean_array_push(v_fvars_410_, v___x_457_);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v_numHaves_407_, v___x_459_);
lean_dec(v_numHaves_407_);
v_e_406_ = v_body_430_;
v_numHaves_407_ = v___x_460_;
v_info_408_ = v___x_455_;
v_lctx_409_ = v___x_456_;
v_fvars_410_ = v___x_458_;
goto _start;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_a_437_);
lean_dec_ref(v_v_434_);
lean_dec_ref(v_t_433_);
lean_dec_ref(v_valueBackDeps_432_);
lean_dec_ref(v_typeBackDeps_431_);
lean_dec_ref(v_body_430_);
lean_dec(v_declName_427_);
lean_dec_ref(v_fvars_410_);
lean_dec_ref(v_lctx_409_);
lean_dec_ref(v_info_408_);
lean_dec(v_numHaves_407_);
v_a_464_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_438_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_438_);
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
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_v_434_);
lean_dec_ref(v_t_433_);
lean_dec_ref(v_valueBackDeps_432_);
lean_dec_ref(v_typeBackDeps_431_);
lean_dec_ref(v_body_430_);
lean_dec(v_declName_427_);
lean_dec_ref(v_fvars_410_);
lean_dec_ref(v_lctx_409_);
lean_dec_ref(v_info_408_);
lean_dec(v_numHaves_407_);
v_a_472_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_436_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_436_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
v___y_418_ = v_a_411_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
goto v___jp_417_;
}
}
else
{
v___y_418_ = v_a_411_;
v___y_419_ = v_a_412_;
v___y_420_ = v_a_413_;
v___y_421_ = v_a_414_;
goto v___jp_417_;
}
v___jp_417_:
{
lean_object* v_bodyDeps_422_; lean_object* v_body_423_; lean_object* v___f_424_; lean_object* v___x_425_; 
lean_inc_ref(v_e_406_);
v_bodyDeps_422_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__0(v_numHaves_407_, v_e_406_);
lean_dec(v_numHaves_407_);
v_body_423_ = lean_expr_instantiate_rev(v_e_406_, v_fvars_410_);
lean_dec_ref(v_e_406_);
v___f_424_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___boxed), 10, 5);
lean_closure_set(v___f_424_, 0, v_body_423_);
lean_closure_set(v___f_424_, 1, v___x_416_);
lean_closure_set(v___f_424_, 2, v_fvars_410_);
lean_closure_set(v___f_424_, 3, v_info_408_);
lean_closure_set(v___f_424_, 4, v_bodyDeps_422_);
v___x_425_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__5___redArg(v_lctx_409_, v___f_424_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_425_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_406_ = stack[0].m_obj;
lean_object* v_numHaves_407_ = stack[1].m_obj;
lean_object* v_info_408_ = stack[2].m_obj;
lean_object* v_lctx_409_ = stack[3].m_obj;
lean_object* v_fvars_410_ = stack[4].m_obj;
lean_object* v_a_411_ = stack[5].m_obj;
lean_object* v_a_412_ = stack[6].m_obj;
lean_object* v_a_413_ = stack[7].m_obj;
lean_object* v_a_414_ = stack[8].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_406_, v_numHaves_407_, v_info_408_, v_lctx_409_, v_fvars_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___boxed(lean_object* v_e_481_, lean_object* v_numHaves_482_, lean_object* v_info_483_, lean_object* v_lctx_484_, lean_object* v_fvars_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_481_, v_numHaves_482_, v_info_483_, v_lctx_484_, v_fvars_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0(lean_object* v_00_u03b2_492_, lean_object* v_m_493_, lean_object* v_a_494_, lean_object* v_b_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0___redArg(v_m_493_, v_a_494_, v_b_495_);
return v___x_496_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_object* v_00_u03b2_497_, lean_object* v_k_498_, lean_object* v_t_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_k_498_, v_t_499_);
return v___x_500_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_498_ = stack[1].m_obj;
lean_object* v_t_499_ = stack[2].m_obj;
uint8_t v_res_501_;
v_res_501_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(lean_box(0), v_k_498_, v_t_499_);
stack->m_num = v_res_501_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___boxed(lean_object* v_00_u03b2_502_, lean_object* v_k_503_, lean_object* v_t_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3(v_00_u03b2_502_, v_k_503_, v_t_504_);
lean_dec(v_t_504_);
lean_dec(v_k_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(lean_object* v_fvars_507_, lean_object* v___x_508_, lean_object* v_n_509_, lean_object* v_j_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___redArg(v_fvars_507_, v___x_508_, v_n_509_, v_j_510_, v_a_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4___boxed(lean_object* v_fvars_514_, lean_object* v___x_515_, lean_object* v_n_516_, lean_object* v_j_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__4(v_fvars_514_, v___x_515_, v_n_516_, v_j_517_, v_a_518_, v_a_519_);
lean_dec(v_n_516_);
lean_dec(v___x_515_);
lean_dec_ref(v_fvars_514_);
return v_res_520_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___redArg(v___y_524_);
return v___x_526_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_521_ = stack[0].m_obj;
lean_object* v___y_522_ = stack[1].m_obj;
lean_object* v___y_523_ = stack[2].m_obj;
lean_object* v___y_524_ = stack[3].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_521_, v___y_522_, v___y_523_, v___y_524_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8___boxed(lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__6_spec__8(v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_object* v_00_u03b2_534_, lean_object* v_a_535_, lean_object* v_x_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___redArg(v_a_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_535_ = stack[1].m_obj;
lean_object* v_x_536_ = stack[2].m_obj;
uint8_t v_res_538_;
v_res_538_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(lean_box(0), v_a_535_, v_x_536_);
stack->m_num = v_res_538_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0___boxed(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__0(v_00_u03b2_539_, v_a_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec(v_a_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1(lean_object* v_00_u03b2_544_, lean_object* v_data_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1___redArg(v_data_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_547_, lean_object* v_i_548_, lean_object* v_source_549_, lean_object* v_target_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3___redArg(v_i_548_, v_source_549_, v_target_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__0_spec__1_spec__3_spec__10___redArg(v_x_553_, v_x_554_);
return v___x_555_;
}
}
lean_object* l_Lean_Meta_getHaveTelescopeInfo(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_lctx_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_lctx_562_ = lean_ctor_get(v_a_557_, 2);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = ((lean_object*)(l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__0));
v___x_565_ = lean_obj_once(&l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5, &l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5_once, _init_l_Lean_Meta_instInhabitedHaveTelescopeInfo_default___closed__5);
lean_inc_ref(v_lctx_562_);
v___x_566_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_556_, v___x_563_, v___x_565_, v_lctx_562_, v___x_564_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
return v___x_566_;
}
}
LEAN_EXPORT void l_Lean_Meta_getHaveTelescopeInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_556_ = stack[0].m_obj;
lean_object* v_a_557_ = stack[1].m_obj;
lean_object* v_a_558_ = stack[2].m_obj;
lean_object* v_a_559_ = stack[3].m_obj;
lean_object* v_a_560_ = stack[4].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getHaveTelescopeInfo___boxed(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_getHaveTelescopeInfo(v_e_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
return v_x_575_;
}
else
{
lean_object* v_key_577_; lean_object* v_tail_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_key_577_ = lean_ctor_get(v_x_576_, 0);
v_tail_578_ = lean_ctor_get(v_x_576_, 2);
v___x_579_ = 1;
v___x_580_ = lean_box(v___x_579_);
v___x_581_ = lean_array_set(v_x_575_, v_key_577_, v___x_580_);
v_x_575_ = v___x_581_;
v_x_576_ = v_tail_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0___boxed(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_x_583_, v_x_584_);
lean_dec(v_x_584_);
return v_res_585_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(lean_object* v_as_586_, size_t v_i_587_, size_t v_stop_588_, lean_object* v_b_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_eq(v_i_587_, v_stop_588_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; size_t v___x_593_; size_t v___x_594_; 
v___x_591_ = lean_array_uget_borrowed(v_as_586_, v_i_587_);
v___x_592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__0(v_b_589_, v___x_591_);
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_587_, v___x_593_);
v_i_587_ = v___x_594_;
v_b_589_ = v___x_592_;
goto _start;
}
else
{
return v_b_589_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_586_ = stack[0].m_obj;
size_t v_i_587_ = stack[1].m_num;
size_t v_stop_588_ = stack[2].m_num;
lean_object* v_b_589_ = stack[3].m_obj;
lean_object* v_res_596_;
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_586_, v_i_587_, v_stop_588_, v_b_589_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1___boxed(lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_stop_599_, lean_object* v_b_600_){
_start:
{
size_t v_i_boxed_601_; size_t v_stop_boxed_602_; lean_object* v_res_603_; 
v_i_boxed_601_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_stop_boxed_602_ = lean_unbox_usize(v_stop_599_);
lean_dec(v_stop_599_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_as_597_, v_i_boxed_601_, v_stop_boxed_602_, v_b_600_);
lean_dec_ref(v_as_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(lean_object* v_arr_604_, lean_object* v_s_605_){
_start:
{
lean_object* v_buckets_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_buckets_606_ = lean_ctor_get(v_s_605_, 1);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_array_get_size(v_buckets_606_);
v___x_609_ = lean_nat_dec_lt(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
return v_arr_604_;
}
else
{
size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((size_t)0ULL);
v___x_611_ = lean_usize_of_nat(v___x_608_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps_spec__1(v_buckets_606_, v___x_610_, v___x_611_, v_arr_604_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps___boxed(lean_object* v_arr_613_, lean_object* v_s_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_arr_613_, v_s_614_);
lean_dec_ref(v_s_614_);
return v_res_615_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(lean_object* v_upperBound_616_, lean_object* v_numHaves_617_, lean_object* v___x_618_, lean_object* v_a_619_, lean_object* v_b_620_){
_start:
{
lean_object* v_a_623_; uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_lt(v_a_619_, v_upperBound_616_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec(v_a_619_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_620_);
return v___x_628_;
}
else
{
uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_629_ = 0;
v___x_630_ = lean_nat_sub(v_numHaves_617_, v_a_619_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_sub(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(v___x_629_);
v___x_634_ = lean_array_get(v___x_633_, v_b_620_, v___x_632_);
lean_dec(v___x_633_);
v___x_635_ = lean_unbox(v___x_634_);
lean_dec(v___x_634_);
if (v___x_635_ == 0)
{
lean_dec(v___x_632_);
v_a_623_ = v_b_620_;
goto v___jp_622_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_typeBackDeps_638_; lean_object* v_valueBackDeps_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_636_ = l_Lean_Meta_instInhabitedHaveInfo_default;
v___x_637_ = lean_array_get_borrowed(v___x_636_, v___x_618_, v___x_632_);
lean_dec(v___x_632_);
v_typeBackDeps_638_ = lean_ctor_get(v___x_637_, 0);
v_valueBackDeps_639_ = lean_ctor_get(v___x_637_, 1);
v___x_640_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_b_620_, v_typeBackDeps_638_);
v___x_641_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v___x_640_, v_valueBackDeps_639_);
v_a_623_ = v___x_641_;
goto v___jp_622_;
}
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_a_619_, v___x_624_);
lean_dec(v_a_619_);
v_a_619_ = v___x_625_;
v_b_620_ = v_a_623_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_616_ = stack[0].m_obj;
lean_object* v_numHaves_617_ = stack[1].m_obj;
lean_object* v___x_618_ = stack[2].m_obj;
lean_object* v_a_619_ = stack[3].m_obj;
lean_object* v_b_620_ = stack[4].m_obj;
lean_object* v_res_642_;
v_res_642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_616_, v_numHaves_617_, v___x_618_, v_a_619_, v_b_620_);
stack->m_obj
 = v_res_642_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg___boxed(lean_object* v_upperBound_643_, lean_object* v_numHaves_644_, lean_object* v___x_645_, lean_object* v_a_646_, lean_object* v_b_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_643_, v_numHaves_644_, v___x_645_, v_a_646_, v_b_647_);
lean_dec_ref(v___x_645_);
lean_dec(v_numHaves_644_);
lean_dec(v_upperBound_643_);
return v_res_649_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(lean_object* v_info_650_, lean_object* v_init_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_haveInfo_657_; lean_object* v_numHaves_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v_used_661_; lean_object* v___x_662_; lean_object* v_used_663_; lean_object* v___x_664_; 
v_haveInfo_657_ = lean_ctor_get(v_info_650_, 0);
v_numHaves_658_ = lean_array_get_size(v_haveInfo_657_);
v___x_659_ = 0;
v___x_660_ = lean_box(v___x_659_);
v_used_661_ = lean_mk_array(v_numHaves_658_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(0u);
v_used_663_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_updateArrayFromBackDeps(v_used_661_, v_init_651_);
v___x_664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_numHaves_658_, v_numHaves_658_, v_haveInfo_657_, v___x_662_, v_used_663_);
return v___x_664_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_650_ = stack[0].m_obj;
lean_object* v_init_651_ = stack[1].m_obj;
lean_object* v_a_652_ = stack[2].m_obj;
lean_object* v_a_653_ = stack[3].m_obj;
lean_object* v_a_654_ = stack[4].m_obj;
lean_object* v_a_655_ = stack[5].m_obj;
lean_object* v_res_665_;
v_res_665_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_650_, v_init_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go___boxed(lean_object* v_info_666_, lean_object* v_init_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_666_, v_init_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec_ref(v_init_667_);
lean_dec_ref(v_info_666_);
return v_res_673_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(lean_object* v_upperBound_674_, lean_object* v_numHaves_675_, lean_object* v___x_676_, lean_object* v_inst_677_, lean_object* v_R_678_, lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_c_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___redArg(v_upperBound_674_, v_numHaves_675_, v___x_676_, v_a_679_, v_b_680_);
return v___x_687_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_674_ = stack[0].m_obj;
lean_object* v_numHaves_675_ = stack[1].m_obj;
lean_object* v___x_676_ = stack[2].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_b_680_ = stack[6].m_obj;
lean_object* v___y_682_ = stack[8].m_obj;
lean_object* v___y_683_ = stack[9].m_obj;
lean_object* v___y_684_ = stack[10].m_obj;
lean_object* v___y_685_ = stack[11].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_674_, v_numHaves_675_, v___x_676_, lean_box(0), lean_box(0), v_a_679_, v_b_680_, lean_box(0), v___y_682_, v___y_683_, v___y_684_, v___y_685_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0___boxed(lean_object* v_upperBound_689_, lean_object* v_numHaves_690_, lean_object* v___x_691_, lean_object* v_inst_692_, lean_object* v_R_693_, lean_object* v_a_694_, lean_object* v_b_695_, lean_object* v_c_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go_spec__0(v_upperBound_689_, v_numHaves_690_, v___x_691_, v_inst_692_, v_R_693_, v_a_694_, v_b_695_, v_c_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec_ref(v___x_691_);
lean_dec(v_numHaves_690_);
lean_dec(v_upperBound_689_);
return v_res_702_;
}
}
lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(lean_object* v_info_705_, uint8_t v_keepUnused_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_bodyDeps_712_; lean_object* v_bodyTypeDeps_713_; lean_object* v___x_714_; 
v_bodyDeps_712_ = lean_ctor_get(v_info_705_, 1);
v_bodyTypeDeps_713_ = lean_ctor_get(v_info_705_, 2);
v___x_714_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_705_, v_bodyTypeDeps_713_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_714_) == 0)
{
if (v_keepUnused_706_ == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_HaveTelescopeInfo_computeFixedUsed_go(v_info_705_, v_bodyDeps_712_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_725_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v_a_715_);
lean_ctor_set(v___x_721_, 1, v_a_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_723_ = v___x_719_;
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
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_715_);
v_a_726_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_716_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_716_);
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
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_743_; 
v_a_734_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_743_ == 0)
{
v___x_736_ = v___x_714_;
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_714_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_738_ = ((lean_object*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___closed__0));
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_734_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_a_744_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_714_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_714_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_705_ = stack[0].m_obj;
uint8_t v_keepUnused_706_ = stack[1].m_num;
lean_object* v_a_707_ = stack[2].m_obj;
lean_object* v_a_708_ = stack[3].m_obj;
lean_object* v_a_709_ = stack[4].m_obj;
lean_object* v_a_710_ = stack[5].m_obj;
lean_object* v_res_752_;
v_res_752_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_705_, v_keepUnused_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed(lean_object* v_info_753_, lean_object* v_keepUnused_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
uint8_t v_keepUnused_boxed_760_; lean_object* v_res_761_; 
v_keepUnused_boxed_760_ = lean_unbox(v_keepUnused_754_);
v_res_761_ = l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed(v_info_753_, v_keepUnused_boxed_760_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec_ref(v_info_753_);
return v_res_761_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = ((lean_object*)(l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__1));
v___x_767_ = l_Lean_Expr_const___override(v___x_766_, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3(void){
_start:
{
uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = 0;
v___x_769_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__2);
v___x_770_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
lean_ctor_set(v___x_770_, 3, v___x_769_);
lean_ctor_set(v___x_770_, 4, v___x_769_);
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*5, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpHaveResult_default(void){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_obj_once(&l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3, &l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3_once, _init_l_Lean_Meta_instInhabitedSimpHaveResult_default___closed__3);
return v___x_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
return v___x_772_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(lean_object* v_level_789_, lean_object* v_exprType_790_, lean_object* v_e_791_, uint8_t v___x_792_, lean_object* v_toPure_793_, lean_object* v_xs_794_, lean_object* v_____do__lift_795_){
_start:
{
if (lean_obj_tag(v_____do__lift_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_proof_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_798_, 0, v_level_789_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_mkConst(v___x_796_, v___x_798_);
lean_inc_ref_n(v_e_791_, 3);
lean_inc_ref(v_exprType_790_);
v_proof_800_ = l_Lean_mkAppB(v___x_799_, v_exprType_790_, v_e_791_);
v___x_801_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_801_, 0, v_e_791_);
lean_ctor_set(v___x_801_, 1, v_exprType_790_);
lean_ctor_set(v___x_801_, 2, v_e_791_);
lean_ctor_set(v___x_801_, 3, v_e_791_);
lean_ctor_set(v___x_801_, 4, v_proof_800_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*5, v___x_792_);
v___x_802_ = lean_apply_2(v_toPure_793_, lean_box(0), v___x_801_);
return v___x_802_;
}
else
{
lean_object* v_e_803_; lean_object* v_h_804_; lean_object* v_expr_805_; lean_object* v_proof_806_; lean_object* v___x_811_; uint8_t v___x_812_; 
lean_dec(v_level_789_);
v_e_803_ = lean_ctor_get(v_____do__lift_795_, 0);
v_h_804_ = lean_ctor_get(v_____do__lift_795_, 1);
v_expr_805_ = lean_expr_abstract(v_e_803_, v_xs_794_);
v_proof_806_ = lean_expr_abstract(v_h_804_, v_xs_794_);
lean_inc_ref(v_proof_806_);
v___x_811_ = l_Lean_Expr_cleanupAnnotations(v_proof_806_);
v___x_812_ = l_Lean_Expr_isApp(v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v___x_811_);
goto v___jp_807_;
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
goto v___jp_807_;
}
else
{
lean_object* v_arg_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_arg_816_ = lean_ctor_get(v___x_814_, 1);
lean_inc_ref(v_arg_816_);
v___x_817_ = l_Lean_Expr_appFnCleanup___redArg(v___x_814_);
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__4));
v___x_819_ = l_Lean_Expr_isConstOf(v___x_817_, v___x_818_);
lean_dec_ref(v___x_817_);
if (v___x_819_ == 0)
{
lean_dec_ref(v_arg_816_);
lean_dec_ref(v_arg_813_);
goto v___jp_807_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_821_ = lean_unsigned_to_nat(3u);
v___x_822_ = l_Lean_Expr_isAppOfArity(v_arg_816_, v___x_820_, v___x_821_);
lean_dec_ref(v_arg_816_);
if (v___x_822_ == 0)
{
lean_dec_ref(v_arg_813_);
goto v___jp_807_;
}
else
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = l_Lean_Expr_cleanupAnnotations(v_arg_813_);
v___x_824_ = l_Lean_Expr_isApp(v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v___x_823_);
goto v___jp_807_;
}
else
{
lean_object* v_arg_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_arg_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc_ref(v_arg_825_);
v___x_826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_823_);
v___x_827_ = l_Lean_Expr_isApp(v___x_826_);
if (v___x_827_ == 0)
{
lean_dec_ref(v___x_826_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v_arg_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_arg_828_ = lean_ctor_get(v___x_826_, 1);
lean_inc_ref(v_arg_828_);
v___x_829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_826_);
v___x_830_ = l_Lean_Expr_isConstOf(v___x_829_, v___x_818_);
lean_dec_ref(v___x_829_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_arg_828_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = l_Lean_Expr_cleanupAnnotations(v_arg_828_);
v___x_832_ = l_Lean_Expr_isApp(v___x_831_);
if (v___x_832_ == 0)
{
lean_dec_ref(v___x_831_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v_arg_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_arg_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc_ref(v_arg_833_);
v___x_834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_831_);
v___x_835_ = l_Lean_Expr_isApp(v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v___x_834_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v_arg_836_; uint8_t v___y_838_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_arg_836_ = lean_ctor_get(v___x_834_, 1);
lean_inc_ref(v_arg_836_);
v___x_841_ = l_Lean_Expr_appFnCleanup___redArg(v___x_834_);
v___x_842_ = l_Lean_Expr_isApp(v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v___x_841_);
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = l_Lean_Expr_appFnCleanup___redArg(v___x_841_);
v___x_844_ = l_Lean_Expr_isConstOf(v___x_843_, v___x_820_);
lean_dec_ref(v___x_843_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Expr_getAppFn(v_arg_825_);
if (lean_obj_tag(v___x_845_) == 4)
{
lean_object* v_declName_846_; 
v_declName_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_declName_846_);
lean_dec_ref_known(v___x_845_, 2);
if (lean_obj_tag(v_declName_846_) == 1)
{
lean_object* v_pre_847_; 
v_pre_847_ = lean_ctor_get(v_declName_846_, 0);
if (lean_obj_tag(v_pre_847_) == 0)
{
lean_object* v_str_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_str_848_ = lean_ctor_get(v_declName_846_, 1);
lean_inc_ref(v_str_848_);
lean_dec_ref_known(v_declName_846_, 2);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__6));
v___x_850_ = lean_string_dec_eq(v_str_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__7));
v___x_852_ = lean_string_dec_eq(v_str_848_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__8));
v___x_854_ = lean_string_dec_eq(v_str_848_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__9));
v___x_856_ = lean_string_dec_eq(v_str_848_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__10));
v___x_858_ = lean_string_dec_eq(v_str_848_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__11));
v___x_860_ = lean_string_dec_eq(v_str_848_, v___x_859_);
lean_dec_ref(v_str_848_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
v___y_838_ = v___x_819_;
goto v___jp_837_;
}
}
else
{
lean_dec_ref(v_str_848_);
v___y_838_ = v___x_819_;
goto v___jp_837_;
}
}
else
{
lean_dec_ref(v_str_848_);
v___y_838_ = v___x_819_;
goto v___jp_837_;
}
}
else
{
lean_dec_ref(v_str_848_);
v___y_838_ = v___x_819_;
goto v___jp_837_;
}
}
else
{
lean_dec_ref(v_str_848_);
v___y_838_ = v___x_819_;
goto v___jp_837_;
}
}
else
{
lean_dec_ref(v_str_848_);
v___y_838_ = v___x_819_;
goto v___jp_837_;
}
}
else
{
lean_dec_ref_known(v_declName_846_, 2);
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
}
else
{
lean_dec(v_declName_846_);
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
}
else
{
lean_dec_ref(v___x_845_);
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
}
}
v___jp_837_:
{
if (v___y_838_ == 0)
{
lean_dec_ref(v_arg_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_825_);
goto v___jp_807_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_proof_806_);
lean_dec_ref(v_e_791_);
v___x_839_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_839_, 0, v_arg_833_);
lean_ctor_set(v___x_839_, 1, v_exprType_790_);
lean_ctor_set(v___x_839_, 2, v_arg_836_);
lean_ctor_set(v___x_839_, 3, v_expr_805_);
lean_ctor_set(v___x_839_, 4, v_arg_825_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*5, v___x_819_);
v___x_840_ = lean_apply_2(v_toPure_793_, lean_box(0), v___x_839_);
return v___x_840_;
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
v___jp_807_:
{
uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = 1;
lean_inc_ref(v_expr_805_);
v___x_809_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_809_, 0, v_expr_805_);
lean_ctor_set(v___x_809_, 1, v_exprType_790_);
lean_ctor_set(v___x_809_, 2, v_e_791_);
lean_ctor_set(v___x_809_, 3, v_expr_805_);
lean_ctor_set(v___x_809_, 4, v_proof_806_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*5, v___x_808_);
v___x_810_ = lean_apply_2(v_toPure_793_, lean_box(0), v___x_809_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_789_ = stack[0].m_obj;
lean_object* v_exprType_790_ = stack[1].m_obj;
lean_object* v_e_791_ = stack[2].m_obj;
uint8_t v___x_792_ = stack[3].m_num;
lean_object* v_toPure_793_ = stack[4].m_obj;
lean_object* v_xs_794_ = stack[5].m_obj;
lean_object* v_____do__lift_795_ = stack[6].m_obj;
lean_object* v_res_861_;
v_res_861_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_level_789_, v_exprType_790_, v_e_791_, v___x_792_, v_toPure_793_, v_xs_794_, v_____do__lift_795_);
stack->m_obj
 = v_res_861_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed(lean_object* v_level_862_, lean_object* v_exprType_863_, lean_object* v_e_864_, lean_object* v___x_865_, lean_object* v_toPure_866_, lean_object* v_xs_867_, lean_object* v_____do__lift_868_){
_start:
{
uint8_t v___x_7908__boxed_869_; lean_object* v_res_870_; 
v___x_7908__boxed_869_ = lean_unbox(v___x_865_);
v_res_870_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_level_862_, v_exprType_863_, v_e_864_, v___x_7908__boxed_869_, v_toPure_866_, v_xs_867_, v_____do__lift_868_);
lean_dec(v_____do__lift_868_);
lean_dec_ref(v_xs_867_);
return v_res_870_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(lean_object* v_inst_871_, lean_object* v_bodyType_872_, lean_object* v_xs_873_, lean_object* v_level_874_, lean_object* v_e_875_, uint8_t v___x_876_, lean_object* v_toPure_877_, lean_object* v_body_878_, lean_object* v_toBind_879_, lean_object* v_____r_880_){
_start:
{
lean_object* v_simp_881_; lean_object* v_exprType_882_; lean_object* v___x_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_simp_881_ = lean_ctor_get(v_inst_871_, 2);
lean_inc(v_simp_881_);
lean_dec_ref(v_inst_871_);
v_exprType_882_ = lean_expr_abstract(v_bodyType_872_, v_xs_873_);
v___x_883_ = lean_box(v___x_876_);
v___f_884_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_884_, 0, v_level_874_);
lean_closure_set(v___f_884_, 1, v_exprType_882_);
lean_closure_set(v___f_884_, 2, v_e_875_);
lean_closure_set(v___f_884_, 3, v___x_883_);
lean_closure_set(v___f_884_, 4, v_toPure_877_);
lean_closure_set(v___f_884_, 5, v_xs_873_);
v___x_885_ = lean_apply_1(v_simp_881_, v_body_878_);
v___x_886_ = lean_apply_4(v_toBind_879_, lean_box(0), lean_box(0), v___x_885_, v___f_884_);
return v___x_886_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_871_ = stack[0].m_obj;
lean_object* v_bodyType_872_ = stack[1].m_obj;
lean_object* v_xs_873_ = stack[2].m_obj;
lean_object* v_level_874_ = stack[3].m_obj;
lean_object* v_e_875_ = stack[4].m_obj;
uint8_t v___x_876_ = stack[5].m_num;
lean_object* v_toPure_877_ = stack[6].m_obj;
lean_object* v_body_878_ = stack[7].m_obj;
lean_object* v_toBind_879_ = stack[8].m_obj;
lean_object* v_____r_880_ = stack[9].m_obj;
lean_object* v_res_887_;
v_res_887_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_871_, v_bodyType_872_, v_xs_873_, v_level_874_, v_e_875_, v___x_876_, v_toPure_877_, v_body_878_, v_toBind_879_, v_____r_880_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed(lean_object* v_inst_888_, lean_object* v_bodyType_889_, lean_object* v_xs_890_, lean_object* v_level_891_, lean_object* v_e_892_, lean_object* v___x_893_, lean_object* v_toPure_894_, lean_object* v_body_895_, lean_object* v_toBind_896_, lean_object* v_____r_897_){
_start:
{
uint8_t v___x_8143__boxed_898_; lean_object* v_res_899_; 
v___x_8143__boxed_898_ = lean_unbox(v___x_893_);
v_res_899_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_888_, v_bodyType_889_, v_xs_890_, v_level_891_, v_e_892_, v___x_8143__boxed_898_, v_toPure_894_, v_body_895_, v_toBind_896_, v_____r_897_);
lean_dec_ref(v_bodyType_889_);
return v_res_899_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_906_, lean_object* v_body_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_toMonadRef_910_, lean_object* v___x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_toCold_920_; lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
v_toCold_920_ = lean_ctor_get(v___y_914_, 0);
v_options_921_ = lean_ctor_get(v_toCold_920_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_toMonadRef_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_body_907_);
lean_dec(v_cls_906_);
goto v___jp_917_;
}
else
{
lean_object* v_inheritedTraceOptions_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_inheritedTraceOptions_923_ = lean_ctor_get(v_toCold_920_, 11);
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_906_);
v___x_925_ = l_Lean_Name_append(v___x_924_, v_cls_906_);
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_923_, v_options_921_, v___x_925_);
lean_dec(v___x_925_);
if (v___x_926_ == 0)
{
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v___x_911_);
lean_dec_ref(v_toMonadRef_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_body_907_);
lean_dec(v_cls_906_);
goto v___jp_917_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_7530__overap_930_; lean_object* v___x_931_; 
v___x_927_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3);
v___x_928_ = l_Lean_MessageData_ofExpr(v_body_907_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_7530__overap_930_ = l_Lean_addTrace___redArg(v___x_908_, v___x_909_, v_toMonadRef_910_, v___x_911_, v_cls_906_, v___x_929_);
v___x_931_ = lean_apply_5(v___x_7530__overap_930_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, lean_box(0));
return v___x_931_;
}
}
v___jp_917_:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_906_ = stack[0].m_obj;
lean_object* v_body_907_ = stack[1].m_obj;
lean_object* v___x_908_ = stack[2].m_obj;
lean_object* v___x_909_ = stack[3].m_obj;
lean_object* v_toMonadRef_910_ = stack[4].m_obj;
lean_object* v___x_911_ = stack[5].m_obj;
lean_object* v___y_912_ = stack[6].m_obj;
lean_object* v___y_913_ = stack[7].m_obj;
lean_object* v___y_914_ = stack[8].m_obj;
lean_object* v___y_915_ = stack[9].m_obj;
lean_object* v_res_932_;
v_res_932_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_906_, v_body_907_, v___x_908_, v___x_909_, v_toMonadRef_910_, v___x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
stack->m_obj
 = v_res_932_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_933_, lean_object* v_body_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v_toMonadRef_937_, lean_object* v___x_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_933_, v_body_934_, v___x_935_, v___x_936_, v_toMonadRef_937_, v___x_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v_res_944_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_947_, lean_object* v_type_948_, lean_object* v___y_949_, lean_object* v_value_950_, uint8_t v___y_951_, lean_object* v___x_952_, uint8_t v___y_953_, lean_object* v_toPure_954_, lean_object* v_us_955_, uint8_t v___x_956_, lean_object* v_rb_957_){
_start:
{
lean_object* v_expr_958_; lean_object* v_exprType_959_; lean_object* v_exprInit_960_; lean_object* v_exprResult_961_; lean_object* v_proof_962_; uint8_t v_modified_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_990_; 
v_expr_958_ = lean_ctor_get(v_rb_957_, 0);
v_exprType_959_ = lean_ctor_get(v_rb_957_, 1);
v_exprInit_960_ = lean_ctor_get(v_rb_957_, 2);
v_exprResult_961_ = lean_ctor_get(v_rb_957_, 3);
v_proof_962_ = lean_ctor_get(v_rb_957_, 4);
v_modified_963_ = lean_ctor_get_uint8(v_rb_957_, sizeof(void*)*5);
v_isSharedCheck_990_ = !lean_is_exclusive(v_rb_957_);
if (v_isSharedCheck_990_ == 0)
{
v___x_965_ = v_rb_957_;
v_isShared_966_ = v_isSharedCheck_990_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_proof_962_);
lean_inc(v_exprResult_961_);
lean_inc(v_exprInit_960_);
lean_inc(v_exprType_959_);
lean_inc(v_expr_958_);
lean_dec(v_rb_957_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_990_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v_expr_969_; lean_object* v___x_970_; lean_object* v_exprType_971_; lean_object* v___x_972_; lean_object* v_exprInit_973_; lean_object* v_exprResult_974_; 
v___x_967_ = 0;
lean_inc_ref_n(v_type_948_, 4);
lean_inc_n(v_declName_947_, 4);
v___x_968_ = l_Lean_mkLambda(v_declName_947_, v___x_967_, v_type_948_, v_expr_958_);
lean_inc_ref_n(v___y_949_, 3);
lean_inc_ref(v___x_968_);
v_expr_969_ = l_Lean_Expr_app___override(v___x_968_, v___y_949_);
v___x_970_ = l_Lean_mkLambda(v_declName_947_, v___x_967_, v_type_948_, v_exprType_959_);
lean_inc_ref(v___x_970_);
v_exprType_971_ = l_Lean_Expr_app___override(v___x_970_, v___y_949_);
v___x_972_ = l_Lean_mkLambda(v_declName_947_, v___x_967_, v_type_948_, v_exprInit_960_);
lean_inc_ref(v___x_972_);
v_exprInit_973_ = l_Lean_Expr_app___override(v___x_972_, v_value_950_);
v_exprResult_974_ = l_Lean_Expr_letE___override(v_declName_947_, v_type_948_, v___y_949_, v_exprResult_961_, v___y_951_);
if (v_modified_963_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_proof_977_; lean_object* v___x_979_; 
lean_dec_ref(v___x_972_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v___x_968_);
lean_dec_ref(v_proof_962_);
lean_dec(v_us_955_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_type_948_);
lean_dec(v_declName_947_);
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_976_ = l_Lean_mkConst(v___x_975_, v___x_952_);
lean_inc_ref(v_expr_969_);
lean_inc_ref(v_exprType_971_);
v_proof_977_ = l_Lean_mkAppB(v___x_976_, v_exprType_971_, v_expr_969_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v_proof_977_);
lean_ctor_set(v___x_965_, 3, v_exprResult_974_);
lean_ctor_set(v___x_965_, 2, v_exprInit_973_);
lean_ctor_set(v___x_965_, 1, v_exprType_971_);
lean_ctor_set(v___x_965_, 0, v_expr_969_);
v___x_979_ = v___x_965_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_expr_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_exprType_971_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_exprInit_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_exprResult_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_proof_977_);
v___x_979_ = v_reuseFailAlloc_981_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; 
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*5, v___y_953_);
v___x_980_ = lean_apply_2(v_toPure_954_, lean_box(0), v___x_979_);
return v___x_980_;
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_proof_985_; lean_object* v___x_987_; 
lean_dec(v___x_952_);
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_983_ = l_Lean_mkConst(v___x_982_, v_us_955_);
lean_inc_ref(v_type_948_);
v___x_984_ = l_Lean_mkLambda(v_declName_947_, v___x_967_, v_type_948_, v_proof_962_);
v_proof_985_ = l_Lean_mkApp6(v___x_983_, v_type_948_, v___x_970_, v___y_949_, v___x_972_, v___x_968_, v___x_984_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v_proof_985_);
lean_ctor_set(v___x_965_, 3, v_exprResult_974_);
lean_ctor_set(v___x_965_, 2, v_exprInit_973_);
lean_ctor_set(v___x_965_, 1, v_exprType_971_);
lean_ctor_set(v___x_965_, 0, v_expr_969_);
v___x_987_ = v___x_965_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_expr_969_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_exprType_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_exprInit_973_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_exprResult_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_proof_985_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*5, v___x_956_);
v___x_988_ = lean_apply_2(v_toPure_954_, lean_box(0), v___x_987_);
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_947_ = stack[0].m_obj;
lean_object* v_type_948_ = stack[1].m_obj;
lean_object* v___y_949_ = stack[2].m_obj;
lean_object* v_value_950_ = stack[3].m_obj;
uint8_t v___y_951_ = stack[4].m_num;
lean_object* v___x_952_ = stack[5].m_obj;
uint8_t v___y_953_ = stack[6].m_num;
lean_object* v_toPure_954_ = stack[7].m_obj;
lean_object* v_us_955_ = stack[8].m_obj;
uint8_t v___x_956_ = stack[9].m_num;
lean_object* v_rb_957_ = stack[10].m_obj;
lean_object* v_res_991_;
v_res_991_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_947_, v_type_948_, v___y_949_, v_value_950_, v___y_951_, v___x_952_, v___y_953_, v_toPure_954_, v_us_955_, v___x_956_, v_rb_957_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_992_, lean_object* v_type_993_, lean_object* v___y_994_, lean_object* v_value_995_, lean_object* v___y_996_, lean_object* v___x_997_, lean_object* v___y_998_, lean_object* v_toPure_999_, lean_object* v_us_1000_, lean_object* v___x_1001_, lean_object* v_rb_1002_){
_start:
{
uint8_t v___y_8282__boxed_1003_; uint8_t v___y_8284__boxed_1004_; uint8_t v___x_8285__boxed_1005_; lean_object* v_res_1006_; 
v___y_8282__boxed_1003_ = lean_unbox(v___y_996_);
v___y_8284__boxed_1004_ = lean_unbox(v___y_998_);
v___x_8285__boxed_1005_ = lean_unbox(v___x_1001_);
v_res_1006_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_992_, v_type_993_, v___y_994_, v_value_995_, v___y_8282__boxed_1003_, v___x_997_, v___y_8284__boxed_1004_, v_toPure_999_, v_us_1000_, v___x_8285__boxed_1005_, v_rb_1002_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1007_, lean_object* v_____x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_apply_1(v___f_1007_, v_____x_1008_);
return v___x_1009_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1014_, lean_object* v_declName_1015_, lean_object* v_type_1016_, lean_object* v_value_1017_, lean_object* v_us_1018_, lean_object* v___x_1019_, uint8_t v___x_1020_, lean_object* v_toPure_1021_, lean_object* v_rb_1022_){
_start:
{
lean_object* v_expr_1023_; lean_object* v_exprType_1024_; lean_object* v_exprInit_1025_; lean_object* v_exprResult_1026_; lean_object* v_proof_1027_; uint8_t v_modified_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1056_; 
v_expr_1023_ = lean_ctor_get(v_rb_1022_, 0);
v_exprType_1024_ = lean_ctor_get(v_rb_1022_, 1);
v_exprInit_1025_ = lean_ctor_get(v_rb_1022_, 2);
v_exprResult_1026_ = lean_ctor_get(v_rb_1022_, 3);
v_proof_1027_ = lean_ctor_get(v_rb_1022_, 4);
v_modified_1028_ = lean_ctor_get_uint8(v_rb_1022_, sizeof(void*)*5);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_rb_1022_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1030_ = v_rb_1022_;
v_isShared_1031_ = v_isSharedCheck_1056_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_proof_1027_);
lean_inc(v_exprResult_1026_);
lean_inc(v_exprInit_1025_);
lean_inc(v_exprType_1024_);
lean_inc(v_expr_1023_);
lean_dec(v_rb_1022_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1056_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_expr_1032_; lean_object* v_exprType_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v_exprInit_1036_; lean_object* v_exprResult_1037_; 
v_expr_1032_ = lean_expr_lower_loose_bvars(v_expr_1023_, v___x_1014_, v___x_1014_);
lean_dec_ref(v_expr_1023_);
v_exprType_1033_ = lean_expr_lower_loose_bvars(v_exprType_1024_, v___x_1014_, v___x_1014_);
lean_dec_ref(v_exprType_1024_);
v___x_1034_ = 0;
lean_inc_ref(v_type_1016_);
lean_inc(v_declName_1015_);
v___x_1035_ = l_Lean_mkLambda(v_declName_1015_, v___x_1034_, v_type_1016_, v_exprInit_1025_);
lean_inc_ref(v_value_1017_);
lean_inc_ref(v___x_1035_);
v_exprInit_1036_ = l_Lean_Expr_app___override(v___x_1035_, v_value_1017_);
v_exprResult_1037_ = lean_expr_lower_loose_bvars(v_exprResult_1026_, v___x_1014_, v___x_1014_);
lean_dec_ref(v_exprResult_1026_);
if (v_modified_1028_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_proof_1043_; lean_object* v___x_1045_; 
lean_dec_ref(v___x_1035_);
lean_dec_ref(v_proof_1027_);
lean_dec(v_declName_1015_);
v___x_1038_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1039_ = l_Lean_mkConst(v___x_1038_, v_us_1018_);
v___x_1040_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1041_ = l_Lean_mkConst(v___x_1040_, v___x_1019_);
lean_inc_ref_n(v_expr_1032_, 3);
lean_inc_ref_n(v_exprType_1033_, 2);
v___x_1042_ = l_Lean_mkAppB(v___x_1041_, v_exprType_1033_, v_expr_1032_);
v_proof_1043_ = l_Lean_mkApp6(v___x_1039_, v_type_1016_, v_exprType_1033_, v_value_1017_, v_expr_1032_, v_expr_1032_, v___x_1042_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 4, v_proof_1043_);
lean_ctor_set(v___x_1030_, 3, v_exprResult_1037_);
lean_ctor_set(v___x_1030_, 2, v_exprInit_1036_);
lean_ctor_set(v___x_1030_, 1, v_exprType_1033_);
lean_ctor_set(v___x_1030_, 0, v_expr_1032_);
v___x_1045_ = v___x_1030_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_expr_1032_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_exprType_1033_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_exprInit_1036_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_exprResult_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_proof_1043_);
v___x_1045_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*5, v___x_1020_);
v___x_1046_ = lean_apply_2(v_toPure_1021_, lean_box(0), v___x_1045_);
return v___x_1046_;
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_proof_1051_; lean_object* v___x_1053_; 
lean_dec(v___x_1019_);
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1049_ = l_Lean_mkConst(v___x_1048_, v_us_1018_);
lean_inc_ref(v_type_1016_);
v___x_1050_ = l_Lean_mkLambda(v_declName_1015_, v___x_1034_, v_type_1016_, v_proof_1027_);
lean_inc_ref(v_expr_1032_);
lean_inc_ref(v_exprType_1033_);
v_proof_1051_ = l_Lean_mkApp6(v___x_1049_, v_type_1016_, v_exprType_1033_, v_value_1017_, v___x_1035_, v_expr_1032_, v___x_1050_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 4, v_proof_1051_);
lean_ctor_set(v___x_1030_, 3, v_exprResult_1037_);
lean_ctor_set(v___x_1030_, 2, v_exprInit_1036_);
lean_ctor_set(v___x_1030_, 1, v_exprType_1033_);
lean_ctor_set(v___x_1030_, 0, v_expr_1032_);
v___x_1053_ = v___x_1030_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_expr_1032_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_exprType_1033_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_exprInit_1036_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v_exprResult_1037_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v_proof_1051_);
v___x_1053_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; 
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*5, v___x_1020_);
v___x_1054_ = lean_apply_2(v_toPure_1021_, lean_box(0), v___x_1053_);
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1014_ = stack[0].m_obj;
lean_object* v_declName_1015_ = stack[1].m_obj;
lean_object* v_type_1016_ = stack[2].m_obj;
lean_object* v_value_1017_ = stack[3].m_obj;
lean_object* v_us_1018_ = stack[4].m_obj;
lean_object* v___x_1019_ = stack[5].m_obj;
uint8_t v___x_1020_ = stack[6].m_num;
lean_object* v_toPure_1021_ = stack[7].m_obj;
lean_object* v_rb_1022_ = stack[8].m_obj;
lean_object* v_res_1057_;
v_res_1057_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1014_, v_declName_1015_, v_type_1016_, v_value_1017_, v_us_1018_, v___x_1019_, v___x_1020_, v_toPure_1021_, v_rb_1022_);
stack->m_obj
 = v_res_1057_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1058_, lean_object* v_declName_1059_, lean_object* v_type_1060_, lean_object* v_value_1061_, lean_object* v_us_1062_, lean_object* v___x_1063_, lean_object* v___x_1064_, lean_object* v_toPure_1065_, lean_object* v_rb_1066_){
_start:
{
uint8_t v___x_8414__boxed_1067_; lean_object* v_res_1068_; 
v___x_8414__boxed_1067_ = lean_unbox(v___x_1064_);
v_res_1068_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1058_, v_declName_1059_, v_type_1060_, v_value_1061_, v_us_1062_, v___x_1063_, v___x_8414__boxed_1067_, v_toPure_1065_, v_rb_1066_);
lean_dec(v___x_1058_);
return v_res_1068_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1075_, lean_object* v_declName_1076_, lean_object* v_val_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_toMonadRef_1080_, lean_object* v___x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_toCold_1090_; lean_object* v_options_1091_; uint8_t v_hasTrace_1092_; 
v_toCold_1090_ = lean_ctor_get(v___y_1084_, 0);
v_options_1091_ = lean_ctor_get(v_toCold_1090_, 2);
v_hasTrace_1092_ = lean_ctor_get_uint8(v_options_1091_, sizeof(void*)*1);
if (v_hasTrace_1092_ == 0)
{
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_toMonadRef_1080_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v___x_1078_);
lean_dec_ref(v_val_1077_);
lean_dec(v_declName_1076_);
lean_dec(v_cls_1075_);
goto v___jp_1087_;
}
else
{
lean_object* v_inheritedTraceOptions_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_inheritedTraceOptions_1093_ = lean_ctor_get(v_toCold_1090_, 11);
v___x_1094_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1075_);
v___x_1095_ = l_Lean_Name_append(v___x_1094_, v_cls_1075_);
v___x_1096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1093_, v_options_1091_, v___x_1095_);
lean_dec(v___x_1095_);
if (v___x_1096_ == 0)
{
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_toMonadRef_1080_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v___x_1078_);
lean_dec_ref(v_val_1077_);
lean_dec(v_declName_1076_);
lean_dec(v_cls_1075_);
goto v___jp_1087_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_7874__overap_1104_; lean_object* v___x_1105_; 
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1098_ = l_Lean_MessageData_ofName(v_declName_1076_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_MessageData_ofExpr(v_val_1077_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_7874__overap_1104_ = l_Lean_addTrace___redArg(v___x_1078_, v___x_1079_, v_toMonadRef_1080_, v___x_1081_, v_cls_1075_, v___x_1103_);
v___x_1105_ = lean_apply_5(v___x_7874__overap_1104_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, lean_box(0));
return v___x_1105_;
}
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1075_ = stack[0].m_obj;
lean_object* v_declName_1076_ = stack[1].m_obj;
lean_object* v_val_1077_ = stack[2].m_obj;
lean_object* v___x_1078_ = stack[3].m_obj;
lean_object* v___x_1079_ = stack[4].m_obj;
lean_object* v_toMonadRef_1080_ = stack[5].m_obj;
lean_object* v___x_1081_ = stack[6].m_obj;
lean_object* v___y_1082_ = stack[7].m_obj;
lean_object* v___y_1083_ = stack[8].m_obj;
lean_object* v___y_1084_ = stack[9].m_obj;
lean_object* v___y_1085_ = stack[10].m_obj;
lean_object* v_res_1106_;
v_res_1106_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1075_, v_declName_1076_, v_val_1077_, v___x_1078_, v___x_1079_, v_toMonadRef_1080_, v___x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
stack->m_obj
 = v_res_1106_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1107_, lean_object* v_declName_1108_, lean_object* v_val_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v_toMonadRef_1112_, lean_object* v___x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1107_, v_declName_1108_, v_val_1109_, v___x_1110_, v___x_1111_, v_toMonadRef_1112_, v___x_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
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
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1126_, lean_object* v_declName_1127_, lean_object* v_val_1128_, lean_object* v_val_x27_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v_toMonadRef_1132_, lean_object* v___x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_toCold_1142_; lean_object* v_options_1143_; uint8_t v_hasTrace_1144_; 
v_toCold_1142_ = lean_ctor_get(v___y_1136_, 0);
v_options_1143_ = lean_ctor_get(v_toCold_1142_, 2);
v_hasTrace_1144_ = lean_ctor_get_uint8(v_options_1143_, sizeof(void*)*1);
if (v_hasTrace_1144_ == 0)
{
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_toMonadRef_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_val_x27_1129_);
lean_dec_ref(v_val_1128_);
lean_dec(v_declName_1127_);
lean_dec(v_cls_1126_);
goto v___jp_1139_;
}
else
{
lean_object* v_inheritedTraceOptions_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_inheritedTraceOptions_1145_ = lean_ctor_get(v_toCold_1142_, 11);
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1126_);
v___x_1147_ = l_Lean_Name_append(v___x_1146_, v_cls_1126_);
v___x_1148_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1145_, v_options_1143_, v___x_1147_);
lean_dec(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_toMonadRef_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_val_x27_1129_);
lean_dec_ref(v_val_1128_);
lean_dec(v_declName_1127_);
lean_dec(v_cls_1126_);
goto v___jp_1139_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_7618__overap_1160_; lean_object* v___x_1161_; 
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1150_ = l_Lean_MessageData_ofName(v_declName_1127_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofExpr(v_val_1128_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_ofExpr(v_val_x27_1129_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_7618__overap_1160_ = l_Lean_addTrace___redArg(v___x_1130_, v___x_1131_, v_toMonadRef_1132_, v___x_1133_, v_cls_1126_, v___x_1159_);
v___x_1161_ = lean_apply_5(v___x_7618__overap_1160_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, lean_box(0));
return v___x_1161_;
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
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1126_ = stack[0].m_obj;
lean_object* v_declName_1127_ = stack[1].m_obj;
lean_object* v_val_1128_ = stack[2].m_obj;
lean_object* v_val_x27_1129_ = stack[3].m_obj;
lean_object* v___x_1130_ = stack[4].m_obj;
lean_object* v___x_1131_ = stack[5].m_obj;
lean_object* v_toMonadRef_1132_ = stack[6].m_obj;
lean_object* v___x_1133_ = stack[7].m_obj;
lean_object* v___y_1134_ = stack[8].m_obj;
lean_object* v___y_1135_ = stack[9].m_obj;
lean_object* v___y_1136_ = stack[10].m_obj;
lean_object* v___y_1137_ = stack[11].m_obj;
lean_object* v_res_1162_;
v_res_1162_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1126_, v_declName_1127_, v_val_1128_, v_val_x27_1129_, v___x_1130_, v___x_1131_, v_toMonadRef_1132_, v___x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
stack->m_obj
 = v_res_1162_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1163_, lean_object* v_declName_1164_, lean_object* v_val_1165_, lean_object* v_val_x27_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_toMonadRef_1169_, lean_object* v___x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1163_, v_declName_1164_, v_val_1165_, v_val_x27_1166_, v___x_1167_, v___x_1168_, v_toMonadRef_1169_, v___x_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v_res_1176_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_e_1177_, lean_object* v_xs_1178_, lean_object* v_h_1179_, uint8_t v___x_1180_, lean_object* v_toPure_1181_, lean_object* v_toBind_1182_, lean_object* v___f_1183_, lean_object* v_____r_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1185_ = lean_expr_abstract(v_e_1177_, v_xs_1178_);
v___x_1186_ = lean_expr_abstract(v_h_1179_, v_xs_1178_);
v___x_1187_ = lean_box(v___x_1180_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___x_1186_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_apply_2(v_toPure_1181_, lean_box(0), v___x_1189_);
v___x_1191_ = lean_apply_4(v_toBind_1182_, lean_box(0), lean_box(0), v___x_1190_, v___f_1183_);
return v___x_1191_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1177_ = stack[0].m_obj;
lean_object* v_xs_1178_ = stack[1].m_obj;
lean_object* v_h_1179_ = stack[2].m_obj;
uint8_t v___x_1180_ = stack[3].m_num;
lean_object* v_toPure_1181_ = stack[4].m_obj;
lean_object* v_toBind_1182_ = stack[5].m_obj;
lean_object* v___f_1183_ = stack[6].m_obj;
lean_object* v_____r_1184_ = stack[7].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_e_1177_, v_xs_1178_, v_h_1179_, v___x_1180_, v_toPure_1181_, v_toBind_1182_, v___f_1183_, v_____r_1184_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_e_1193_, lean_object* v_xs_1194_, lean_object* v_h_1195_, lean_object* v___x_1196_, lean_object* v_toPure_1197_, lean_object* v_toBind_1198_, lean_object* v___f_1199_, lean_object* v_____r_1200_){
_start:
{
uint8_t v___x_8768__boxed_1201_; lean_object* v_res_1202_; 
v___x_8768__boxed_1201_ = lean_unbox(v___x_1196_);
v_res_1202_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_e_1193_, v_xs_1194_, v_h_1195_, v___x_8768__boxed_1201_, v_toPure_1197_, v_toBind_1198_, v___f_1199_, v_____r_1200_);
lean_dec_ref(v_h_1195_);
lean_dec_ref(v_xs_1194_);
lean_dec_ref(v_e_1193_);
return v_res_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1206_, lean_object* v_declName_1207_, lean_object* v_val_1208_, lean_object* v_e_1209_, lean_object* v___x_1210_, lean_object* v___x_1211_, lean_object* v_toMonadRef_1212_, lean_object* v___x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_toCold_1222_; lean_object* v_options_1223_; uint8_t v_hasTrace_1224_; 
v_toCold_1222_ = lean_ctor_get(v___y_1216_, 0);
v_options_1223_ = lean_ctor_get(v_toCold_1222_, 2);
v_hasTrace_1224_ = lean_ctor_get_uint8(v_options_1223_, sizeof(void*)*1);
if (v_hasTrace_1224_ == 0)
{
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_toMonadRef_1212_);
lean_dec_ref(v___x_1211_);
lean_dec_ref(v___x_1210_);
lean_dec_ref(v_e_1209_);
lean_dec_ref(v_val_1208_);
lean_dec(v_declName_1207_);
lean_dec(v_cls_1206_);
goto v___jp_1219_;
}
else
{
lean_object* v_inheritedTraceOptions_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_inheritedTraceOptions_1225_ = lean_ctor_get(v_toCold_1222_, 11);
v___x_1226_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1206_);
v___x_1227_ = l_Lean_Name_append(v___x_1226_, v_cls_1206_);
v___x_1228_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1225_, v_options_1223_, v___x_1227_);
lean_dec(v___x_1227_);
if (v___x_1228_ == 0)
{
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_toMonadRef_1212_);
lean_dec_ref(v___x_1211_);
lean_dec_ref(v___x_1210_);
lean_dec_ref(v_e_1209_);
lean_dec_ref(v_val_1208_);
lean_dec(v_declName_1207_);
lean_dec(v_cls_1206_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_7768__overap_1240_; lean_object* v___x_1241_; 
v___x_1229_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1230_ = l_Lean_MessageData_ofName(v_declName_1207_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_MessageData_ofExpr(v_val_1208_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_MessageData_ofExpr(v_e_1209_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_7768__overap_1240_ = l_Lean_addTrace___redArg(v___x_1210_, v___x_1211_, v_toMonadRef_1212_, v___x_1213_, v_cls_1206_, v___x_1239_);
v___x_1241_ = lean_apply_5(v___x_7768__overap_1240_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, lean_box(0));
return v___x_1241_;
}
}
v___jp_1219_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1206_ = stack[0].m_obj;
lean_object* v_declName_1207_ = stack[1].m_obj;
lean_object* v_val_1208_ = stack[2].m_obj;
lean_object* v_e_1209_ = stack[3].m_obj;
lean_object* v___x_1210_ = stack[4].m_obj;
lean_object* v___x_1211_ = stack[5].m_obj;
lean_object* v_toMonadRef_1212_ = stack[6].m_obj;
lean_object* v___x_1213_ = stack[7].m_obj;
lean_object* v___y_1214_ = stack[8].m_obj;
lean_object* v___y_1215_ = stack[9].m_obj;
lean_object* v___y_1216_ = stack[10].m_obj;
lean_object* v___y_1217_ = stack[11].m_obj;
lean_object* v_res_1242_;
v_res_1242_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1206_, v_declName_1207_, v_val_1208_, v_e_1209_, v___x_1210_, v___x_1211_, v_toMonadRef_1212_, v___x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
stack->m_obj
 = v_res_1242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1243_, lean_object* v_declName_1244_, lean_object* v_val_1245_, lean_object* v_e_1246_, lean_object* v___x_1247_, lean_object* v___x_1248_, lean_object* v_toMonadRef_1249_, lean_object* v___x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1243_, v_declName_1244_, v_val_1245_, v_e_1246_, v___x_1247_, v___x_1248_, v_toMonadRef_1249_, v___x_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
return v_res_1256_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_level_1266_, lean_object* v___x_1267_, lean_object* v_type_1268_, lean_object* v_value_1269_, uint8_t v___x_1270_, lean_object* v_toPure_1271_, lean_object* v_toBind_1272_, lean_object* v___f_1273_, lean_object* v_xs_1274_, uint8_t v___x_1275_, lean_object* v___f_1276_, lean_object* v_declName_1277_, lean_object* v_val_1278_, lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v_toMonadRef_1281_, lean_object* v___x_1282_, lean_object* v_inst_1283_, lean_object* v_____do__lift_1284_){
_start:
{
if (lean_obj_tag(v_____do__lift_1284_) == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec(v_inst_1283_);
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_toMonadRef_1281_);
lean_dec_ref(v___x_1280_);
lean_dec_ref(v___x_1279_);
lean_dec_ref(v_val_1278_);
lean_dec(v_declName_1277_);
lean_dec(v___f_1276_);
lean_dec_ref(v_xs_1274_);
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_level_1266_);
lean_ctor_set(v___x_1286_, 1, v___x_1267_);
v___x_1287_ = l_Lean_mkConst(v___x_1285_, v___x_1286_);
lean_inc_ref(v_value_1269_);
v___x_1288_ = l_Lean_mkAppB(v___x_1287_, v_type_1268_, v_value_1269_);
v___x_1289_ = lean_box(v___x_1270_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1288_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_value_1269_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_apply_2(v_toPure_1271_, lean_box(0), v___x_1291_);
v___x_1293_ = lean_apply_4(v_toBind_1272_, lean_box(0), lean_box(0), v___x_1292_, v___f_1273_);
return v___x_1293_;
}
else
{
lean_object* v_e_1294_; lean_object* v_h_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; lean_object* v_cls_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v___f_1273_);
lean_dec_ref(v_value_1269_);
lean_dec_ref(v_type_1268_);
lean_dec(v___x_1267_);
lean_dec(v_level_1266_);
v_e_1294_ = lean_ctor_get(v_____do__lift_1284_, 0);
lean_inc_ref_n(v_e_1294_, 2);
v_h_1295_ = lean_ctor_get(v_____do__lift_1284_, 1);
lean_inc_ref(v_h_1295_);
lean_dec_ref_known(v_____do__lift_1284_, 2);
v___x_1296_ = lean_box(v___x_1275_);
lean_inc(v_toBind_1272_);
v___f_1297_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1297_, 0, v_e_1294_);
lean_closure_set(v___f_1297_, 1, v_xs_1274_);
lean_closure_set(v___f_1297_, 2, v_h_1295_);
lean_closure_set(v___f_1297_, 3, v___x_1296_);
lean_closure_set(v___f_1297_, 4, v_toPure_1271_);
lean_closure_set(v___f_1297_, 5, v_toBind_1272_);
lean_closure_set(v___f_1297_, 6, v___f_1276_);
v_cls_1298_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1299_, 0, v_cls_1298_);
lean_closure_set(v___f_1299_, 1, v_declName_1277_);
lean_closure_set(v___f_1299_, 2, v_val_1278_);
lean_closure_set(v___f_1299_, 3, v_e_1294_);
lean_closure_set(v___f_1299_, 4, v___x_1279_);
lean_closure_set(v___f_1299_, 5, v___x_1280_);
lean_closure_set(v___f_1299_, 6, v_toMonadRef_1281_);
lean_closure_set(v___f_1299_, 7, v___x_1282_);
v___x_1300_ = lean_apply_2(v_inst_1283_, lean_box(0), v___f_1299_);
v___x_1301_ = lean_apply_4(v_toBind_1272_, lean_box(0), lean_box(0), v___x_1300_, v___f_1297_);
return v___x_1301_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_1266_ = stack[0].m_obj;
lean_object* v___x_1267_ = stack[1].m_obj;
lean_object* v_type_1268_ = stack[2].m_obj;
lean_object* v_value_1269_ = stack[3].m_obj;
uint8_t v___x_1270_ = stack[4].m_num;
lean_object* v_toPure_1271_ = stack[5].m_obj;
lean_object* v_toBind_1272_ = stack[6].m_obj;
lean_object* v___f_1273_ = stack[7].m_obj;
lean_object* v_xs_1274_ = stack[8].m_obj;
uint8_t v___x_1275_ = stack[9].m_num;
lean_object* v___f_1276_ = stack[10].m_obj;
lean_object* v_declName_1277_ = stack[11].m_obj;
lean_object* v_val_1278_ = stack[12].m_obj;
lean_object* v___x_1279_ = stack[13].m_obj;
lean_object* v___x_1280_ = stack[14].m_obj;
lean_object* v_toMonadRef_1281_ = stack[15].m_obj;
lean_object* v___x_1282_ = stack[16].m_obj;
lean_object* v_inst_1283_ = stack[17].m_obj;
lean_object* v_____do__lift_1284_ = stack[18].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_level_1266_, v___x_1267_, v_type_1268_, v_value_1269_, v___x_1270_, v_toPure_1271_, v_toBind_1272_, v___f_1273_, v_xs_1274_, v___x_1275_, v___f_1276_, v_declName_1277_, v_val_1278_, v___x_1279_, v___x_1280_, v_toMonadRef_1281_, v___x_1282_, v_inst_1283_, v_____do__lift_1284_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_level_1303_ = _args[0];
lean_object* v___x_1304_ = _args[1];
lean_object* v_type_1305_ = _args[2];
lean_object* v_value_1306_ = _args[3];
lean_object* v___x_1307_ = _args[4];
lean_object* v_toPure_1308_ = _args[5];
lean_object* v_toBind_1309_ = _args[6];
lean_object* v___f_1310_ = _args[7];
lean_object* v_xs_1311_ = _args[8];
lean_object* v___x_1312_ = _args[9];
lean_object* v___f_1313_ = _args[10];
lean_object* v_declName_1314_ = _args[11];
lean_object* v_val_1315_ = _args[12];
lean_object* v___x_1316_ = _args[13];
lean_object* v___x_1317_ = _args[14];
lean_object* v_toMonadRef_1318_ = _args[15];
lean_object* v___x_1319_ = _args[16];
lean_object* v_inst_1320_ = _args[17];
lean_object* v_____do__lift_1321_ = _args[18];
_start:
{
uint8_t v___x_8968__boxed_1322_; uint8_t v___x_8970__boxed_1323_; lean_object* v_res_1324_; 
v___x_8968__boxed_1322_ = lean_unbox(v___x_1307_);
v___x_8970__boxed_1323_ = lean_unbox(v___x_1312_);
v_res_1324_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_level_1303_, v___x_1304_, v_type_1305_, v_value_1306_, v___x_8968__boxed_1322_, v_toPure_1308_, v_toBind_1309_, v___f_1310_, v_xs_1311_, v___x_8970__boxed_1323_, v___f_1313_, v_declName_1314_, v_val_1315_, v___x_1316_, v___x_1317_, v_toMonadRef_1318_, v___x_1319_, v_inst_1320_, v_____do__lift_1321_);
return v_res_1324_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1335_ = lean_unsigned_to_nat(8u);
v___x_1336_ = lean_unsigned_to_nat(287u);
v___x_1337_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1339_ = l_mkPanicMessageWithDecl(v___x_1338_, v___x_1337_, v___x_1336_, v___x_1335_, v___x_1334_);
return v___x_1339_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1340_, lean_object* v_type_1341_, lean_object* v_fst_1342_, lean_object* v___x_1343_, lean_object* v_value_1344_, uint8_t v___x_1345_, uint8_t v_fst_1346_, lean_object* v___x_1347_, uint8_t v___x_1348_, lean_object* v_toPure_1349_, lean_object* v_us_1350_, lean_object* v_snd_1351_, lean_object* v___x_1352_, lean_object* v_rb_1353_){
_start:
{
lean_object* v_expr_1354_; lean_object* v_exprType_1355_; lean_object* v_exprInit_1356_; lean_object* v_exprResult_1357_; lean_object* v_proof_1358_; uint8_t v_modified_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1404_; 
v_expr_1354_ = lean_ctor_get(v_rb_1353_, 0);
v_exprType_1355_ = lean_ctor_get(v_rb_1353_, 1);
v_exprInit_1356_ = lean_ctor_get(v_rb_1353_, 2);
v_exprResult_1357_ = lean_ctor_get(v_rb_1353_, 3);
v_proof_1358_ = lean_ctor_get(v_rb_1353_, 4);
v_modified_1359_ = lean_ctor_get_uint8(v_rb_1353_, sizeof(void*)*5);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_rb_1353_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1361_ = v_rb_1353_;
v_isShared_1362_ = v_isSharedCheck_1404_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_proof_1358_);
lean_inc(v_exprResult_1357_);
lean_inc(v_exprInit_1356_);
lean_inc(v_exprType_1355_);
lean_inc(v_expr_1354_);
lean_dec(v_rb_1353_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1404_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_expr_has_loose_bvar(v_exprType_1355_, v___x_1363_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v_expr_1367_; lean_object* v_exprType_1368_; lean_object* v___x_1369_; lean_object* v_exprInit_1370_; lean_object* v_exprResult_1371_; 
v___x_1365_ = 0;
lean_inc_ref_n(v_type_1341_, 3);
lean_inc_n(v_declName_1340_, 3);
v___x_1366_ = l_Lean_mkLambda(v_declName_1340_, v___x_1365_, v_type_1341_, v_expr_1354_);
lean_inc_ref_n(v_fst_1342_, 2);
lean_inc_ref(v___x_1366_);
v_expr_1367_ = l_Lean_Expr_app___override(v___x_1366_, v_fst_1342_);
v_exprType_1368_ = lean_expr_lower_loose_bvars(v_exprType_1355_, v___x_1343_, v___x_1343_);
lean_dec_ref(v_exprType_1355_);
v___x_1369_ = l_Lean_mkLambda(v_declName_1340_, v___x_1365_, v_type_1341_, v_exprInit_1356_);
lean_inc_ref(v_value_1344_);
lean_inc_ref(v___x_1369_);
v_exprInit_1370_ = l_Lean_Expr_app___override(v___x_1369_, v_value_1344_);
v_exprResult_1371_ = l_Lean_Expr_letE___override(v_declName_1340_, v_type_1341_, v_fst_1342_, v_exprResult_1357_, v___x_1345_);
if (v_fst_1346_ == 0)
{
lean_dec_ref(v_snd_1351_);
lean_dec_ref(v_fst_1342_);
if (v_modified_1359_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_proof_1374_; lean_object* v___x_1376_; 
lean_dec_ref(v___x_1369_);
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_proof_1358_);
lean_dec(v_us_1350_);
lean_dec_ref(v_value_1344_);
lean_dec_ref(v_type_1341_);
lean_dec(v_declName_1340_);
v___x_1372_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1373_ = l_Lean_mkConst(v___x_1372_, v___x_1347_);
lean_inc_ref(v_expr_1367_);
lean_inc_ref(v_exprType_1368_);
v_proof_1374_ = l_Lean_mkAppB(v___x_1373_, v_exprType_1368_, v_expr_1367_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v_proof_1374_);
lean_ctor_set(v___x_1361_, 3, v_exprResult_1371_);
lean_ctor_set(v___x_1361_, 2, v_exprInit_1370_);
lean_ctor_set(v___x_1361_, 1, v_exprType_1368_);
lean_ctor_set(v___x_1361_, 0, v_expr_1367_);
v___x_1376_ = v___x_1361_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_expr_1367_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_exprType_1368_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_exprInit_1370_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_exprResult_1371_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_proof_1374_);
v___x_1376_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; 
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5, v___x_1348_);
v___x_1377_ = lean_apply_2(v_toPure_1349_, lean_box(0), v___x_1376_);
return v___x_1377_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_proof_1382_; lean_object* v___x_1384_; 
lean_dec(v___x_1347_);
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1380_ = l_Lean_mkConst(v___x_1379_, v_us_1350_);
lean_inc_ref(v_type_1341_);
v___x_1381_ = l_Lean_mkLambda(v_declName_1340_, v___x_1365_, v_type_1341_, v_proof_1358_);
lean_inc_ref(v_exprType_1368_);
v_proof_1382_ = l_Lean_mkApp6(v___x_1380_, v_type_1341_, v_exprType_1368_, v_value_1344_, v___x_1369_, v___x_1366_, v___x_1381_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v_proof_1382_);
lean_ctor_set(v___x_1361_, 3, v_exprResult_1371_);
lean_ctor_set(v___x_1361_, 2, v_exprInit_1370_);
lean_ctor_set(v___x_1361_, 1, v_exprType_1368_);
lean_ctor_set(v___x_1361_, 0, v_expr_1367_);
v___x_1384_ = v___x_1361_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_expr_1367_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_exprType_1368_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_exprInit_1370_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_exprResult_1371_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_proof_1382_);
v___x_1384_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*5, v___x_1345_);
v___x_1385_ = lean_apply_2(v_toPure_1349_, lean_box(0), v___x_1384_);
return v___x_1385_;
}
}
}
else
{
lean_dec(v___x_1347_);
if (v_modified_1359_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_proof_1389_; lean_object* v___x_1391_; 
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_proof_1358_);
lean_dec(v_declName_1340_);
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1388_ = l_Lean_mkConst(v___x_1387_, v_us_1350_);
lean_inc_ref(v_exprType_1368_);
v_proof_1389_ = l_Lean_mkApp6(v___x_1388_, v_type_1341_, v_exprType_1368_, v_value_1344_, v_fst_1342_, v___x_1369_, v_snd_1351_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v_proof_1389_);
lean_ctor_set(v___x_1361_, 3, v_exprResult_1371_);
lean_ctor_set(v___x_1361_, 2, v_exprInit_1370_);
lean_ctor_set(v___x_1361_, 1, v_exprType_1368_);
lean_ctor_set(v___x_1361_, 0, v_expr_1367_);
v___x_1391_ = v___x_1361_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_expr_1367_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_exprType_1368_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_exprInit_1370_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_exprResult_1371_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_proof_1389_);
v___x_1391_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5, v___x_1345_);
v___x_1392_ = lean_apply_2(v_toPure_1349_, lean_box(0), v___x_1391_);
return v___x_1392_;
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_proof_1397_; lean_object* v___x_1399_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1395_ = l_Lean_mkConst(v___x_1394_, v_us_1350_);
lean_inc_ref(v_type_1341_);
v___x_1396_ = l_Lean_mkLambda(v_declName_1340_, v___x_1365_, v_type_1341_, v_proof_1358_);
lean_inc_ref(v_exprType_1368_);
v_proof_1397_ = l_Lean_mkApp8(v___x_1395_, v_type_1341_, v_exprType_1368_, v_value_1344_, v_fst_1342_, v___x_1369_, v___x_1366_, v_snd_1351_, v___x_1396_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v_proof_1397_);
lean_ctor_set(v___x_1361_, 3, v_exprResult_1371_);
lean_ctor_set(v___x_1361_, 2, v_exprInit_1370_);
lean_ctor_set(v___x_1361_, 1, v_exprType_1368_);
lean_ctor_set(v___x_1361_, 0, v_expr_1367_);
v___x_1399_ = v___x_1361_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_expr_1367_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_exprType_1368_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_exprInit_1370_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_exprResult_1371_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_proof_1397_);
v___x_1399_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5, v___x_1345_);
v___x_1400_ = lean_apply_2(v_toPure_1349_, lean_box(0), v___x_1399_);
return v___x_1400_;
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1361_);
lean_dec_ref(v_proof_1358_);
lean_dec_ref(v_exprResult_1357_);
lean_dec_ref(v_exprInit_1356_);
lean_dec_ref(v_exprType_1355_);
lean_dec_ref(v_expr_1354_);
lean_dec_ref(v_snd_1351_);
lean_dec(v_us_1350_);
lean_dec(v_toPure_1349_);
lean_dec(v___x_1347_);
lean_dec_ref(v_value_1344_);
lean_dec_ref(v_fst_1342_);
lean_dec_ref(v_type_1341_);
lean_dec(v_declName_1340_);
v___x_1402_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1403_ = l_panic___redArg(v___x_1352_, v___x_1402_);
return v___x_1403_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1340_ = stack[0].m_obj;
lean_object* v_type_1341_ = stack[1].m_obj;
lean_object* v_fst_1342_ = stack[2].m_obj;
lean_object* v___x_1343_ = stack[3].m_obj;
lean_object* v_value_1344_ = stack[4].m_obj;
uint8_t v___x_1345_ = stack[5].m_num;
uint8_t v_fst_1346_ = stack[6].m_num;
lean_object* v___x_1347_ = stack[7].m_obj;
uint8_t v___x_1348_ = stack[8].m_num;
lean_object* v_toPure_1349_ = stack[9].m_obj;
lean_object* v_us_1350_ = stack[10].m_obj;
lean_object* v_snd_1351_ = stack[11].m_obj;
lean_object* v___x_1352_ = stack[12].m_obj;
lean_object* v_rb_1353_ = stack[13].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1340_, v_type_1341_, v_fst_1342_, v___x_1343_, v_value_1344_, v___x_1345_, v_fst_1346_, v___x_1347_, v___x_1348_, v_toPure_1349_, v_us_1350_, v_snd_1351_, v___x_1352_, v_rb_1353_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1406_, lean_object* v_type_1407_, lean_object* v_fst_1408_, lean_object* v___x_1409_, lean_object* v_value_1410_, lean_object* v___x_1411_, lean_object* v_fst_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v_toPure_1415_, lean_object* v_us_1416_, lean_object* v_snd_1417_, lean_object* v___x_1418_, lean_object* v_rb_1419_){
_start:
{
uint8_t v___x_9142__boxed_1420_; uint8_t v_fst_9143__boxed_1421_; uint8_t v___x_9145__boxed_1422_; lean_object* v_res_1423_; 
v___x_9142__boxed_1420_ = lean_unbox(v___x_1411_);
v_fst_9143__boxed_1421_ = lean_unbox(v_fst_1412_);
v___x_9145__boxed_1422_ = lean_unbox(v___x_1414_);
v_res_1423_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1406_, v_type_1407_, v_fst_1408_, v___x_1409_, v_value_1410_, v___x_9142__boxed_1420_, v_fst_9143__boxed_1421_, v___x_1413_, v___x_9145__boxed_1422_, v_toPure_1415_, v_us_1416_, v_snd_1417_, v___x_1418_, v_rb_1419_);
lean_dec(v___x_1418_);
lean_dec(v___x_1409_);
return v_res_1423_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_instMonadEIO___redArg();
return v___x_1427_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0);
v___x_1429_ = l_StateRefT_x27_instMonad___redArg(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1436_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1437_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1436_, v___x_1435_);
return v___x_1437_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__8);
v___f_1440_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___x_1441_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1440_, v___x_1439_);
return v___x_1441_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1443_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1444_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__7));
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__11));
v___x_1446_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1445_, v___x_1444_, v___x_1443_);
return v___x_1446_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; 
v___x_1448_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__12);
v___f_1449_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__6));
v___f_1450_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__10));
v___x_1451_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1450_, v___f_1449_, v___x_1448_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__14));
v___x_1454_ = lean_unsigned_to_nat(34u);
v___x_1455_ = lean_unsigned_to_nat(217u);
v___x_1456_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1458_ = l_mkPanicMessageWithDecl(v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_, v___x_1453_);
return v___x_1458_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1459_, lean_object* v_type_1460_, lean_object* v_value_1461_, uint8_t v___y_1462_, lean_object* v___x_1463_, lean_object* v_toPure_1464_, lean_object* v_us_1465_, uint8_t v___x_1466_, lean_object* v_decl_1467_, lean_object* v_x_1468_, lean_object* v_i_1469_, lean_object* v_xs_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_info_1475_, lean_object* v_fixed_1476_, lean_object* v_used_1477_, lean_object* v_body_1478_, lean_object* v_toBind_1479_, lean_object* v_withNewLemmas_1480_, lean_object* v_val_x27_1481_, lean_object* v_val_1482_, uint8_t v___x_1483_, lean_object* v_____r_1484_){
_start:
{
uint8_t v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1504_; uint8_t v___x_1506_; 
v___x_1506_ = lean_expr_eqv(v_val_1482_, v_val_x27_1481_);
if (v___x_1506_ == 0)
{
v___y_1504_ = v___y_1462_;
goto v___jp_1503_;
}
else
{
v___y_1504_ = v___x_1483_;
goto v___jp_1503_;
}
v___jp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1488_ = lean_box(v___y_1462_);
v___x_1489_ = lean_box(v___y_1486_);
v___x_1490_ = lean_box(v___x_1466_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_1491_, 0, v_declName_1459_);
lean_closure_set(v___f_1491_, 1, v_type_1460_);
lean_closure_set(v___f_1491_, 2, v___y_1487_);
lean_closure_set(v___f_1491_, 3, v_value_1461_);
lean_closure_set(v___f_1491_, 4, v___x_1488_);
lean_closure_set(v___f_1491_, 5, v___x_1463_);
lean_closure_set(v___f_1491_, 6, v___x_1489_);
lean_closure_set(v___f_1491_, 7, v_toPure_1464_);
lean_closure_set(v___f_1491_, 8, v_us_1465_);
lean_closure_set(v___f_1491_, 9, v___x_1490_);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_decl_1467_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_mk_empty_array_with_capacity(v___x_1494_);
lean_inc_ref(v_x_1468_);
v___x_1496_ = lean_array_push(v___x_1495_, v_x_1468_);
v___x_1497_ = lean_nat_add(v_i_1469_, v___x_1494_);
v___x_1498_ = lean_array_push(v_xs_1470_, v_x_1468_);
lean_inc_ref(v_inst_1473_);
lean_inc_ref(v_inst_1471_);
v___x_1499_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1471_, v_inst_1472_, v_inst_1473_, v_inst_1474_, v_info_1475_, v_fixed_1476_, v_used_1477_, v_body_1478_, v___x_1497_, v___x_1498_);
v___x_1500_ = lean_apply_4(v_toBind_1479_, lean_box(0), lean_box(0), v___x_1499_, v___f_1491_);
v___x_1501_ = lean_apply_3(v_withNewLemmas_1480_, lean_box(0), v___x_1496_, v___x_1500_);
v___x_1502_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1473_, v_inst_1471_, v___x_1493_, v___x_1501_);
return v___x_1502_;
}
v___jp_1503_:
{
if (v___y_1504_ == 0)
{
lean_inc_ref(v_value_1461_);
v___y_1486_ = v___y_1504_;
v___y_1487_ = v_value_1461_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_expr_abstract(v_val_x27_1481_, v_xs_1470_);
v___y_1486_ = v___y_1504_;
v___y_1487_ = v___x_1505_;
goto v___jp_1485_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1459_ = stack[0].m_obj;
lean_object* v_type_1460_ = stack[1].m_obj;
lean_object* v_value_1461_ = stack[2].m_obj;
uint8_t v___y_1462_ = stack[3].m_num;
lean_object* v___x_1463_ = stack[4].m_obj;
lean_object* v_toPure_1464_ = stack[5].m_obj;
lean_object* v_us_1465_ = stack[6].m_obj;
uint8_t v___x_1466_ = stack[7].m_num;
lean_object* v_decl_1467_ = stack[8].m_obj;
lean_object* v_x_1468_ = stack[9].m_obj;
lean_object* v_i_1469_ = stack[10].m_obj;
lean_object* v_xs_1470_ = stack[11].m_obj;
lean_object* v_inst_1471_ = stack[12].m_obj;
lean_object* v_inst_1472_ = stack[13].m_obj;
lean_object* v_inst_1473_ = stack[14].m_obj;
lean_object* v_inst_1474_ = stack[15].m_obj;
lean_object* v_info_1475_ = stack[16].m_obj;
lean_object* v_fixed_1476_ = stack[17].m_obj;
lean_object* v_used_1477_ = stack[18].m_obj;
lean_object* v_body_1478_ = stack[19].m_obj;
lean_object* v_toBind_1479_ = stack[20].m_obj;
lean_object* v_withNewLemmas_1480_ = stack[21].m_obj;
lean_object* v_val_x27_1481_ = stack[22].m_obj;
lean_object* v_val_1482_ = stack[23].m_obj;
uint8_t v___x_1483_ = stack[24].m_num;
lean_object* v_____r_1484_ = stack[25].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1459_, v_type_1460_, v_value_1461_, v___y_1462_, v___x_1463_, v_toPure_1464_, v_us_1465_, v___x_1466_, v_decl_1467_, v_x_1468_, v_i_1469_, v_xs_1470_, v_inst_1471_, v_inst_1472_, v_inst_1473_, v_inst_1474_, v_info_1475_, v_fixed_1476_, v_used_1477_, v_body_1478_, v_toBind_1479_, v_withNewLemmas_1480_, v_val_x27_1481_, v_val_1482_, v___x_1483_, v_____r_1484_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1508_ = _args[0];
lean_object* v_type_1509_ = _args[1];
lean_object* v_value_1510_ = _args[2];
lean_object* v___y_1511_ = _args[3];
lean_object* v___x_1512_ = _args[4];
lean_object* v_toPure_1513_ = _args[5];
lean_object* v_us_1514_ = _args[6];
lean_object* v___x_1515_ = _args[7];
lean_object* v_decl_1516_ = _args[8];
lean_object* v_x_1517_ = _args[9];
lean_object* v_i_1518_ = _args[10];
lean_object* v_xs_1519_ = _args[11];
lean_object* v_inst_1520_ = _args[12];
lean_object* v_inst_1521_ = _args[13];
lean_object* v_inst_1522_ = _args[14];
lean_object* v_inst_1523_ = _args[15];
lean_object* v_info_1524_ = _args[16];
lean_object* v_fixed_1525_ = _args[17];
lean_object* v_used_1526_ = _args[18];
lean_object* v_body_1527_ = _args[19];
lean_object* v_toBind_1528_ = _args[20];
lean_object* v_withNewLemmas_1529_ = _args[21];
lean_object* v_val_x27_1530_ = _args[22];
lean_object* v_val_1531_ = _args[23];
lean_object* v___x_1532_ = _args[24];
lean_object* v_____r_1533_ = _args[25];
_start:
{
uint8_t v___y_9477__boxed_1534_; uint8_t v___x_9479__boxed_1535_; uint8_t v___x_9485__boxed_1536_; lean_object* v_res_1537_; 
v___y_9477__boxed_1534_ = lean_unbox(v___y_1511_);
v___x_9479__boxed_1535_ = lean_unbox(v___x_1515_);
v___x_9485__boxed_1536_ = lean_unbox(v___x_1532_);
v_res_1537_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1508_, v_type_1509_, v_value_1510_, v___y_9477__boxed_1534_, v___x_1512_, v_toPure_1513_, v_us_1514_, v___x_9479__boxed_1535_, v_decl_1516_, v_x_1517_, v_i_1518_, v_xs_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_info_1524_, v_fixed_1525_, v_used_1526_, v_body_1527_, v_toBind_1528_, v_withNewLemmas_1529_, v_val_x27_1530_, v_val_1531_, v___x_9485__boxed_1536_, v_____r_1533_);
lean_dec_ref(v_val_1531_);
lean_dec_ref(v_val_x27_1530_);
lean_dec(v_i_1518_);
return v_res_1537_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1538_, lean_object* v_type_1539_, lean_object* v_value_1540_, uint8_t v___y_1541_, lean_object* v___x_1542_, lean_object* v_toPure_1543_, lean_object* v_us_1544_, uint8_t v___x_1545_, lean_object* v_decl_1546_, lean_object* v_x_1547_, lean_object* v_i_1548_, lean_object* v_xs_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_info_1554_, lean_object* v_fixed_1555_, lean_object* v_used_1556_, lean_object* v_body_1557_, lean_object* v_toBind_1558_, lean_object* v_withNewLemmas_1559_, lean_object* v_val_1560_, uint8_t v___x_1561_, lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v_toMonadRef_1564_, lean_object* v___x_1565_, lean_object* v_val_x27_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___f_1570_; lean_object* v_cls_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1567_ = lean_box(v___y_1541_);
v___x_1568_ = lean_box(v___x_1545_);
v___x_1569_ = lean_box(v___x_1561_);
lean_inc_ref(v_val_1560_);
lean_inc_ref(v_val_x27_1566_);
lean_inc(v_toBind_1558_);
lean_inc(v_inst_1551_);
lean_inc(v_declName_1538_);
v___f_1570_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 26, 25);
lean_closure_set(v___f_1570_, 0, v_declName_1538_);
lean_closure_set(v___f_1570_, 1, v_type_1539_);
lean_closure_set(v___f_1570_, 2, v_value_1540_);
lean_closure_set(v___f_1570_, 3, v___x_1567_);
lean_closure_set(v___f_1570_, 4, v___x_1542_);
lean_closure_set(v___f_1570_, 5, v_toPure_1543_);
lean_closure_set(v___f_1570_, 6, v_us_1544_);
lean_closure_set(v___f_1570_, 7, v___x_1568_);
lean_closure_set(v___f_1570_, 8, v_decl_1546_);
lean_closure_set(v___f_1570_, 9, v_x_1547_);
lean_closure_set(v___f_1570_, 10, v_i_1548_);
lean_closure_set(v___f_1570_, 11, v_xs_1549_);
lean_closure_set(v___f_1570_, 12, v_inst_1550_);
lean_closure_set(v___f_1570_, 13, v_inst_1551_);
lean_closure_set(v___f_1570_, 14, v_inst_1552_);
lean_closure_set(v___f_1570_, 15, v_inst_1553_);
lean_closure_set(v___f_1570_, 16, v_info_1554_);
lean_closure_set(v___f_1570_, 17, v_fixed_1555_);
lean_closure_set(v___f_1570_, 18, v_used_1556_);
lean_closure_set(v___f_1570_, 19, v_body_1557_);
lean_closure_set(v___f_1570_, 20, v_toBind_1558_);
lean_closure_set(v___f_1570_, 21, v_withNewLemmas_1559_);
lean_closure_set(v___f_1570_, 22, v_val_x27_1566_);
lean_closure_set(v___f_1570_, 23, v_val_1560_);
lean_closure_set(v___f_1570_, 24, v___x_1569_);
v_cls_1571_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1572_, 0, v_cls_1571_);
lean_closure_set(v___f_1572_, 1, v_declName_1538_);
lean_closure_set(v___f_1572_, 2, v_val_1560_);
lean_closure_set(v___f_1572_, 3, v_val_x27_1566_);
lean_closure_set(v___f_1572_, 4, v___x_1562_);
lean_closure_set(v___f_1572_, 5, v___x_1563_);
lean_closure_set(v___f_1572_, 6, v_toMonadRef_1564_);
lean_closure_set(v___f_1572_, 7, v___x_1565_);
v___x_1573_ = lean_apply_2(v_inst_1551_, lean_box(0), v___f_1572_);
v___x_1574_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1573_, v___f_1570_);
return v___x_1574_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1538_ = stack[0].m_obj;
lean_object* v_type_1539_ = stack[1].m_obj;
lean_object* v_value_1540_ = stack[2].m_obj;
uint8_t v___y_1541_ = stack[3].m_num;
lean_object* v___x_1542_ = stack[4].m_obj;
lean_object* v_toPure_1543_ = stack[5].m_obj;
lean_object* v_us_1544_ = stack[6].m_obj;
uint8_t v___x_1545_ = stack[7].m_num;
lean_object* v_decl_1546_ = stack[8].m_obj;
lean_object* v_x_1547_ = stack[9].m_obj;
lean_object* v_i_1548_ = stack[10].m_obj;
lean_object* v_xs_1549_ = stack[11].m_obj;
lean_object* v_inst_1550_ = stack[12].m_obj;
lean_object* v_inst_1551_ = stack[13].m_obj;
lean_object* v_inst_1552_ = stack[14].m_obj;
lean_object* v_inst_1553_ = stack[15].m_obj;
lean_object* v_info_1554_ = stack[16].m_obj;
lean_object* v_fixed_1555_ = stack[17].m_obj;
lean_object* v_used_1556_ = stack[18].m_obj;
lean_object* v_body_1557_ = stack[19].m_obj;
lean_object* v_toBind_1558_ = stack[20].m_obj;
lean_object* v_withNewLemmas_1559_ = stack[21].m_obj;
lean_object* v_val_1560_ = stack[22].m_obj;
uint8_t v___x_1561_ = stack[23].m_num;
lean_object* v___x_1562_ = stack[24].m_obj;
lean_object* v___x_1563_ = stack[25].m_obj;
lean_object* v_toMonadRef_1564_ = stack[26].m_obj;
lean_object* v___x_1565_ = stack[27].m_obj;
lean_object* v_val_x27_1566_ = stack[28].m_obj;
lean_object* v_res_1575_;
v_res_1575_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1538_, v_type_1539_, v_value_1540_, v___y_1541_, v___x_1542_, v_toPure_1543_, v_us_1544_, v___x_1545_, v_decl_1546_, v_x_1547_, v_i_1548_, v_xs_1549_, v_inst_1550_, v_inst_1551_, v_inst_1552_, v_inst_1553_, v_info_1554_, v_fixed_1555_, v_used_1556_, v_body_1557_, v_toBind_1558_, v_withNewLemmas_1559_, v_val_1560_, v___x_1561_, v___x_1562_, v___x_1563_, v_toMonadRef_1564_, v___x_1565_, v_val_x27_1566_);
stack->m_obj
 = v_res_1575_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1576_ = _args[0];
lean_object* v_type_1577_ = _args[1];
lean_object* v_value_1578_ = _args[2];
lean_object* v___y_1579_ = _args[3];
lean_object* v___x_1580_ = _args[4];
lean_object* v_toPure_1581_ = _args[5];
lean_object* v_us_1582_ = _args[6];
lean_object* v___x_1583_ = _args[7];
lean_object* v_decl_1584_ = _args[8];
lean_object* v_x_1585_ = _args[9];
lean_object* v_i_1586_ = _args[10];
lean_object* v_xs_1587_ = _args[11];
lean_object* v_inst_1588_ = _args[12];
lean_object* v_inst_1589_ = _args[13];
lean_object* v_inst_1590_ = _args[14];
lean_object* v_inst_1591_ = _args[15];
lean_object* v_info_1592_ = _args[16];
lean_object* v_fixed_1593_ = _args[17];
lean_object* v_used_1594_ = _args[18];
lean_object* v_body_1595_ = _args[19];
lean_object* v_toBind_1596_ = _args[20];
lean_object* v_withNewLemmas_1597_ = _args[21];
lean_object* v_val_1598_ = _args[22];
lean_object* v___x_1599_ = _args[23];
lean_object* v___x_1600_ = _args[24];
lean_object* v___x_1601_ = _args[25];
lean_object* v_toMonadRef_1602_ = _args[26];
lean_object* v___x_1603_ = _args[27];
lean_object* v_val_x27_1604_ = _args[28];
_start:
{
uint8_t v___y_9424__boxed_1605_; uint8_t v___x_9426__boxed_1606_; uint8_t v___x_9432__boxed_1607_; lean_object* v_res_1608_; 
v___y_9424__boxed_1605_ = lean_unbox(v___y_1579_);
v___x_9426__boxed_1606_ = lean_unbox(v___x_1583_);
v___x_9432__boxed_1607_ = lean_unbox(v___x_1599_);
v_res_1608_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1576_, v_type_1577_, v_value_1578_, v___y_9424__boxed_1605_, v___x_1580_, v_toPure_1581_, v_us_1582_, v___x_9426__boxed_1606_, v_decl_1584_, v_x_1585_, v_i_1586_, v_xs_1587_, v_inst_1588_, v_inst_1589_, v_inst_1590_, v_inst_1591_, v_info_1592_, v_fixed_1593_, v_used_1594_, v_body_1595_, v_toBind_1596_, v_withNewLemmas_1597_, v_val_1598_, v___x_9432__boxed_1607_, v___x_1600_, v___x_1601_, v_toMonadRef_1602_, v___x_1603_, v_val_x27_1604_);
return v_res_1608_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1609_, lean_object* v_declName_1610_, lean_object* v_type_1611_, lean_object* v_value_1612_, uint8_t v___x_1613_, lean_object* v___x_1614_, uint8_t v___x_1615_, lean_object* v_toPure_1616_, lean_object* v_us_1617_, lean_object* v___x_1618_, lean_object* v_x_1619_, lean_object* v_i_1620_, lean_object* v_xs_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_info_1626_, lean_object* v_fixed_1627_, lean_object* v_used_1628_, lean_object* v_body_1629_, lean_object* v_toBind_1630_, lean_object* v_withNewLemmas_1631_, lean_object* v_____x_1632_){
_start:
{
lean_object* v_snd_1633_; lean_object* v_fst_1634_; lean_object* v_fst_1635_; lean_object* v_snd_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1656_; 
v_snd_1633_ = lean_ctor_get(v_____x_1632_, 1);
lean_inc(v_snd_1633_);
v_fst_1634_ = lean_ctor_get(v_____x_1632_, 0);
lean_inc(v_fst_1634_);
lean_dec_ref(v_____x_1632_);
v_fst_1635_ = lean_ctor_get(v_snd_1633_, 0);
v_snd_1636_ = lean_ctor_get(v_snd_1633_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_snd_1633_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1638_ = v_snd_1633_;
v_isShared_1639_ = v_isSharedCheck_1656_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_snd_1636_);
lean_inc(v_fst_1635_);
lean_dec(v_snd_1633_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1656_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 1);
lean_ctor_set(v___x_1638_, 1, v___x_1640_);
lean_ctor_set(v___x_1638_, 0, v_decl_1609_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_decl_1609_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_box(v___x_1613_);
v___x_1645_ = lean_box(v___x_1615_);
v___f_1646_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 14, 13);
lean_closure_set(v___f_1646_, 0, v_declName_1610_);
lean_closure_set(v___f_1646_, 1, v_type_1611_);
lean_closure_set(v___f_1646_, 2, v_fst_1634_);
lean_closure_set(v___f_1646_, 3, v___x_1643_);
lean_closure_set(v___f_1646_, 4, v_value_1612_);
lean_closure_set(v___f_1646_, 5, v___x_1644_);
lean_closure_set(v___f_1646_, 6, v_fst_1635_);
lean_closure_set(v___f_1646_, 7, v___x_1614_);
lean_closure_set(v___f_1646_, 8, v___x_1645_);
lean_closure_set(v___f_1646_, 9, v_toPure_1616_);
lean_closure_set(v___f_1646_, 10, v_us_1617_);
lean_closure_set(v___f_1646_, 11, v_snd_1636_);
lean_closure_set(v___f_1646_, 12, v___x_1618_);
v___x_1647_ = lean_mk_empty_array_with_capacity(v___x_1643_);
lean_inc_ref(v_x_1619_);
v___x_1648_ = lean_array_push(v___x_1647_, v_x_1619_);
v___x_1649_ = lean_nat_add(v_i_1620_, v___x_1643_);
v___x_1650_ = lean_array_push(v_xs_1621_, v_x_1619_);
lean_inc_ref(v_inst_1624_);
lean_inc_ref(v_inst_1622_);
v___x_1651_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1622_, v_inst_1623_, v_inst_1624_, v_inst_1625_, v_info_1626_, v_fixed_1627_, v_used_1628_, v_body_1629_, v___x_1649_, v___x_1650_);
v___x_1652_ = lean_apply_4(v_toBind_1630_, lean_box(0), lean_box(0), v___x_1651_, v___f_1646_);
v___x_1653_ = lean_apply_3(v_withNewLemmas_1631_, lean_box(0), v___x_1648_, v___x_1652_);
v___x_1654_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1624_, v_inst_1622_, v___x_1642_, v___x_1653_);
return v___x_1654_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1609_ = stack[0].m_obj;
lean_object* v_declName_1610_ = stack[1].m_obj;
lean_object* v_type_1611_ = stack[2].m_obj;
lean_object* v_value_1612_ = stack[3].m_obj;
uint8_t v___x_1613_ = stack[4].m_num;
lean_object* v___x_1614_ = stack[5].m_obj;
uint8_t v___x_1615_ = stack[6].m_num;
lean_object* v_toPure_1616_ = stack[7].m_obj;
lean_object* v_us_1617_ = stack[8].m_obj;
lean_object* v___x_1618_ = stack[9].m_obj;
lean_object* v_x_1619_ = stack[10].m_obj;
lean_object* v_i_1620_ = stack[11].m_obj;
lean_object* v_xs_1621_ = stack[12].m_obj;
lean_object* v_inst_1622_ = stack[13].m_obj;
lean_object* v_inst_1623_ = stack[14].m_obj;
lean_object* v_inst_1624_ = stack[15].m_obj;
lean_object* v_inst_1625_ = stack[16].m_obj;
lean_object* v_info_1626_ = stack[17].m_obj;
lean_object* v_fixed_1627_ = stack[18].m_obj;
lean_object* v_used_1628_ = stack[19].m_obj;
lean_object* v_body_1629_ = stack[20].m_obj;
lean_object* v_toBind_1630_ = stack[21].m_obj;
lean_object* v_withNewLemmas_1631_ = stack[22].m_obj;
lean_object* v_____x_1632_ = stack[23].m_obj;
lean_object* v_res_1657_;
v_res_1657_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1609_, v_declName_1610_, v_type_1611_, v_value_1612_, v___x_1613_, v___x_1614_, v___x_1615_, v_toPure_1616_, v_us_1617_, v___x_1618_, v_x_1619_, v_i_1620_, v_xs_1621_, v_inst_1622_, v_inst_1623_, v_inst_1624_, v_inst_1625_, v_info_1626_, v_fixed_1627_, v_used_1628_, v_body_1629_, v_toBind_1630_, v_withNewLemmas_1631_, v_____x_1632_);
stack->m_obj
 = v_res_1657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1658_ = _args[0];
lean_object* v_declName_1659_ = _args[1];
lean_object* v_type_1660_ = _args[2];
lean_object* v_value_1661_ = _args[3];
lean_object* v___x_1662_ = _args[4];
lean_object* v___x_1663_ = _args[5];
lean_object* v___x_1664_ = _args[6];
lean_object* v_toPure_1665_ = _args[7];
lean_object* v_us_1666_ = _args[8];
lean_object* v___x_1667_ = _args[9];
lean_object* v_x_1668_ = _args[10];
lean_object* v_i_1669_ = _args[11];
lean_object* v_xs_1670_ = _args[12];
lean_object* v_inst_1671_ = _args[13];
lean_object* v_inst_1672_ = _args[14];
lean_object* v_inst_1673_ = _args[15];
lean_object* v_inst_1674_ = _args[16];
lean_object* v_info_1675_ = _args[17];
lean_object* v_fixed_1676_ = _args[18];
lean_object* v_used_1677_ = _args[19];
lean_object* v_body_1678_ = _args[20];
lean_object* v_toBind_1679_ = _args[21];
lean_object* v_withNewLemmas_1680_ = _args[22];
lean_object* v_____x_1681_ = _args[23];
_start:
{
uint8_t v___x_9448__boxed_1682_; uint8_t v___x_9450__boxed_1683_; lean_object* v_res_1684_; 
v___x_9448__boxed_1682_ = lean_unbox(v___x_1662_);
v___x_9450__boxed_1683_ = lean_unbox(v___x_1664_);
v_res_1684_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1658_, v_declName_1659_, v_type_1660_, v_value_1661_, v___x_9448__boxed_1682_, v___x_1663_, v___x_9450__boxed_1683_, v_toPure_1665_, v_us_1666_, v___x_1667_, v_x_1668_, v_i_1669_, v_xs_1670_, v_inst_1671_, v_inst_1672_, v_inst_1673_, v_inst_1674_, v_info_1675_, v_fixed_1676_, v_used_1677_, v_body_1678_, v_toBind_1679_, v_withNewLemmas_1680_, v_____x_1681_);
lean_dec(v_i_1669_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1685_ = _args[0];
lean_object* v_declName_1686_ = _args[1];
lean_object* v_type_1687_ = _args[2];
lean_object* v_value_1688_ = _args[3];
lean_object* v_us_1689_ = _args[4];
lean_object* v___x_1690_ = _args[5];
lean_object* v___x_1691_ = _args[6];
lean_object* v_toPure_1692_ = _args[7];
lean_object* v_i_1693_ = _args[8];
lean_object* v_xs_1694_ = _args[9];
lean_object* v_inst_1695_ = _args[10];
lean_object* v_inst_1696_ = _args[11];
lean_object* v_inst_1697_ = _args[12];
lean_object* v_inst_1698_ = _args[13];
lean_object* v_info_1699_ = _args[14];
lean_object* v_fixed_1700_ = _args[15];
lean_object* v_used_1701_ = _args[16];
lean_object* v_body_1702_ = _args[17];
lean_object* v_toBind_1703_ = _args[18];
lean_object* v_____r_1704_ = _args[19];
_start:
{
uint8_t v___x_9407__boxed_1705_; lean_object* v_res_1706_; 
v___x_9407__boxed_1705_ = lean_unbox(v___x_1691_);
v_res_1706_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1685_, v_declName_1686_, v_type_1687_, v_value_1688_, v_us_1689_, v___x_1690_, v___x_9407__boxed_1705_, v_toPure_1692_, v_i_1693_, v_xs_1694_, v_inst_1695_, v_inst_1696_, v_inst_1697_, v_inst_1698_, v_info_1699_, v_fixed_1700_, v_used_1701_, v_body_1702_, v_toBind_1703_, v_____r_1704_);
lean_dec(v_i_1693_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_info_1711_, lean_object* v_fixed_1712_, lean_object* v_used_1713_, lean_object* v_e_1714_, lean_object* v_i_1715_, lean_object* v_xs_1716_){
_start:
{
lean_object* v___x_1717_; lean_object* v_toApplicative_1718_; lean_object* v_toFunctor_1719_; lean_object* v_toSeq_1720_; lean_object* v_toSeqLeft_1721_; lean_object* v_toSeqRight_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___x_1727_; lean_object* v___f_1728_; lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_toApplicative_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1835_; 
v___x_1717_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v_toApplicative_1718_ = lean_ctor_get(v___x_1717_, 0);
v_toFunctor_1719_ = lean_ctor_get(v_toApplicative_1718_, 0);
v_toSeq_1720_ = lean_ctor_get(v_toApplicative_1718_, 2);
v_toSeqLeft_1721_ = lean_ctor_get(v_toApplicative_1718_, 3);
v_toSeqRight_1722_ = lean_ctor_get(v_toApplicative_1718_, 4);
v___f_1723_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__2));
v___f_1724_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1719_, 2);
v___f_1725_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1725_, 0, v_toFunctor_1719_);
v___f_1726_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1726_, 0, v_toFunctor_1719_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___f_1725_);
lean_ctor_set(v___x_1727_, 1, v___f_1726_);
lean_inc(v_toSeqRight_1722_);
v___f_1728_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1728_, 0, v_toSeqRight_1722_);
lean_inc(v_toSeqLeft_1721_);
v___f_1729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1729_, 0, v_toSeqLeft_1721_);
lean_inc(v_toSeq_1720_);
v___f_1730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1730_, 0, v_toSeq_1720_);
v___x_1731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1727_);
lean_ctor_set(v___x_1731_, 1, v___f_1723_);
lean_ctor_set(v___x_1731_, 2, v___f_1730_);
lean_ctor_set(v___x_1731_, 3, v___f_1729_);
lean_ctor_set(v___x_1731_, 4, v___f_1728_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v___f_1724_);
v___x_1733_ = l_StateRefT_x27_instMonad___redArg(v___x_1732_);
v_toApplicative_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v___x_1733_, 1);
lean_dec(v_unused_1836_);
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1835_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_toApplicative_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1835_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_toFunctor_1738_; lean_object* v_toSeq_1739_; lean_object* v_toSeqLeft_1740_; lean_object* v_toSeqRight_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1833_; 
v_toFunctor_1738_ = lean_ctor_get(v_toApplicative_1734_, 0);
v_toSeq_1739_ = lean_ctor_get(v_toApplicative_1734_, 2);
v_toSeqLeft_1740_ = lean_ctor_get(v_toApplicative_1734_, 3);
v_toSeqRight_1741_ = lean_ctor_get(v_toApplicative_1734_, 4);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_toApplicative_1734_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v_toApplicative_1734_, 1);
lean_dec(v_unused_1834_);
v___x_1743_ = v_toApplicative_1734_;
v_isShared_1744_ = v_isSharedCheck_1833_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_toSeqRight_1741_);
lean_inc(v_toSeqLeft_1740_);
lean_inc(v_toSeq_1739_);
lean_inc(v_toFunctor_1738_);
lean_dec(v_toApplicative_1734_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1833_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___f_1745_; lean_object* v___f_1746_; lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___f_1751_; lean_object* v___f_1752_; lean_object* v___x_1754_; 
v___f_1745_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__4));
v___f_1746_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__5));
lean_inc_ref(v_toFunctor_1738_);
v___f_1747_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1747_, 0, v_toFunctor_1738_);
v___f_1748_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1748_, 0, v_toFunctor_1738_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___f_1747_);
lean_ctor_set(v___x_1749_, 1, v___f_1748_);
v___f_1750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1750_, 0, v_toSeqRight_1741_);
v___f_1751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1751_, 0, v_toSeqLeft_1740_);
v___f_1752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1752_, 0, v_toSeq_1739_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 4, v___f_1750_);
lean_ctor_set(v___x_1743_, 3, v___f_1751_);
lean_ctor_set(v___x_1743_, 2, v___f_1752_);
lean_ctor_set(v___x_1743_, 1, v___f_1745_);
lean_ctor_set(v___x_1743_, 0, v___x_1749_);
v___x_1754_ = v___x_1743_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___f_1745_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v___f_1752_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v___f_1751_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v___f_1750_);
v___x_1754_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___f_1746_);
lean_ctor_set(v___x_1736_, 0, v___x_1754_);
v___x_1756_ = v___x_1736_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___f_1746_);
v___x_1756_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v_toApplicative_1759_; lean_object* v_toMonadRef_1760_; lean_object* v_haveInfo_1761_; lean_object* v_body_1762_; lean_object* v_bodyType_1763_; lean_object* v_level_1764_; lean_object* v_toBind_1765_; lean_object* v_toPure_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1757_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__9);
v___x_1758_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__13);
v_toApplicative_1759_ = lean_ctor_get(v_inst_1707_, 0);
v_toMonadRef_1760_ = lean_ctor_get(v___x_1758_, 0);
v_haveInfo_1761_ = lean_ctor_get(v_info_1711_, 0);
v_body_1762_ = lean_ctor_get(v_info_1711_, 3);
v_bodyType_1763_ = lean_ctor_get(v_info_1711_, 4);
v_level_1764_ = lean_ctor_get(v_info_1711_, 5);
v_toBind_1765_ = lean_ctor_get(v_inst_1707_, 1);
lean_inc(v_toBind_1765_);
v_toPure_1766_ = lean_ctor_get(v_toApplicative_1759_, 1);
lean_inc(v_toPure_1766_);
v___x_1767_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1768_ = lean_array_get_size(v_haveInfo_1761_);
v___x_1769_ = lean_nat_dec_lt(v_i_1715_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v_cls_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc(v_level_1764_);
lean_inc_ref(v_bodyType_1763_);
lean_inc_ref_n(v_body_1762_, 2);
lean_dec(v_i_1715_);
lean_dec_ref(v_used_1713_);
lean_dec_ref(v_fixed_1712_);
lean_dec_ref(v_info_1711_);
lean_dec_ref(v_inst_1709_);
lean_dec_ref(v_inst_1707_);
v___x_1770_ = lean_box(v___x_1769_);
lean_inc(v_toBind_1765_);
v___f_1771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1771_, 0, v_inst_1710_);
lean_closure_set(v___f_1771_, 1, v_bodyType_1763_);
lean_closure_set(v___f_1771_, 2, v_xs_1716_);
lean_closure_set(v___f_1771_, 3, v_level_1764_);
lean_closure_set(v___f_1771_, 4, v_e_1714_);
lean_closure_set(v___f_1771_, 5, v___x_1770_);
lean_closure_set(v___f_1771_, 6, v_toPure_1766_);
lean_closure_set(v___f_1771_, 7, v_body_1762_);
lean_closure_set(v___f_1771_, 8, v_toBind_1765_);
v_cls_1772_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1760_);
v___f_1773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1773_, 0, v_cls_1772_);
lean_closure_set(v___f_1773_, 1, v_body_1762_);
lean_closure_set(v___f_1773_, 2, v___x_1756_);
lean_closure_set(v___f_1773_, 3, v___x_1757_);
lean_closure_set(v___f_1773_, 4, v_toMonadRef_1760_);
lean_closure_set(v___f_1773_, 5, v___x_1767_);
v___x_1774_ = lean_apply_2(v_inst_1708_, lean_box(0), v___f_1773_);
v___x_1775_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1774_, v___f_1771_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = l_Lean_Meta_instInhabitedSimpHaveResult_default;
lean_inc_ref(v_inst_1707_);
v___x_1777_ = l_instInhabitedOfMonad___redArg(v_inst_1707_, v___x_1776_);
if (lean_obj_tag(v_e_1714_) == 8)
{
uint8_t v_nondep_1781_; 
v_nondep_1781_ = lean_ctor_get_uint8(v_e_1714_, sizeof(void*)*4 + 8);
if (v_nondep_1781_ == 1)
{
lean_object* v_declName_1782_; lean_object* v_type_1783_; lean_object* v_value_1784_; lean_object* v_body_1785_; lean_object* v_hinfo_1786_; lean_object* v_decl_1787_; lean_object* v_level_1788_; lean_object* v_x_1789_; lean_object* v_val_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v_us_1793_; uint8_t v___y_1795_; uint8_t v___y_1796_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_declName_1782_ = lean_ctor_get(v_e_1714_, 0);
lean_inc(v_declName_1782_);
v_type_1783_ = lean_ctor_get(v_e_1714_, 1);
lean_inc_ref(v_type_1783_);
v_value_1784_ = lean_ctor_get(v_e_1714_, 2);
lean_inc_ref(v_value_1784_);
v_body_1785_ = lean_ctor_get(v_e_1714_, 3);
lean_inc_ref(v_body_1785_);
lean_dec_ref_known(v_e_1714_, 4);
v_hinfo_1786_ = lean_array_fget_borrowed(v_haveInfo_1761_, v_i_1715_);
v_decl_1787_ = lean_ctor_get(v_hinfo_1786_, 2);
v_level_1788_ = lean_ctor_get(v_hinfo_1786_, 3);
lean_inc_ref(v_decl_1787_);
v_x_1789_ = l_Lean_LocalDecl_toExpr(v_decl_1787_);
v_val_1790_ = l_Lean_LocalDecl_value(v_decl_1787_, v___x_1769_);
v___x_1791_ = lean_box(0);
lean_inc(v_level_1764_);
v___x_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_level_1764_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
lean_inc_ref(v___x_1792_);
lean_inc(v_level_1788_);
v_us_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1793_, 0, v_level_1788_);
lean_ctor_set(v_us_1793_, 1, v___x_1792_);
v___x_1821_ = lean_array_get_size(v_used_1713_);
v___x_1822_ = lean_nat_dec_lt(v_i_1715_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_inc_ref(v_decl_1787_);
goto v___jp_1805_;
}
else
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_array_fget_borrowed(v_used_1713_, v_i_1715_);
v___x_1824_ = lean_unbox(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v_cls_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_x_1789_);
lean_dec(v___x_1777_);
v___x_1825_ = lean_box(v___x_1769_);
lean_inc(v_toBind_1765_);
lean_inc(v_inst_1708_);
lean_inc(v_declName_1782_);
v___f_1826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1826_, 0, v___x_1791_);
lean_closure_set(v___f_1826_, 1, v_declName_1782_);
lean_closure_set(v___f_1826_, 2, v_type_1783_);
lean_closure_set(v___f_1826_, 3, v_value_1784_);
lean_closure_set(v___f_1826_, 4, v_us_1793_);
lean_closure_set(v___f_1826_, 5, v___x_1792_);
lean_closure_set(v___f_1826_, 6, v___x_1825_);
lean_closure_set(v___f_1826_, 7, v_toPure_1766_);
lean_closure_set(v___f_1826_, 8, v_i_1715_);
lean_closure_set(v___f_1826_, 9, v_xs_1716_);
lean_closure_set(v___f_1826_, 10, v_inst_1707_);
lean_closure_set(v___f_1826_, 11, v_inst_1708_);
lean_closure_set(v___f_1826_, 12, v_inst_1709_);
lean_closure_set(v___f_1826_, 13, v_inst_1710_);
lean_closure_set(v___f_1826_, 14, v_info_1711_);
lean_closure_set(v___f_1826_, 15, v_fixed_1712_);
lean_closure_set(v___f_1826_, 16, v_used_1713_);
lean_closure_set(v___f_1826_, 17, v_body_1785_);
lean_closure_set(v___f_1826_, 18, v_toBind_1765_);
v_cls_1827_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__4));
lean_inc_ref(v_toMonadRef_1760_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1828_, 0, v_cls_1827_);
lean_closure_set(v___f_1828_, 1, v_declName_1782_);
lean_closure_set(v___f_1828_, 2, v_val_1790_);
lean_closure_set(v___f_1828_, 3, v___x_1756_);
lean_closure_set(v___f_1828_, 4, v___x_1757_);
lean_closure_set(v___f_1828_, 5, v_toMonadRef_1760_);
lean_closure_set(v___f_1828_, 6, v___x_1767_);
v___x_1829_ = lean_apply_2(v_inst_1708_, lean_box(0), v___f_1828_);
v___x_1830_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1829_, v___f_1826_);
return v___x_1830_;
}
else
{
lean_inc_ref(v_decl_1787_);
goto v___jp_1805_;
}
}
v___jp_1794_:
{
lean_object* v_withNewLemmas_1797_; lean_object* v_dsimp_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_withNewLemmas_1797_ = lean_ctor_get(v_inst_1710_, 0);
lean_inc(v_withNewLemmas_1797_);
v_dsimp_1798_ = lean_ctor_get(v_inst_1710_, 1);
lean_inc(v_dsimp_1798_);
v___x_1799_ = lean_box(v___y_1796_);
v___x_1800_ = lean_box(v___x_1769_);
v___x_1801_ = lean_box(v___y_1795_);
lean_inc_ref(v_toMonadRef_1760_);
lean_inc_ref(v_val_1790_);
lean_inc(v_toBind_1765_);
v___f_1802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 29, 28);
lean_closure_set(v___f_1802_, 0, v_declName_1782_);
lean_closure_set(v___f_1802_, 1, v_type_1783_);
lean_closure_set(v___f_1802_, 2, v_value_1784_);
lean_closure_set(v___f_1802_, 3, v___x_1799_);
lean_closure_set(v___f_1802_, 4, v___x_1792_);
lean_closure_set(v___f_1802_, 5, v_toPure_1766_);
lean_closure_set(v___f_1802_, 6, v_us_1793_);
lean_closure_set(v___f_1802_, 7, v___x_1800_);
lean_closure_set(v___f_1802_, 8, v_decl_1787_);
lean_closure_set(v___f_1802_, 9, v_x_1789_);
lean_closure_set(v___f_1802_, 10, v_i_1715_);
lean_closure_set(v___f_1802_, 11, v_xs_1716_);
lean_closure_set(v___f_1802_, 12, v_inst_1707_);
lean_closure_set(v___f_1802_, 13, v_inst_1708_);
lean_closure_set(v___f_1802_, 14, v_inst_1709_);
lean_closure_set(v___f_1802_, 15, v_inst_1710_);
lean_closure_set(v___f_1802_, 16, v_info_1711_);
lean_closure_set(v___f_1802_, 17, v_fixed_1712_);
lean_closure_set(v___f_1802_, 18, v_used_1713_);
lean_closure_set(v___f_1802_, 19, v_body_1785_);
lean_closure_set(v___f_1802_, 20, v_toBind_1765_);
lean_closure_set(v___f_1802_, 21, v_withNewLemmas_1797_);
lean_closure_set(v___f_1802_, 22, v_val_1790_);
lean_closure_set(v___f_1802_, 23, v___x_1801_);
lean_closure_set(v___f_1802_, 24, v___x_1756_);
lean_closure_set(v___f_1802_, 25, v___x_1757_);
lean_closure_set(v___f_1802_, 26, v_toMonadRef_1760_);
lean_closure_set(v___f_1802_, 27, v___x_1767_);
v___x_1803_ = lean_apply_1(v_dsimp_1798_, v_val_1790_);
v___x_1804_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1803_, v___f_1802_);
return v___x_1804_;
}
v___jp_1805_:
{
uint8_t v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = 0;
v___x_1807_ = lean_array_get_size(v_fixed_1712_);
v___x_1808_ = lean_nat_dec_lt(v_i_1715_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_dec(v___x_1777_);
v___y_1795_ = v___x_1806_;
v___y_1796_ = v___x_1769_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_array_fget_borrowed(v_fixed_1712_, v_i_1715_);
v___x_1810_ = lean_unbox(v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v_withNewLemmas_1811_; lean_object* v_simp_1812_; lean_object* v___x_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_inc_n(v___x_1809_, 2);
lean_inc(v_level_1788_);
v_withNewLemmas_1811_ = lean_ctor_get(v_inst_1710_, 0);
lean_inc(v_withNewLemmas_1811_);
v_simp_1812_ = lean_ctor_get(v_inst_1710_, 2);
lean_inc(v_simp_1812_);
v___x_1813_ = lean_box(v___x_1769_);
lean_inc_n(v_toBind_1765_, 2);
lean_inc(v_inst_1708_);
lean_inc_ref(v_xs_1716_);
lean_inc(v_toPure_1766_);
lean_inc_ref(v_value_1784_);
lean_inc_ref(v_type_1783_);
lean_inc(v_declName_1782_);
v___f_1814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 24, 23);
lean_closure_set(v___f_1814_, 0, v_decl_1787_);
lean_closure_set(v___f_1814_, 1, v_declName_1782_);
lean_closure_set(v___f_1814_, 2, v_type_1783_);
lean_closure_set(v___f_1814_, 3, v_value_1784_);
lean_closure_set(v___f_1814_, 4, v___x_1813_);
lean_closure_set(v___f_1814_, 5, v___x_1792_);
lean_closure_set(v___f_1814_, 6, v___x_1809_);
lean_closure_set(v___f_1814_, 7, v_toPure_1766_);
lean_closure_set(v___f_1814_, 8, v_us_1793_);
lean_closure_set(v___f_1814_, 9, v___x_1777_);
lean_closure_set(v___f_1814_, 10, v_x_1789_);
lean_closure_set(v___f_1814_, 11, v_i_1715_);
lean_closure_set(v___f_1814_, 12, v_xs_1716_);
lean_closure_set(v___f_1814_, 13, v_inst_1707_);
lean_closure_set(v___f_1814_, 14, v_inst_1708_);
lean_closure_set(v___f_1814_, 15, v_inst_1709_);
lean_closure_set(v___f_1814_, 16, v_inst_1710_);
lean_closure_set(v___f_1814_, 17, v_info_1711_);
lean_closure_set(v___f_1814_, 18, v_fixed_1712_);
lean_closure_set(v___f_1814_, 19, v_used_1713_);
lean_closure_set(v___f_1814_, 20, v_body_1785_);
lean_closure_set(v___f_1814_, 21, v_toBind_1765_);
lean_closure_set(v___f_1814_, 22, v_withNewLemmas_1811_);
v___f_1815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1815_, 0, v___f_1814_);
v___x_1816_ = lean_box(v___x_1769_);
lean_inc_ref(v_toMonadRef_1760_);
lean_inc_ref(v_val_1790_);
lean_inc_ref(v___f_1815_);
v___f_1817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_1817_, 0, v_level_1788_);
lean_closure_set(v___f_1817_, 1, v___x_1791_);
lean_closure_set(v___f_1817_, 2, v_type_1783_);
lean_closure_set(v___f_1817_, 3, v_value_1784_);
lean_closure_set(v___f_1817_, 4, v___x_1809_);
lean_closure_set(v___f_1817_, 5, v_toPure_1766_);
lean_closure_set(v___f_1817_, 6, v_toBind_1765_);
lean_closure_set(v___f_1817_, 7, v___f_1815_);
lean_closure_set(v___f_1817_, 8, v_xs_1716_);
lean_closure_set(v___f_1817_, 9, v___x_1816_);
lean_closure_set(v___f_1817_, 10, v___f_1815_);
lean_closure_set(v___f_1817_, 11, v_declName_1782_);
lean_closure_set(v___f_1817_, 12, v_val_1790_);
lean_closure_set(v___f_1817_, 13, v___x_1756_);
lean_closure_set(v___f_1817_, 14, v___x_1757_);
lean_closure_set(v___f_1817_, 15, v_toMonadRef_1760_);
lean_closure_set(v___f_1817_, 16, v___x_1767_);
lean_closure_set(v___f_1817_, 17, v_inst_1708_);
v___x_1818_ = lean_apply_1(v_simp_1812_, v_val_1790_);
v___x_1819_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1818_, v___f_1817_);
return v___x_1819_;
}
else
{
uint8_t v___x_1820_; 
lean_dec(v___x_1777_);
v___x_1820_ = lean_unbox(v___x_1809_);
v___y_1795_ = v___x_1806_;
v___y_1796_ = v___x_1820_;
goto v___jp_1794_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1714_, 4);
lean_dec(v_toPure_1766_);
lean_dec(v_toBind_1765_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_xs_1716_);
lean_dec(v_i_1715_);
lean_dec_ref(v_used_1713_);
lean_dec_ref(v_fixed_1712_);
lean_dec_ref(v_info_1711_);
lean_dec_ref(v_inst_1710_);
lean_dec_ref(v_inst_1709_);
lean_dec(v_inst_1708_);
lean_dec_ref(v_inst_1707_);
goto v___jp_1778_;
}
}
else
{
lean_dec(v_toPure_1766_);
lean_dec(v_toBind_1765_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_xs_1716_);
lean_dec(v_i_1715_);
lean_dec_ref(v_e_1714_);
lean_dec_ref(v_used_1713_);
lean_dec_ref(v_fixed_1712_);
lean_dec_ref(v_info_1711_);
lean_dec_ref(v_inst_1710_);
lean_dec_ref(v_inst_1709_);
lean_dec(v_inst_1708_);
lean_dec_ref(v_inst_1707_);
goto v___jp_1778_;
}
v___jp_1778_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__15);
v___x_1780_ = l_panic___redArg(v___x_1777_, v___x_1779_);
lean_dec(v___x_1777_);
return v___x_1780_;
}
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1837_, lean_object* v_declName_1838_, lean_object* v_type_1839_, lean_object* v_value_1840_, lean_object* v_us_1841_, lean_object* v___x_1842_, uint8_t v___x_1843_, lean_object* v_toPure_1844_, lean_object* v_i_1845_, lean_object* v_xs_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_info_1851_, lean_object* v_fixed_1852_, lean_object* v_used_1853_, lean_object* v_body_1854_, lean_object* v_toBind_1855_, lean_object* v_____r_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v_x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1858_ = l_Lean_mkConst(v___x_1857_, v___x_1837_);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_box(v___x_1843_);
v___f_1861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1861_, 0, v___x_1859_);
lean_closure_set(v___f_1861_, 1, v_declName_1838_);
lean_closure_set(v___f_1861_, 2, v_type_1839_);
lean_closure_set(v___f_1861_, 3, v_value_1840_);
lean_closure_set(v___f_1861_, 4, v_us_1841_);
lean_closure_set(v___f_1861_, 5, v___x_1842_);
lean_closure_set(v___f_1861_, 6, v___x_1860_);
lean_closure_set(v___f_1861_, 7, v_toPure_1844_);
v___x_1862_ = lean_nat_add(v_i_1845_, v___x_1859_);
v___x_1863_ = lean_array_push(v_xs_1846_, v_x_1858_);
v___x_1864_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1847_, v_inst_1848_, v_inst_1849_, v_inst_1850_, v_info_1851_, v_fixed_1852_, v_used_1853_, v_body_1854_, v___x_1862_, v___x_1863_);
v___x_1865_ = lean_apply_4(v_toBind_1855_, lean_box(0), lean_box(0), v___x_1864_, v___f_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1837_ = stack[0].m_obj;
lean_object* v_declName_1838_ = stack[1].m_obj;
lean_object* v_type_1839_ = stack[2].m_obj;
lean_object* v_value_1840_ = stack[3].m_obj;
lean_object* v_us_1841_ = stack[4].m_obj;
lean_object* v___x_1842_ = stack[5].m_obj;
uint8_t v___x_1843_ = stack[6].m_num;
lean_object* v_toPure_1844_ = stack[7].m_obj;
lean_object* v_i_1845_ = stack[8].m_obj;
lean_object* v_xs_1846_ = stack[9].m_obj;
lean_object* v_inst_1847_ = stack[10].m_obj;
lean_object* v_inst_1848_ = stack[11].m_obj;
lean_object* v_inst_1849_ = stack[12].m_obj;
lean_object* v_inst_1850_ = stack[13].m_obj;
lean_object* v_info_1851_ = stack[14].m_obj;
lean_object* v_fixed_1852_ = stack[15].m_obj;
lean_object* v_used_1853_ = stack[16].m_obj;
lean_object* v_body_1854_ = stack[17].m_obj;
lean_object* v_toBind_1855_ = stack[18].m_obj;
lean_object* v_____r_1856_ = stack[19].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1837_, v_declName_1838_, v_type_1839_, v_value_1840_, v_us_1841_, v___x_1842_, v___x_1843_, v_toPure_1844_, v_i_1845_, v_xs_1846_, v_inst_1847_, v_inst_1848_, v_inst_1849_, v_inst_1850_, v_info_1851_, v_fixed_1852_, v_used_1853_, v_body_1854_, v_toBind_1855_, v_____r_1856_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_info_1872_, lean_object* v_fixed_1873_, lean_object* v_used_1874_, lean_object* v_e_1875_, lean_object* v_i_1876_, lean_object* v_xs_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_info_1872_, v_fixed_1873_, v_used_1874_, v_e_1875_, v_i_1876_, v_xs_1877_);
return v___x_1878_;
}
}
lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl(uint8_t v_x_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_box(v_x_1879_);
v___x_1881_ = lean_obj_tag_nat(v___x_1880_);
lean_dec(v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT void l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1879_ = stack[0].m_num;
lean_object* v_res_1882_;
v_res_1882_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl(v_x_1879_);
stack->m_obj
 = v_res_1882_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl___boxed(lean_object* v_x_1883_){
_start:
{
uint8_t v_x_4__boxed_1884_; lean_object* v_res_1885_; 
v_x_4__boxed_1884_ = lean_unbox(v_x_1883_);
v_res_1885_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx___impl(v_x_4__boxed_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_1886_){
_start:
{
lean_inc(v_k_1886_);
return v_k_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_1887_);
lean_dec(v_k_1887_);
return v_res_1888_;
}
}
lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_1889_, lean_object* v_ctorIdx_1890_, uint8_t v_t_1891_, lean_object* v_h_1892_, lean_object* v_k_1893_){
_start:
{
lean_inc(v_k_1893_);
return v_k_1893_;
}
}
LEAN_EXPORT void l_Lean_Meta_ZetaUnusedMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1890_ = stack[1].m_obj;
uint8_t v_t_1891_ = stack[2].m_num;
lean_object* v_k_1893_ = stack[4].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_box(0), v_ctorIdx_1890_, v_t_1891_, lean_box(0), v_k_1893_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_1895_, lean_object* v_ctorIdx_1896_, lean_object* v_t_1897_, lean_object* v_h_1898_, lean_object* v_k_1899_){
_start:
{
uint8_t v_t_boxed_1900_; lean_object* v_res_1901_; 
v_t_boxed_1900_ = lean_unbox(v_t_1897_);
v_res_1901_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_1895_, v_ctorIdx_1896_, v_t_boxed_1900_, v_h_1898_, v_k_1899_);
lean_dec(v_k_1899_);
lean_dec(v_ctorIdx_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_1902_){
_start:
{
lean_inc(v_no_1902_);
return v_no_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_1903_);
lean_dec(v_no_1903_);
return v_res_1904_;
}
}
lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_1905_, uint8_t v_t_1906_, lean_object* v_h_1907_, lean_object* v_no_1908_){
_start:
{
lean_inc(v_no_1908_);
return v_no_1908_;
}
}
LEAN_EXPORT void l_Lean_Meta_ZetaUnusedMode_no_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1906_ = stack[1].m_num;
lean_object* v_no_1908_ = stack[3].m_obj;
lean_object* v_res_1909_;
v_res_1909_ = l_Lean_Meta_ZetaUnusedMode_no_elim(lean_box(0), v_t_1906_, lean_box(0), v_no_1908_);
stack->m_obj
 = v_res_1909_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_1910_, lean_object* v_t_1911_, lean_object* v_h_1912_, lean_object* v_no_1913_){
_start:
{
uint8_t v_t_boxed_1914_; lean_object* v_res_1915_; 
v_t_boxed_1914_ = lean_unbox(v_t_1911_);
v_res_1915_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_1910_, v_t_boxed_1914_, v_h_1912_, v_no_1913_);
lean_dec(v_no_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_1916_){
_start:
{
lean_inc(v_singlePass_1916_);
return v_singlePass_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_1917_);
lean_dec(v_singlePass_1917_);
return v_res_1918_;
}
}
lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_1919_, uint8_t v_t_1920_, lean_object* v_h_1921_, lean_object* v_singlePass_1922_){
_start:
{
lean_inc(v_singlePass_1922_);
return v_singlePass_1922_;
}
}
LEAN_EXPORT void l_Lean_Meta_ZetaUnusedMode_singlePass_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1920_ = stack[1].m_num;
lean_object* v_singlePass_1922_ = stack[3].m_obj;
lean_object* v_res_1923_;
v_res_1923_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_box(0), v_t_1920_, lean_box(0), v_singlePass_1922_);
stack->m_obj
 = v_res_1923_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_1924_, lean_object* v_t_1925_, lean_object* v_h_1926_, lean_object* v_singlePass_1927_){
_start:
{
uint8_t v_t_boxed_1928_; lean_object* v_res_1929_; 
v_t_boxed_1928_ = lean_unbox(v_t_1925_);
v_res_1929_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_1924_, v_t_boxed_1928_, v_h_1926_, v_singlePass_1927_);
lean_dec(v_singlePass_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_1930_){
_start:
{
lean_inc(v_twoPasses_1930_);
return v_twoPasses_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_1931_);
lean_dec(v_twoPasses_1931_);
return v_res_1932_;
}
}
lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_1933_, uint8_t v_t_1934_, lean_object* v_h_1935_, lean_object* v_twoPasses_1936_){
_start:
{
lean_inc(v_twoPasses_1936_);
return v_twoPasses_1936_;
}
}
LEAN_EXPORT void l_Lean_Meta_ZetaUnusedMode_twoPasses_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1934_ = stack[1].m_num;
lean_object* v_twoPasses_1936_ = stack[3].m_obj;
lean_object* v_res_1937_;
v_res_1937_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_box(0), v_t_1934_, lean_box(0), v_twoPasses_1936_);
stack->m_obj
 = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_1938_, lean_object* v_t_1939_, lean_object* v_h_1940_, lean_object* v_twoPasses_1941_){
_start:
{
uint8_t v_t_boxed_1942_; lean_object* v_res_1943_; 
v_t_boxed_1942_ = lean_unbox(v_t_1939_);
v_res_1943_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_1938_, v_t_boxed_1942_, v_h_1940_, v_twoPasses_1941_);
lean_dec(v_twoPasses_1941_);
return v_res_1943_;
}
}
lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_1944_, lean_object* v_b_1945_, lean_object* v_c_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
v___x_1952_ = lean_apply_7(v_k_1944_, v_b_1945_, v_c_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, lean_box(0));
return v___x_1952_;
}
}
LEAN_EXPORT void l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1944_ = stack[0].m_obj;
lean_object* v_b_1945_ = stack[1].m_obj;
lean_object* v_c_1946_ = stack[2].m_obj;
lean_object* v___y_1947_ = stack[3].m_obj;
lean_object* v___y_1948_ = stack[4].m_obj;
lean_object* v___y_1949_ = stack[5].m_obj;
lean_object* v___y_1950_ = stack[6].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_1944_, v_b_1945_, v_c_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_1954_, lean_object* v_b_1955_, lean_object* v_c_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_1954_, v_b_1955_, v_c_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1962_;
}
}
lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_1963_, lean_object* v_k_1964_, uint8_t v_cleanupAnnotations_1965_, uint8_t v_preserveNondepLet_1966_, uint8_t v_nondepLetOnly_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___f_1973_; uint8_t v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1973_, 0, v_k_1964_);
v___x_1974_ = 0;
v___x_1975_ = 1;
v___x_1976_ = lean_box(0);
v___x_1977_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1963_, v___x_1974_, v___x_1975_, v_preserveNondepLet_1966_, v_nondepLetOnly_1967_, v___x_1976_, v___f_1973_, v_cleanupAnnotations_1965_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1977_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1977_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1963_ = stack[0].m_obj;
lean_object* v_k_1964_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1965_ = stack[2].m_num;
uint8_t v_preserveNondepLet_1966_ = stack[3].m_num;
uint8_t v_nondepLetOnly_1967_ = stack[4].m_num;
lean_object* v___y_1968_ = stack[5].m_obj;
lean_object* v___y_1969_ = stack[6].m_obj;
lean_object* v___y_1970_ = stack[7].m_obj;
lean_object* v___y_1971_ = stack[8].m_obj;
lean_object* v_res_1994_;
v_res_1994_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1963_, v_k_1964_, v_cleanupAnnotations_1965_, v_preserveNondepLet_1966_, v_nondepLetOnly_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
stack->m_obj
 = v_res_1994_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_1995_, lean_object* v_k_1996_, lean_object* v_cleanupAnnotations_1997_, lean_object* v_preserveNondepLet_1998_, lean_object* v_nondepLetOnly_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2005_; uint8_t v_preserveNondepLet_boxed_2006_; uint8_t v_nondepLetOnly_boxed_2007_; lean_object* v_res_2008_; 
v_cleanupAnnotations_boxed_2005_ = lean_unbox(v_cleanupAnnotations_1997_);
v_preserveNondepLet_boxed_2006_ = lean_unbox(v_preserveNondepLet_1998_);
v_nondepLetOnly_boxed_2007_ = lean_unbox(v_nondepLetOnly_1999_);
v_res_2008_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_1995_, v_k_1996_, v_cleanupAnnotations_boxed_2005_, v_preserveNondepLet_boxed_2006_, v_nondepLetOnly_boxed_2007_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2008_;
}
}
lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2009_, lean_object* v_e_2010_, lean_object* v_k_2011_, uint8_t v_cleanupAnnotations_2012_, uint8_t v_preserveNondepLet_2013_, uint8_t v_nondepLetOnly_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2010_, v_k_2011_, v_cleanupAnnotations_2012_, v_preserveNondepLet_2013_, v_nondepLetOnly_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT void l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2010_ = stack[1].m_obj;
lean_object* v_k_2011_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2012_ = stack[3].m_num;
uint8_t v_preserveNondepLet_2013_ = stack[4].m_num;
uint8_t v_nondepLetOnly_2014_ = stack[5].m_num;
lean_object* v___y_2015_ = stack[6].m_obj;
lean_object* v___y_2016_ = stack[7].m_obj;
lean_object* v___y_2017_ = stack[8].m_obj;
lean_object* v___y_2018_ = stack[9].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_box(0), v_e_2010_, v_k_2011_, v_cleanupAnnotations_2012_, v_preserveNondepLet_2013_, v_nondepLetOnly_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_e_2023_, lean_object* v_k_2024_, lean_object* v_cleanupAnnotations_2025_, lean_object* v_preserveNondepLet_2026_, lean_object* v_nondepLetOnly_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2033_; uint8_t v_preserveNondepLet_boxed_2034_; uint8_t v_nondepLetOnly_boxed_2035_; lean_object* v_res_2036_; 
v_cleanupAnnotations_boxed_2033_ = lean_unbox(v_cleanupAnnotations_2025_);
v_preserveNondepLet_boxed_2034_ = lean_unbox(v_preserveNondepLet_2026_);
v_nondepLetOnly_boxed_2035_ = lean_unbox(v_nondepLetOnly_2027_);
v_res_2036_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2022_, v_e_2023_, v_k_2024_, v_cleanupAnnotations_boxed_2033_, v_preserveNondepLet_boxed_2034_, v_nondepLetOnly_boxed_2035_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
return v_res_2036_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2037_, lean_object* v_a_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_snd_2043_; lean_object* v_fst_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2099_; 
v_snd_2043_ = lean_ctor_get(v_a_2038_, 1);
v_fst_2044_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2046_ = v_a_2038_;
v_isShared_2047_ = v_isSharedCheck_2099_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_snd_2043_);
lean_inc(v_fst_2044_);
lean_dec(v_a_2038_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2099_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2098_; 
v_fst_2048_ = lean_ctor_get(v_snd_2043_, 0);
v_snd_2049_ = lean_ctor_get(v_snd_2043_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_snd_2043_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2051_ = v_snd_2043_;
v_isShared_2052_ = v_isSharedCheck_2098_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snd_2049_);
lean_inc(v_fst_2048_);
lean_dec(v_snd_2043_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2098_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_nat_dec_lt(v___x_2053_, v_snd_2049_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2056_; 
if (v_isShared_2052_ == 0)
{
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_snd_2049_);
v___x_2056_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2056_);
v___x_2058_ = v___x_2046_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_fst_2044_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
else
{
lean_object* v_fvarSet_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_fvarSet_2062_ = lean_ctor_get(v_fst_2044_, 1);
v___x_2063_ = l_Lean_instInhabitedExpr;
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_nat_sub(v_snd_2049_, v___x_2064_);
lean_dec(v_snd_2049_);
v___x_2066_ = lean_array_get_borrowed(v___x_2063_, v_xs_2037_, v___x_2065_);
v___x_2067_ = l_Lean_Expr_fvarId_x21(v___x_2066_);
v___x_2068_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v___x_2067_, v_fvarSet_2062_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2070_; 
lean_dec(v___x_2067_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2065_);
v___x_2070_ = v___x_2051_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2065_);
v___x_2070_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2070_);
v___x_2072_ = v___x_2046_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_fst_2044_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
v_a_2038_ = v___x_2072_;
goto _start;
}
}
}
else
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_FVarId_getDecl___redArg(v___x_2067_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v___x_2078_ = l_Lean_LocalDecl_type(v_a_2077_);
v___x_2079_ = l_Lean_collectFVars(v_fst_2044_, v___x_2078_);
v___x_2080_ = l_Lean_LocalDecl_value(v_a_2077_, v___x_2054_);
lean_dec(v_a_2077_);
v___x_2081_ = l_Lean_collectFVars(v___x_2079_, v___x_2080_);
lean_inc(v___x_2066_);
v___x_2082_ = lean_array_push(v_fst_2048_, v___x_2066_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2065_);
lean_ctor_set(v___x_2051_, 0, v___x_2082_);
v___x_2084_ = v___x_2051_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2065_);
v___x_2084_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2084_);
lean_ctor_set(v___x_2046_, 0, v___x_2081_);
v___x_2086_ = v___x_2046_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v_a_2038_ = v___x_2086_;
goto _start;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v___x_2065_);
lean_del_object(v___x_2051_);
lean_dec(v_fst_2048_);
lean_del_object(v___x_2046_);
lean_dec(v_fst_2044_);
v_a_2090_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2076_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2076_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2037_ = stack[0].m_obj;
lean_object* v_a_2038_ = stack[1].m_obj;
lean_object* v___y_2039_ = stack[2].m_obj;
lean_object* v___y_2040_ = stack[3].m_obj;
lean_object* v___y_2041_ = stack[4].m_obj;
lean_object* v_res_2100_;
v_res_2100_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2037_, v_a_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
stack->m_obj
 = v_res_2100_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2101_, lean_object* v_a_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2101_, v_a_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v_xs_2101_);
return v_res_2107_;
}
}
lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2108_, lean_object* v_e_2109_, lean_object* v_xs_2110_, lean_object* v_body_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_s_2120_; lean_object* v_i_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2117_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2108_);
lean_ctor_set(v___x_2119_, 2, v___x_2118_);
lean_inc_ref(v_body_2111_);
v_s_2120_ = l_Lean_collectFVars(v___x_2119_, v_body_2111_);
v_i_2121_ = lean_array_get_size(v_xs_2110_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2118_);
lean_ctor_set(v___x_2122_, 1, v_i_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_s_2120_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2110_, v___x_2123_, v___y_2112_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2140_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2140_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2140_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_snd_2129_; lean_object* v_fst_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_snd_2129_ = lean_ctor_get(v_a_2125_, 1);
lean_inc(v_snd_2129_);
lean_dec(v_a_2125_);
v_fst_2130_ = lean_ctor_get(v_snd_2129_, 0);
lean_inc(v_fst_2130_);
lean_dec(v_snd_2129_);
v___x_2131_ = lean_array_get_size(v_fst_2130_);
v___x_2132_ = lean_nat_dec_eq(v___x_2131_, v_i_2121_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; 
lean_del_object(v___x_2127_);
lean_dec_ref(v_e_2109_);
v___x_2133_ = 1;
v___x_2134_ = l_Array_reverse___redArg(v_fst_2130_);
v___x_2135_ = 1;
v___x_2136_ = l_Lean_Meta_mkLetFVars(v___x_2134_, v_body_2111_, v___x_2133_, v___x_2132_, v___x_2135_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v___x_2134_);
return v___x_2136_;
}
else
{
lean_object* v___x_2138_; 
lean_dec(v_fst_2130_);
lean_dec_ref(v_body_2111_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v_e_2109_);
v___x_2138_ = v___x_2127_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_e_2109_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_body_2111_);
lean_dec_ref(v_e_2109_);
v_a_2141_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2124_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2124_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaUnused___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2108_ = stack[0].m_obj;
lean_object* v_e_2109_ = stack[1].m_obj;
lean_object* v_xs_2110_ = stack[2].m_obj;
lean_object* v_body_2111_ = stack[3].m_obj;
lean_object* v___y_2112_ = stack[4].m_obj;
lean_object* v___y_2113_ = stack[5].m_obj;
lean_object* v___y_2114_ = stack[6].m_obj;
lean_object* v___y_2115_ = stack[7].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2108_, v_e_2109_, v_xs_2110_, v_body_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
stack->m_obj
 = v_res_2149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2150_, lean_object* v_e_2151_, lean_object* v_xs_2152_, lean_object* v_body_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2150_, v_e_2151_, v_xs_2152_, v_body_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec_ref(v_xs_2152_);
return v_res_2159_;
}
}
lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; lean_object* v___f_2167_; uint8_t v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2166_ = lean_box(1);
lean_inc_ref(v_e_2160_);
v___f_2167_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2167_, 0, v___x_2166_);
lean_closure_set(v___f_2167_, 1, v_e_2160_);
v___x_2168_ = 0;
v___x_2169_ = 1;
v___x_2170_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2160_, v___f_2167_, v___x_2168_, v___x_2169_, v___x_2168_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
return v___x_2170_;
}
}
LEAN_EXPORT void l_Lean_Meta_zetaUnused_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2160_ = stack[0].m_obj;
lean_object* v_a_2161_ = stack[1].m_obj;
lean_object* v_a_2162_ = stack[2].m_obj;
lean_object* v_a_2163_ = stack[3].m_obj;
lean_object* v_a_2164_ = stack[4].m_obj;
lean_object* v_res_2171_;
v_res_2171_ = l_Lean_Meta_zetaUnused(v_e_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
stack->m_obj
 = v_res_2171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Meta_zetaUnused(v_e_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
return v_res_2178_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2179_, lean_object* v_inst_2180_, lean_object* v_a_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2179_, v_a_2181_, v___y_2182_, v___y_2184_, v___y_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2179_ = stack[0].m_obj;
lean_object* v_a_2181_ = stack[2].m_obj;
lean_object* v___y_2182_ = stack[3].m_obj;
lean_object* v___y_2183_ = stack[4].m_obj;
lean_object* v___y_2184_ = stack[5].m_obj;
lean_object* v___y_2185_ = stack[6].m_obj;
lean_object* v_res_2188_;
v_res_2188_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2179_, lean_box(0), v_a_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
stack->m_obj
 = v_res_2188_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2189_, lean_object* v_inst_2190_, lean_object* v_a_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2189_, v_inst_2190_, v_a_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v_xs_2189_);
return v_res_2197_;
}
}
lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2202_, lean_object* v_source_2203_, lean_object* v_result_2204_, uint8_t v_keepUnused_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
uint8_t v_modified_2211_; 
v_modified_2211_ = lean_ctor_get_uint8(v_result_2204_, sizeof(void*)*5);
if (v_modified_2211_ == 0)
{
if (v_keepUnused_2205_ == 0)
{
lean_object* v_exprType_2212_; lean_object* v___x_2213_; 
v_exprType_2212_ = lean_ctor_get(v_result_2204_, 1);
lean_inc_ref(v_exprType_2212_);
lean_dec_ref(v_result_2204_);
lean_inc_ref(v_source_2203_);
v___x_2213_ = l_Lean_Meta_zetaUnused(v_source_2203_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2232_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2232_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2232_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_expr_eqv(v_a_2214_, v_source_2203_);
lean_dec_ref(v_source_2203_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_u_2202_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_mkConst(v___x_2219_, v___x_2221_);
lean_inc(v_a_2214_);
v___x_2223_ = l_Lean_mkAppB(v___x_2222_, v_exprType_2212_, v_a_2214_);
v___x_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_a_2214_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2224_);
v___x_2226_ = v___x_2216_;
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
lean_dec(v_a_2214_);
lean_dec_ref(v_exprType_2212_);
lean_dec(v_u_2202_);
v___x_2228_ = lean_box(0);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2228_);
v___x_2230_ = v___x_2216_;
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
lean_dec_ref(v_exprType_2212_);
lean_dec_ref(v_source_2203_);
lean_dec(v_u_2202_);
v_a_2233_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2213_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2213_);
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
lean_dec_ref(v_result_2204_);
lean_dec_ref(v_source_2203_);
lean_dec(v_u_2202_);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
else
{
lean_object* v_expr_2243_; lean_object* v_exprType_2244_; lean_object* v_exprInit_2245_; lean_object* v_exprResult_2246_; lean_object* v_proof_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_proof_2255_; 
v_expr_2243_ = lean_ctor_get(v_result_2204_, 0);
lean_inc_ref(v_expr_2243_);
v_exprType_2244_ = lean_ctor_get(v_result_2204_, 1);
lean_inc_ref_n(v_exprType_2244_, 3);
v_exprInit_2245_ = lean_ctor_get(v_result_2204_, 2);
lean_inc_ref(v_exprInit_2245_);
v_exprResult_2246_ = lean_ctor_get(v_result_2204_, 3);
lean_inc_ref_n(v_exprResult_2246_, 2);
v_proof_2247_ = lean_ctor_get(v_result_2204_, 4);
lean_inc_ref(v_proof_2247_);
lean_dec_ref(v_result_2204_);
v___x_2248_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2249_ = lean_box(0);
v___x_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_u_2202_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
lean_inc_ref(v___x_2250_);
v___x_2251_ = l_Lean_mkConst(v___x_2248_, v___x_2250_);
lean_inc_ref(v___x_2251_);
v___x_2252_ = l_Lean_mkApp3(v___x_2251_, v_exprType_2244_, v_exprInit_2245_, v_expr_2243_);
v___x_2253_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2247_, v___x_2252_);
lean_inc_ref(v_source_2203_);
v___x_2254_ = l_Lean_mkApp3(v___x_2251_, v_exprType_2244_, v_source_2203_, v_exprResult_2246_);
v_proof_2255_ = l_Lean_Meta_mkExpectedPropHint(v___x_2253_, v___x_2254_);
if (v_keepUnused_2205_ == 0)
{
lean_object* v___x_2256_; 
lean_inc_ref(v_exprResult_2246_);
v___x_2256_ = l_Lean_Meta_zetaUnused(v_exprResult_2246_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2276_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2276_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2276_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_expr_eqv(v_a_2257_, v_exprResult_2246_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2250_);
v___x_2263_ = l_Lean_mkConst(v___x_2262_, v___x_2250_);
v___x_2264_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2265_ = l_Lean_mkConst(v___x_2264_, v___x_2250_);
lean_inc_n(v_a_2257_, 2);
lean_inc_ref(v_exprType_2244_);
v___x_2266_ = l_Lean_mkAppB(v___x_2265_, v_exprType_2244_, v_a_2257_);
v___x_2267_ = l_Lean_mkApp6(v___x_2263_, v_exprType_2244_, v_source_2203_, v_exprResult_2246_, v_a_2257_, v_proof_2255_, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_a_2257_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2268_);
v___x_2270_ = v___x_2259_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec(v_a_2257_);
lean_dec_ref_known(v___x_2250_, 2);
lean_dec_ref(v_exprType_2244_);
lean_dec_ref(v_source_2203_);
v___x_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_exprResult_2246_);
lean_ctor_set(v___x_2272_, 1, v_proof_2255_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2272_);
v___x_2274_ = v___x_2259_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_proof_2255_);
lean_dec_ref_known(v___x_2250_, 2);
lean_dec_ref(v_exprResult_2246_);
lean_dec_ref(v_exprType_2244_);
lean_dec_ref(v_source_2203_);
v_a_2277_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2256_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2256_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec_ref_known(v___x_2250_, 2);
lean_dec_ref(v_exprType_2244_);
lean_dec_ref(v_source_2203_);
v___x_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_exprResult_2246_);
lean_ctor_set(v___x_2285_, 1, v_proof_2255_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2202_ = stack[0].m_obj;
lean_object* v_source_2203_ = stack[1].m_obj;
lean_object* v_result_2204_ = stack[2].m_obj;
uint8_t v_keepUnused_2205_ = stack[3].m_num;
lean_object* v_a_2206_ = stack[4].m_obj;
lean_object* v_a_2207_ = stack[5].m_obj;
lean_object* v_a_2208_ = stack[6].m_obj;
lean_object* v_a_2209_ = stack[7].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2202_, v_source_2203_, v_result_2204_, v_keepUnused_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2288_, lean_object* v_source_2289_, lean_object* v_result_2290_, lean_object* v_keepUnused_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
uint8_t v_keepUnused_boxed_2297_; lean_object* v_res_2298_; 
v_keepUnused_boxed_2297_ = lean_unbox(v_keepUnused_2291_);
v_res_2298_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2288_, v_source_2289_, v_result_2290_, v_keepUnused_boxed_2297_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2298_;
}
}
lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2299_, lean_object* v_e_2300_, lean_object* v_inst_2301_, uint8_t v_zetaUnusedMode_2302_, uint8_t v___x_2303_, uint8_t v___x_2304_, lean_object* v_r_2305_){
_start:
{
uint8_t v___y_2307_; 
switch(v_zetaUnusedMode_2302_)
{
case 0:
{
v___y_2307_ = v___x_2303_;
goto v___jp_2306_;
}
case 1:
{
v___y_2307_ = v___x_2303_;
goto v___jp_2306_;
}
default: 
{
v___y_2307_ = v___x_2304_;
goto v___jp_2306_;
}
}
v___jp_2306_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = lean_box(v___y_2307_);
v___x_2309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2309_, 0, v_level_2299_);
lean_closure_set(v___x_2309_, 1, v_e_2300_);
lean_closure_set(v___x_2309_, 2, v_r_2305_);
lean_closure_set(v___x_2309_, 3, v___x_2308_);
v___x_2310_ = lean_apply_2(v_inst_2301_, lean_box(0), v___x_2309_);
return v___x_2310_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_simpHaveTelescope___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_2299_ = stack[0].m_obj;
lean_object* v_e_2300_ = stack[1].m_obj;
lean_object* v_inst_2301_ = stack[2].m_obj;
uint8_t v_zetaUnusedMode_2302_ = stack[3].m_num;
uint8_t v___x_2303_ = stack[4].m_num;
uint8_t v___x_2304_ = stack[5].m_num;
lean_object* v_r_2305_ = stack[6].m_obj;
lean_object* v_res_2311_;
v_res_2311_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2299_, v_e_2300_, v_inst_2301_, v_zetaUnusedMode_2302_, v___x_2303_, v___x_2304_, v_r_2305_);
stack->m_obj
 = v_res_2311_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2312_, lean_object* v_e_2313_, lean_object* v_inst_2314_, lean_object* v_zetaUnusedMode_2315_, lean_object* v___x_2316_, lean_object* v___x_2317_, lean_object* v_r_2318_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2319_; uint8_t v___x_289__boxed_2320_; uint8_t v___x_290__boxed_2321_; lean_object* v_res_2322_; 
v_zetaUnusedMode_boxed_2319_ = lean_unbox(v_zetaUnusedMode_2315_);
v___x_289__boxed_2320_ = lean_unbox(v___x_2316_);
v___x_290__boxed_2321_ = lean_unbox(v___x_2317_);
v_res_2322_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2312_, v_e_2313_, v_inst_2314_, v_zetaUnusedMode_boxed_2319_, v___x_289__boxed_2320_, v___x_290__boxed_2321_, v_r_2318_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_info_2328_, lean_object* v_e_2329_, lean_object* v___x_2330_, lean_object* v_toBind_2331_, lean_object* v___f_2332_, lean_object* v_____x_2333_){
_start:
{
lean_object* v_fst_2334_; lean_object* v_snd_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_fst_2334_ = lean_ctor_get(v_____x_2333_, 0);
lean_inc(v_fst_2334_);
v_snd_2335_ = lean_ctor_get(v_____x_2333_, 1);
lean_inc(v_snd_2335_);
lean_dec_ref(v_____x_2333_);
v___x_2336_ = lean_mk_empty_array_with_capacity(v___x_2323_);
v___x_2337_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2324_, v_inst_2325_, v_inst_2326_, v_inst_2327_, v_info_2328_, v_fst_2334_, v_snd_2335_, v_e_2329_, v___x_2330_, v___x_2336_);
v___x_2338_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v___x_2337_, v___f_2332_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_info_2344_, lean_object* v_e_2345_, lean_object* v___x_2346_, lean_object* v_toBind_2347_, lean_object* v___f_2348_, lean_object* v_____x_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2339_, v_inst_2340_, v_inst_2341_, v_inst_2342_, v_inst_2343_, v_info_2344_, v_e_2345_, v___x_2346_, v_toBind_2347_, v___f_2348_, v_____x_2349_);
lean_dec(v___x_2339_);
return v_res_2350_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2353_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2354_ = lean_unsigned_to_nat(2u);
v___x_2355_ = lean_unsigned_to_nat(456u);
v___x_2356_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2357_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2358_ = l_mkPanicMessageWithDecl(v___x_2357_, v___x_2356_, v___x_2355_, v___x_2354_, v___x_2353_);
return v___x_2358_;
}
}
lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2359_, lean_object* v_inst_2360_, uint8_t v_zetaUnusedMode_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_toBind_2365_, lean_object* v___x_2366_, lean_object* v_info_2367_){
_start:
{
lean_object* v_haveInfo_2368_; lean_object* v_level_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_haveInfo_2368_ = lean_ctor_get(v_info_2367_, 0);
v_level_2369_ = lean_ctor_get(v_info_2367_, 5);
v___x_2370_ = lean_array_get_size(v_haveInfo_2368_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_nat_dec_eq(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___f_2378_; uint8_t v___y_2380_; 
v___x_2373_ = 1;
v___x_2374_ = lean_box(v_zetaUnusedMode_2361_);
v___x_2375_ = lean_box(v___x_2373_);
v___x_2376_ = lean_box(v___x_2372_);
lean_inc_n(v_inst_2360_, 2);
lean_inc_ref(v_e_2359_);
lean_inc(v_level_2369_);
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2377_, 0, v_level_2369_);
lean_closure_set(v___f_2377_, 1, v_e_2359_);
lean_closure_set(v___f_2377_, 2, v_inst_2360_);
lean_closure_set(v___f_2377_, 3, v___x_2374_);
lean_closure_set(v___f_2377_, 4, v___x_2375_);
lean_closure_set(v___f_2377_, 5, v___x_2376_);
lean_inc(v_toBind_2365_);
lean_inc_ref(v_info_2367_);
v___f_2378_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2378_, 0, v___x_2370_);
lean_closure_set(v___f_2378_, 1, v_inst_2362_);
lean_closure_set(v___f_2378_, 2, v_inst_2360_);
lean_closure_set(v___f_2378_, 3, v_inst_2363_);
lean_closure_set(v___f_2378_, 4, v_inst_2364_);
lean_closure_set(v___f_2378_, 5, v_info_2367_);
lean_closure_set(v___f_2378_, 6, v_e_2359_);
lean_closure_set(v___f_2378_, 7, v___x_2371_);
lean_closure_set(v___f_2378_, 8, v_toBind_2365_);
lean_closure_set(v___f_2378_, 9, v___f_2377_);
switch(v_zetaUnusedMode_2361_)
{
case 0:
{
v___y_2380_ = v___x_2373_;
goto v___jp_2379_;
}
case 2:
{
v___y_2380_ = v___x_2373_;
goto v___jp_2379_;
}
default: 
{
v___y_2380_ = v___x_2372_;
goto v___jp_2379_;
}
}
v___jp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2381_ = lean_box(v___y_2380_);
v___x_2382_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2382_, 0, v_info_2367_);
lean_closure_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_apply_2(v_inst_2360_, lean_box(0), v___x_2382_);
v___x_2384_ = lean_apply_4(v_toBind_2365_, lean_box(0), lean_box(0), v___x_2383_, v___f_2378_);
return v___x_2384_;
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_info_2367_);
lean_dec(v_toBind_2365_);
lean_dec_ref(v_inst_2364_);
lean_dec_ref(v_inst_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec(v_inst_2360_);
lean_dec_ref(v_e_2359_);
v___x_2385_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2386_ = l_panic___redArg(v___x_2366_, v___x_2385_);
return v___x_2386_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_simpHaveTelescope___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2359_ = stack[0].m_obj;
lean_object* v_inst_2360_ = stack[1].m_obj;
uint8_t v_zetaUnusedMode_2361_ = stack[2].m_num;
lean_object* v_inst_2362_ = stack[3].m_obj;
lean_object* v_inst_2363_ = stack[4].m_obj;
lean_object* v_inst_2364_ = stack[5].m_obj;
lean_object* v_toBind_2365_ = stack[6].m_obj;
lean_object* v___x_2366_ = stack[7].m_obj;
lean_object* v_info_2367_ = stack[8].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2359_, v_inst_2360_, v_zetaUnusedMode_2361_, v_inst_2362_, v_inst_2363_, v_inst_2364_, v_toBind_2365_, v___x_2366_, v_info_2367_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2388_, lean_object* v_inst_2389_, lean_object* v_zetaUnusedMode_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_toBind_2394_, lean_object* v___x_2395_, lean_object* v_info_2396_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2397_; lean_object* v_res_2398_; 
v_zetaUnusedMode_boxed_2397_ = lean_unbox(v_zetaUnusedMode_2390_);
v_res_2398_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2388_, v_inst_2389_, v_zetaUnusedMode_boxed_2397_, v_inst_2391_, v_inst_2392_, v_inst_2393_, v_toBind_2394_, v___x_2395_, v_info_2396_);
lean_dec(v___x_2395_);
return v_res_2398_;
}
}
lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_e_2403_, uint8_t v_zetaUnusedMode_2404_){
_start:
{
lean_object* v_toBind_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; 
v_toBind_2405_ = lean_ctor_get(v_inst_2399_, 1);
lean_inc_n(v_toBind_2405_, 2);
v___x_2406_ = lean_box(0);
lean_inc_ref(v_e_2403_);
v___x_2407_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2407_, 0, v_e_2403_);
lean_inc(v_inst_2400_);
v___x_2408_ = lean_apply_2(v_inst_2400_, lean_box(0), v___x_2407_);
lean_inc_ref(v_inst_2399_);
v___x_2409_ = l_instInhabitedOfMonad___redArg(v_inst_2399_, v___x_2406_);
v___x_2410_ = lean_box(v_zetaUnusedMode_2404_);
v___f_2411_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2411_, 0, v_e_2403_);
lean_closure_set(v___f_2411_, 1, v_inst_2400_);
lean_closure_set(v___f_2411_, 2, v___x_2410_);
lean_closure_set(v___f_2411_, 3, v_inst_2399_);
lean_closure_set(v___f_2411_, 4, v_inst_2401_);
lean_closure_set(v___f_2411_, 5, v_inst_2402_);
lean_closure_set(v___f_2411_, 6, v_toBind_2405_);
lean_closure_set(v___f_2411_, 7, v___x_2409_);
v___x_2412_ = lean_apply_4(v_toBind_2405_, lean_box(0), lean_box(0), v___x_2408_, v___f_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT void l_Lean_Meta_simpHaveTelescope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2399_ = stack[0].m_obj;
lean_object* v_inst_2400_ = stack[1].m_obj;
lean_object* v_inst_2401_ = stack[2].m_obj;
lean_object* v_inst_2402_ = stack[3].m_obj;
lean_object* v_e_2403_ = stack[4].m_obj;
uint8_t v_zetaUnusedMode_2404_ = stack[5].m_num;
lean_object* v_res_2413_;
v_res_2413_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2399_, v_inst_2400_, v_inst_2401_, v_inst_2402_, v_e_2403_, v_zetaUnusedMode_2404_);
stack->m_obj
 = v_res_2413_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_e_2418_, lean_object* v_zetaUnusedMode_2419_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2420_; lean_object* v_res_2421_; 
v_zetaUnusedMode_boxed_2420_ = lean_unbox(v_zetaUnusedMode_2419_);
v_res_2421_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_inst_2417_, v_e_2418_, v_zetaUnusedMode_boxed_2420_);
return v_res_2421_;
}
}
lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_e_2427_, uint8_t v_zetaUnusedMode_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2423_, v_inst_2424_, v_inst_2425_, v_inst_2426_, v_e_2427_, v_zetaUnusedMode_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT void l_Lean_Meta_simpHaveTelescope_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2423_ = stack[1].m_obj;
lean_object* v_inst_2424_ = stack[2].m_obj;
lean_object* v_inst_2425_ = stack[3].m_obj;
lean_object* v_inst_2426_ = stack[4].m_obj;
lean_object* v_e_2427_ = stack[5].m_obj;
uint8_t v_zetaUnusedMode_2428_ = stack[6].m_num;
lean_object* v_res_2430_;
v_res_2430_ = l_Lean_Meta_simpHaveTelescope(lean_box(0), v_inst_2423_, v_inst_2424_, v_inst_2425_, v_inst_2426_, v_e_2427_, v_zetaUnusedMode_2428_);
stack->m_obj
 = v_res_2430_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_e_2436_, lean_object* v_zetaUnusedMode_2437_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2438_; lean_object* v_res_2439_; 
v_zetaUnusedMode_boxed_2438_ = lean_unbox(v_zetaUnusedMode_2437_);
v_res_2439_ = l_Lean_Meta_simpHaveTelescope(v_m_2431_, v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_e_2436_, v_zetaUnusedMode_boxed_2438_);
return v_res_2439_;
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
