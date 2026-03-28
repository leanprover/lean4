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
lean_inc_n(v_a_283_, 2);
lean_dec_ref(v___x_282_);
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
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = ((lean_object*)(l_Lean_Meta_getHaveTelescopeInfo___closed__0));
v___x_568_ = lean_obj_once(&l_Lean_Meta_getHaveTelescopeInfo___closed__5, &l_Lean_Meta_getHaveTelescopeInfo___closed__5_once, _init_l_Lean_Meta_getHaveTelescopeInfo___closed__5);
lean_inc_ref(v_lctx_565_);
v___x_569_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect(v_e_559_, v___x_566_, v___x_568_, v_lctx_565_, v___x_567_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
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
lean_dec_ref(v_a_571_);
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
v___x_639_ = lean_array_get(v___x_638_, v_b_625_, v___x_637_);
lean_dec(v___x_638_);
v___x_640_ = lean_unbox(v___x_639_);
lean_dec(v___x_639_);
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
lean_inc_ref_n(v_e_787_, 3);
lean_inc_ref(v_exprType_786_);
v_proof_796_ = l_Lean_mkAppB(v___x_795_, v_exprType_786_, v_e_787_);
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
uint8_t v___x_12300__boxed_866_; lean_object* v_res_867_; 
v___x_12300__boxed_866_ = lean_unbox(v___x_863_);
v_res_867_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0(v_toApplicative_859_, v_level_860_, v_exprType_861_, v_e_862_, v___x_12300__boxed_866_, v_xs_864_, v_____do__lift_865_);
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
uint8_t v___x_12453__boxed_894_; lean_object* v_res_895_; 
v___x_12453__boxed_894_ = lean_unbox(v___x_890_);
v_res_895_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1(v_inst_884_, v_bodyType_885_, v_xs_886_, v_toApplicative_887_, v_level_888_, v_e_889_, v___x_12453__boxed_894_, v_body_891_, v_toBind_892_, v_____r_893_);
lean_dec_ref(v_bodyType_885_);
return v_res_895_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__4));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(lean_object* v_cls_904_, lean_object* v___x_905_, lean_object* v___f_906_, lean_object* v_body_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_options_918_; uint8_t v_hasTrace_919_; 
v_options_918_ = lean_ctor_get(v___y_912_, 2);
v_hasTrace_919_ = lean_ctor_get_uint8(v_options_918_, sizeof(void*)*1);
if (v_hasTrace_919_ == 0)
{
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_body_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v_cls_904_);
goto v___jp_915_;
}
else
{
lean_object* v_inheritedTraceOptions_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_inheritedTraceOptions_920_ = lean_ctor_get(v___y_912_, 13);
v___x_921_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_904_);
v___x_922_ = l_Lean_Name_append(v___x_921_, v_cls_904_);
v___x_923_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_920_, v_options_918_, v___x_922_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_body_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v_cls_904_);
goto v___jp_915_;
}
else
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_toMonadRef_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_11855__overap_934_; lean_object* v___x_935_; 
v___f_924_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_926_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_927_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_925_, v___x_905_, v___x_926_);
v___x_928_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_924_, v___f_906_, v___x_927_);
v_toMonadRef_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_ref(v_toMonadRef_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__5);
v___x_932_ = l_Lean_MessageData_ofExpr(v_body_907_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_11855__overap_934_ = l_Lean_addTrace___redArg(v___x_908_, v___x_909_, v_toMonadRef_929_, v___x_930_, v_cls_904_, v___x_933_);
v___x_935_ = lean_apply_5(v___x_11855__overap_934_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
return v___x_935_;
}
}
v___jp_915_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed(lean_object* v_cls_936_, lean_object* v___x_937_, lean_object* v___f_938_, lean_object* v_body_939_, lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2(v_cls_936_, v___x_937_, v___f_938_, v_body_939_, v___x_940_, v___x_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(lean_object* v_declName_950_, lean_object* v_type_951_, lean_object* v___y_952_, lean_object* v_value_953_, uint8_t v_nondep_954_, lean_object* v_toApplicative_955_, lean_object* v___x_956_, uint8_t v___y_957_, lean_object* v_us_958_, lean_object* v_rb_959_){
_start:
{
lean_object* v_expr_960_; lean_object* v_exprType_961_; lean_object* v_exprInit_962_; lean_object* v_exprResult_963_; lean_object* v_proof_964_; uint8_t v_modified_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_994_; 
v_expr_960_ = lean_ctor_get(v_rb_959_, 0);
v_exprType_961_ = lean_ctor_get(v_rb_959_, 1);
v_exprInit_962_ = lean_ctor_get(v_rb_959_, 2);
v_exprResult_963_ = lean_ctor_get(v_rb_959_, 3);
v_proof_964_ = lean_ctor_get(v_rb_959_, 4);
v_modified_965_ = lean_ctor_get_uint8(v_rb_959_, sizeof(void*)*5);
v_isSharedCheck_994_ = !lean_is_exclusive(v_rb_959_);
if (v_isSharedCheck_994_ == 0)
{
v___x_967_ = v_rb_959_;
v_isShared_968_ = v_isSharedCheck_994_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_proof_964_);
lean_inc(v_exprResult_963_);
lean_inc(v_exprInit_962_);
lean_inc(v_exprType_961_);
lean_inc(v_expr_960_);
lean_dec(v_rb_959_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_994_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v_expr_971_; lean_object* v___x_972_; lean_object* v_exprType_973_; lean_object* v___x_974_; lean_object* v_exprInit_975_; lean_object* v_exprResult_976_; 
v___x_969_ = 0;
lean_inc_ref_n(v_type_951_, 4);
lean_inc_n(v_declName_950_, 4);
v___x_970_ = l_Lean_mkLambda(v_declName_950_, v___x_969_, v_type_951_, v_expr_960_);
lean_inc_ref_n(v___y_952_, 3);
lean_inc_ref(v___x_970_);
v_expr_971_ = l_Lean_Expr_app___override(v___x_970_, v___y_952_);
v___x_972_ = l_Lean_mkLambda(v_declName_950_, v___x_969_, v_type_951_, v_exprType_961_);
lean_inc_ref(v___x_972_);
v_exprType_973_ = l_Lean_Expr_app___override(v___x_972_, v___y_952_);
v___x_974_ = l_Lean_mkLambda(v_declName_950_, v___x_969_, v_type_951_, v_exprInit_962_);
lean_inc_ref(v___x_974_);
v_exprInit_975_ = l_Lean_Expr_app___override(v___x_974_, v_value_953_);
v_exprResult_976_ = l_Lean_Expr_letE___override(v_declName_950_, v_type_951_, v___y_952_, v_exprResult_963_, v_nondep_954_);
if (v_modified_965_ == 0)
{
lean_object* v_toPure_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_proof_980_; lean_object* v___x_982_; 
lean_dec_ref(v___x_974_);
lean_dec_ref(v___x_972_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v_proof_964_);
lean_dec(v_us_958_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_type_951_);
lean_dec(v_declName_950_);
v_toPure_977_ = lean_ctor_get(v_toApplicative_955_, 1);
lean_inc(v_toPure_977_);
lean_dec_ref(v_toApplicative_955_);
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_979_ = l_Lean_mkConst(v___x_978_, v___x_956_);
lean_inc_ref(v_expr_971_);
lean_inc_ref(v_exprType_973_);
v_proof_980_ = l_Lean_mkAppB(v___x_979_, v_exprType_973_, v_expr_971_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v_proof_980_);
lean_ctor_set(v___x_967_, 3, v_exprResult_976_);
lean_ctor_set(v___x_967_, 2, v_exprInit_975_);
lean_ctor_set(v___x_967_, 1, v_exprType_973_);
lean_ctor_set(v___x_967_, 0, v_expr_971_);
v___x_982_ = v___x_967_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_expr_971_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_exprType_973_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_exprInit_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_exprResult_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_proof_980_);
v___x_982_ = v_reuseFailAlloc_984_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; 
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*5, v___y_957_);
v___x_983_ = lean_apply_2(v_toPure_977_, lean_box(0), v___x_982_);
return v___x_983_;
}
}
else
{
lean_object* v_toPure_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_proof_989_; lean_object* v___x_991_; 
lean_dec(v___x_956_);
v_toPure_985_ = lean_ctor_get(v_toApplicative_955_, 1);
lean_inc(v_toPure_985_);
lean_dec_ref(v_toApplicative_955_);
lean_inc_ref(v_type_951_);
v___x_986_ = l_Lean_mkLambda(v_declName_950_, v___x_969_, v_type_951_, v_proof_964_);
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___closed__0));
v___x_988_ = l_Lean_mkConst(v___x_987_, v_us_958_);
v_proof_989_ = l_Lean_mkApp6(v___x_988_, v_type_951_, v___x_972_, v___y_952_, v___x_974_, v___x_970_, v___x_986_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v_proof_989_);
lean_ctor_set(v___x_967_, 3, v_exprResult_976_);
lean_ctor_set(v___x_967_, 2, v_exprInit_975_);
lean_ctor_set(v___x_967_, 1, v_exprType_973_);
lean_ctor_set(v___x_967_, 0, v_expr_971_);
v___x_991_ = v___x_967_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_expr_971_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_exprType_973_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_exprInit_975_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_exprResult_976_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_proof_989_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*5, v_nondep_954_);
v___x_992_ = lean_apply_2(v_toPure_985_, lean_box(0), v___x_991_);
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed(lean_object* v_declName_995_, lean_object* v_type_996_, lean_object* v___y_997_, lean_object* v_value_998_, lean_object* v_nondep_999_, lean_object* v_toApplicative_1000_, lean_object* v___x_1001_, lean_object* v___y_1002_, lean_object* v_us_1003_, lean_object* v_rb_1004_){
_start:
{
uint8_t v_nondep_12569__boxed_1005_; uint8_t v___y_12571__boxed_1006_; lean_object* v_res_1007_; 
v_nondep_12569__boxed_1005_ = lean_unbox(v_nondep_999_);
v___y_12571__boxed_1006_ = lean_unbox(v___y_1002_);
v_res_1007_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3(v_declName_995_, v_type_996_, v___y_997_, v_value_998_, v_nondep_12569__boxed_1005_, v_toApplicative_1000_, v___x_1001_, v___y_12571__boxed_1006_, v_us_1003_, v_rb_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9(lean_object* v___f_1008_, lean_object* v_____x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_apply_1(v___f_1008_, v_____x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(lean_object* v___x_1015_, lean_object* v_declName_1016_, lean_object* v_type_1017_, lean_object* v_value_1018_, lean_object* v_us_1019_, lean_object* v___x_1020_, lean_object* v_toApplicative_1021_, uint8_t v_nondep_1022_, lean_object* v_rb_1023_){
_start:
{
lean_object* v_expr_1024_; lean_object* v_exprType_1025_; lean_object* v_exprInit_1026_; lean_object* v_exprResult_1027_; lean_object* v_proof_1028_; uint8_t v_modified_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1059_; 
v_expr_1024_ = lean_ctor_get(v_rb_1023_, 0);
v_exprType_1025_ = lean_ctor_get(v_rb_1023_, 1);
v_exprInit_1026_ = lean_ctor_get(v_rb_1023_, 2);
v_exprResult_1027_ = lean_ctor_get(v_rb_1023_, 3);
v_proof_1028_ = lean_ctor_get(v_rb_1023_, 4);
v_modified_1029_ = lean_ctor_get_uint8(v_rb_1023_, sizeof(void*)*5);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_rb_1023_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1031_ = v_rb_1023_;
v_isShared_1032_ = v_isSharedCheck_1059_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_proof_1028_);
lean_inc(v_exprResult_1027_);
lean_inc(v_exprInit_1026_);
lean_inc(v_exprType_1025_);
lean_inc(v_expr_1024_);
lean_dec(v_rb_1023_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1059_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_expr_1033_; lean_object* v_exprType_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v_exprInit_1037_; lean_object* v_exprResult_1038_; 
v_expr_1033_ = lean_expr_lower_loose_bvars(v_expr_1024_, v___x_1015_, v___x_1015_);
lean_dec_ref(v_expr_1024_);
v_exprType_1034_ = lean_expr_lower_loose_bvars(v_exprType_1025_, v___x_1015_, v___x_1015_);
lean_dec_ref(v_exprType_1025_);
v___x_1035_ = 0;
lean_inc_ref(v_type_1017_);
lean_inc(v_declName_1016_);
v___x_1036_ = l_Lean_mkLambda(v_declName_1016_, v___x_1035_, v_type_1017_, v_exprInit_1026_);
lean_inc_ref(v_value_1018_);
lean_inc_ref(v___x_1036_);
v_exprInit_1037_ = l_Lean_Expr_app___override(v___x_1036_, v_value_1018_);
v_exprResult_1038_ = lean_expr_lower_loose_bvars(v_exprResult_1027_, v___x_1015_, v___x_1015_);
lean_dec_ref(v_exprResult_1027_);
if (v_modified_1029_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_proof_1044_; lean_object* v_toPure_1045_; lean_object* v___x_1047_; 
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_proof_1028_);
lean_dec(v_declName_1016_);
v___x_1039_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__0));
v___x_1040_ = l_Lean_mkConst(v___x_1039_, v_us_1019_);
v___x_1041_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1042_ = l_Lean_mkConst(v___x_1041_, v___x_1020_);
lean_inc_ref_n(v_expr_1033_, 3);
lean_inc_ref_n(v_exprType_1034_, 2);
v___x_1043_ = l_Lean_mkAppB(v___x_1042_, v_exprType_1034_, v_expr_1033_);
v_proof_1044_ = l_Lean_mkApp6(v___x_1040_, v_type_1017_, v_exprType_1034_, v_value_1018_, v_expr_1033_, v_expr_1033_, v___x_1043_);
v_toPure_1045_ = lean_ctor_get(v_toApplicative_1021_, 1);
lean_inc(v_toPure_1045_);
lean_dec_ref(v_toApplicative_1021_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 4, v_proof_1044_);
lean_ctor_set(v___x_1031_, 3, v_exprResult_1038_);
lean_ctor_set(v___x_1031_, 2, v_exprInit_1037_);
lean_ctor_set(v___x_1031_, 1, v_exprType_1034_);
lean_ctor_set(v___x_1031_, 0, v_expr_1033_);
v___x_1047_ = v___x_1031_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_expr_1033_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_exprType_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_exprInit_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_exprResult_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_proof_1044_);
v___x_1047_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; 
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5, v_nondep_1022_);
v___x_1048_ = lean_apply_2(v_toPure_1045_, lean_box(0), v___x_1047_);
return v___x_1048_;
}
}
else
{
lean_object* v_toPure_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_proof_1054_; lean_object* v___x_1056_; 
lean_dec(v___x_1020_);
v_toPure_1050_ = lean_ctor_get(v_toApplicative_1021_, 1);
lean_inc(v_toPure_1050_);
lean_dec_ref(v_toApplicative_1021_);
lean_inc_ref(v_type_1017_);
v___x_1051_ = l_Lean_mkLambda(v_declName_1016_, v___x_1035_, v_type_1017_, v_proof_1028_);
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___closed__1));
v___x_1053_ = l_Lean_mkConst(v___x_1052_, v_us_1019_);
lean_inc_ref(v_expr_1033_);
lean_inc_ref(v_exprType_1034_);
v_proof_1054_ = l_Lean_mkApp6(v___x_1053_, v_type_1017_, v_exprType_1034_, v_value_1018_, v___x_1036_, v_expr_1033_, v___x_1051_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 4, v_proof_1054_);
lean_ctor_set(v___x_1031_, 3, v_exprResult_1038_);
lean_ctor_set(v___x_1031_, 2, v_exprInit_1037_);
lean_ctor_set(v___x_1031_, 1, v_exprType_1034_);
lean_ctor_set(v___x_1031_, 0, v_expr_1033_);
v___x_1056_ = v___x_1031_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_expr_1033_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_exprType_1034_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_exprInit_1037_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_exprResult_1038_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_proof_1054_);
v___x_1056_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; 
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*5, v_nondep_1022_);
v___x_1057_ = lean_apply_2(v_toPure_1050_, lean_box(0), v___x_1056_);
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed(lean_object* v___x_1060_, lean_object* v_declName_1061_, lean_object* v_type_1062_, lean_object* v_value_1063_, lean_object* v_us_1064_, lean_object* v___x_1065_, lean_object* v_toApplicative_1066_, lean_object* v_nondep_1067_, lean_object* v_rb_1068_){
_start:
{
uint8_t v_nondep_12656__boxed_1069_; lean_object* v_res_1070_; 
v_nondep_12656__boxed_1069_ = lean_unbox(v_nondep_1067_);
v_res_1070_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13(v___x_1060_, v_declName_1061_, v_type_1062_, v_value_1063_, v_us_1064_, v___x_1065_, v_toApplicative_1066_, v_nondep_12656__boxed_1069_, v_rb_1068_);
lean_dec(v___x_1060_);
return v_res_1070_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__0));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__2));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(lean_object* v_cls_1077_, lean_object* v___x_1078_, lean_object* v___f_1079_, lean_object* v_declName_1080_, lean_object* v_val_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_options_1092_; uint8_t v_hasTrace_1093_; 
v_options_1092_ = lean_ctor_get(v___y_1086_, 2);
v_hasTrace_1093_ = lean_ctor_get_uint8(v_options_1092_, sizeof(void*)*1);
if (v_hasTrace_1093_ == 0)
{
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v___x_1083_);
lean_dec_ref(v___x_1082_);
lean_dec_ref(v_val_1081_);
lean_dec(v_declName_1080_);
lean_dec(v___f_1079_);
lean_dec(v___x_1078_);
lean_dec(v_cls_1077_);
goto v___jp_1089_;
}
else
{
lean_object* v_inheritedTraceOptions_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_inheritedTraceOptions_1094_ = lean_ctor_get(v___y_1086_, 13);
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1077_);
v___x_1096_ = l_Lean_Name_append(v___x_1095_, v_cls_1077_);
v___x_1097_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1094_, v_options_1092_, v___x_1096_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v___x_1083_);
lean_dec_ref(v___x_1082_);
lean_dec_ref(v_val_1081_);
lean_dec(v_declName_1080_);
lean_dec(v___f_1079_);
lean_dec(v___x_1078_);
lean_dec(v_cls_1077_);
goto v___jp_1089_;
}
else
{
lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_toMonadRef_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_12266__overap_1112_; lean_object* v___x_1113_; 
v___f_1098_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1100_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1101_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1099_, v___x_1078_, v___x_1100_);
v___x_1102_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1098_, v___f_1079_, v___x_1101_);
v_toMonadRef_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_toMonadRef_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1105_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__1);
v___x_1106_ = l_Lean_MessageData_ofName(v_declName_1080_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_ofExpr(v_val_1081_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_12266__overap_1112_ = l_Lean_addTrace___redArg(v___x_1082_, v___x_1083_, v_toMonadRef_1103_, v___x_1104_, v_cls_1077_, v___x_1111_);
v___x_1113_ = lean_apply_5(v___x_12266__overap_1112_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, lean_box(0));
return v___x_1113_;
}
}
v___jp_1089_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed(lean_object* v_cls_1114_, lean_object* v___x_1115_, lean_object* v___f_1116_, lean_object* v_declName_1117_, lean_object* v_val_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15(v_cls_1114_, v___x_1115_, v___f_1116_, v_declName_1117_, v_val_1118_, v___x_1119_, v___x_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v_res_1126_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__0));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__2));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(lean_object* v_cls_1133_, lean_object* v___x_1134_, lean_object* v___f_1135_, lean_object* v_declName_1136_, lean_object* v_val_1137_, lean_object* v_val_x27_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_options_1149_; uint8_t v_hasTrace_1150_; 
v_options_1149_ = lean_ctor_get(v___y_1143_, 2);
v_hasTrace_1150_ = lean_ctor_get_uint8(v_options_1149_, sizeof(void*)*1);
if (v_hasTrace_1150_ == 0)
{
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v_val_x27_1138_);
lean_dec_ref(v_val_1137_);
lean_dec(v_declName_1136_);
lean_dec(v___f_1135_);
lean_dec(v___x_1134_);
lean_dec(v_cls_1133_);
goto v___jp_1146_;
}
else
{
lean_object* v_inheritedTraceOptions_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_inheritedTraceOptions_1151_ = lean_ctor_get(v___y_1143_, 13);
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1133_);
v___x_1153_ = l_Lean_Name_append(v___x_1152_, v_cls_1133_);
v___x_1154_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1151_, v_options_1149_, v___x_1153_);
lean_dec(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v_val_x27_1138_);
lean_dec_ref(v_val_1137_);
lean_dec(v_declName_1136_);
lean_dec(v___f_1135_);
lean_dec(v___x_1134_);
lean_dec(v_cls_1133_);
goto v___jp_1146_;
}
else
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_toMonadRef_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_11948__overap_1173_; lean_object* v___x_1174_; 
v___f_1155_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1156_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1157_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1158_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1156_, v___x_1134_, v___x_1157_);
v___x_1159_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1155_, v___f_1135_, v___x_1158_);
v_toMonadRef_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_toMonadRef_1160_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__1);
v___x_1163_ = l_Lean_MessageData_ofName(v_declName_1136_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_MessageData_ofExpr(v_val_1137_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_MessageData_ofExpr(v_val_x27_1138_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_11948__overap_1173_ = l_Lean_addTrace___redArg(v___x_1139_, v___x_1140_, v_toMonadRef_1160_, v___x_1161_, v_cls_1133_, v___x_1172_);
v___x_1174_ = lean_apply_5(v___x_11948__overap_1173_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
return v___x_1174_;
}
}
v___jp_1146_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed(lean_object* v_cls_1175_, lean_object* v___x_1176_, lean_object* v___f_1177_, lean_object* v_declName_1178_, lean_object* v_val_1179_, lean_object* v_val_x27_1180_, lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5(v_cls_1175_, v___x_1176_, v___f_1177_, v_declName_1178_, v_val_1179_, v_val_x27_1180_, v___x_1181_, v___x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(lean_object* v_toApplicative_1189_, lean_object* v_e_1190_, lean_object* v_xs_1191_, lean_object* v_h_1192_, uint8_t v_nondep_1193_, lean_object* v_toBind_1194_, lean_object* v___f_1195_, lean_object* v_____r_1196_){
_start:
{
lean_object* v_toPure_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_toPure_1197_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_inc(v_toPure_1197_);
lean_dec_ref(v_toApplicative_1189_);
v___x_1198_ = lean_expr_abstract(v_e_1190_, v_xs_1191_);
v___x_1199_ = lean_expr_abstract(v_h_1192_, v_xs_1191_);
v___x_1200_ = lean_box(v_nondep_1193_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___x_1199_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1198_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_apply_2(v_toPure_1197_, lean_box(0), v___x_1202_);
v___x_1204_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v___x_1203_, v___f_1195_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed(lean_object* v_toApplicative_1205_, lean_object* v_e_1206_, lean_object* v_xs_1207_, lean_object* v_h_1208_, lean_object* v_nondep_1209_, lean_object* v_toBind_1210_, lean_object* v___f_1211_, lean_object* v_____r_1212_){
_start:
{
uint8_t v_nondep_12922__boxed_1213_; lean_object* v_res_1214_; 
v_nondep_12922__boxed_1213_ = lean_unbox(v_nondep_1209_);
v_res_1214_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11(v_toApplicative_1205_, v_e_1206_, v_xs_1207_, v_h_1208_, v_nondep_12922__boxed_1213_, v_toBind_1210_, v___f_1211_, v_____r_1212_);
lean_dec_ref(v_h_1208_);
lean_dec_ref(v_xs_1207_);
lean_dec_ref(v_e_1206_);
return v_res_1214_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__0));
v___x_1217_ = l_Lean_stringToMessageData(v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(lean_object* v_cls_1218_, lean_object* v___x_1219_, lean_object* v___f_1220_, lean_object* v_declName_1221_, lean_object* v_val_1222_, lean_object* v_e_1223_, lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_options_1234_; uint8_t v_hasTrace_1235_; 
v_options_1234_ = lean_ctor_get(v___y_1228_, 2);
v_hasTrace_1235_ = lean_ctor_get_uint8(v_options_1234_, sizeof(void*)*1);
if (v_hasTrace_1235_ == 0)
{
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_val_1222_);
lean_dec(v_declName_1221_);
lean_dec(v___f_1220_);
lean_dec(v___x_1219_);
lean_dec(v_cls_1218_);
goto v___jp_1231_;
}
else
{
lean_object* v_inheritedTraceOptions_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_inheritedTraceOptions_1236_ = lean_ctor_get(v___y_1228_, 13);
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__1));
lean_inc(v_cls_1218_);
v___x_1238_ = l_Lean_Name_append(v___x_1237_, v_cls_1218_);
v___x_1239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1236_, v_options_1234_, v___x_1238_);
lean_dec(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___x_1225_);
lean_dec_ref(v___x_1224_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_val_1222_);
lean_dec(v_declName_1221_);
lean_dec(v___f_1220_);
lean_dec(v___x_1219_);
lean_dec(v_cls_1218_);
goto v___jp_1231_;
}
else
{
lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_toMonadRef_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_12128__overap_1258_; lean_object* v___x_1259_; 
v___f_1240_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__2));
v___x_1241_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___closed__3));
v___x_1242_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1243_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1241_, v___x_1219_, v___x_1242_);
v___x_1244_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1240_, v___f_1220_, v___x_1243_);
v_toMonadRef_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_toMonadRef_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___closed__1);
v___x_1248_ = l_Lean_MessageData_ofName(v_declName_1221_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___closed__3);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_MessageData_ofExpr(v_val_1222_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___closed__3);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = l_Lean_MessageData_ofExpr(v_e_1223_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_12128__overap_1258_ = l_Lean_addTrace___redArg(v___x_1224_, v___x_1225_, v_toMonadRef_1245_, v___x_1246_, v_cls_1218_, v___x_1257_);
v___x_1259_ = lean_apply_5(v___x_12128__overap_1258_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, lean_box(0));
return v___x_1259_;
}
}
v___jp_1231_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed(lean_object* v_cls_1260_, lean_object* v___x_1261_, lean_object* v___f_1262_, lean_object* v_declName_1263_, lean_object* v_val_1264_, lean_object* v_e_1265_, lean_object* v___x_1266_, lean_object* v___x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10(v_cls_1260_, v___x_1261_, v___f_1262_, v_declName_1263_, v_val_1264_, v_e_1265_, v___x_1266_, v___x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v_res_1273_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_instMonadEIO(lean_box(0));
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__0);
v___x_1276_ = l_StateRefT_x27_instMonad___redArg(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1294_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1293_, v___x_1292_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; 
v___x_1295_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__13);
v___f_1296_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1297_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1296_, v___x_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(lean_object* v_toApplicative_1298_, lean_object* v_level_1299_, lean_object* v___x_1300_, lean_object* v_type_1301_, lean_object* v_value_1302_, uint8_t v___x_1303_, lean_object* v_toBind_1304_, lean_object* v___f_1305_, lean_object* v_xs_1306_, uint8_t v_nondep_1307_, lean_object* v___f_1308_, lean_object* v_declName_1309_, lean_object* v_val_1310_, lean_object* v_inst_1311_, lean_object* v_____do__lift_1312_){
_start:
{
if (lean_obj_tag(v_____do__lift_1312_) == 0)
{
lean_object* v_toPure_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_inst_1311_);
lean_dec_ref(v_val_1310_);
lean_dec(v_declName_1309_);
lean_dec(v___f_1308_);
lean_dec_ref(v_xs_1306_);
v_toPure_1313_ = lean_ctor_get(v_toApplicative_1298_, 1);
lean_inc(v_toPure_1313_);
lean_dec_ref(v_toApplicative_1298_);
v___x_1314_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_level_1299_);
lean_ctor_set(v___x_1315_, 1, v___x_1300_);
v___x_1316_ = l_Lean_mkConst(v___x_1314_, v___x_1315_);
lean_inc_ref(v_value_1302_);
v___x_1317_ = l_Lean_mkAppB(v___x_1316_, v_type_1301_, v_value_1302_);
v___x_1318_ = lean_box(v___x_1303_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_value_1302_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1320_);
v___x_1322_ = lean_apply_4(v_toBind_1304_, lean_box(0), lean_box(0), v___x_1321_, v___f_1305_);
return v___x_1322_;
}
else
{
lean_object* v_e_1323_; lean_object* v_h_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v___f_1305_);
lean_dec_ref(v_value_1302_);
lean_dec_ref(v_type_1301_);
lean_dec(v___x_1300_);
lean_dec(v_level_1299_);
v_e_1323_ = lean_ctor_get(v_____do__lift_1312_, 0);
v_h_1324_ = lean_ctor_get(v_____do__lift_1312_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_____do__lift_1312_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1326_ = v_____do__lift_1312_;
v_isShared_1327_ = v_isSharedCheck_1385_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_h_1324_);
lean_inc(v_e_1323_);
lean_dec(v_____do__lift_1312_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1385_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v_toApplicative_1329_; lean_object* v_toFunctor_1330_; lean_object* v_toSeq_1331_; lean_object* v_toSeqLeft_1332_; lean_object* v_toSeqRight_1333_; lean_object* v___f_1334_; lean_object* v___f_1335_; lean_object* v___f_1336_; lean_object* v___f_1337_; lean_object* v___x_1339_; 
v___x_1328_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1329_ = lean_ctor_get(v___x_1328_, 0);
v_toFunctor_1330_ = lean_ctor_get(v_toApplicative_1329_, 0);
v_toSeq_1331_ = lean_ctor_get(v_toApplicative_1329_, 2);
v_toSeqLeft_1332_ = lean_ctor_get(v_toApplicative_1329_, 3);
v_toSeqRight_1333_ = lean_ctor_get(v_toApplicative_1329_, 4);
v___f_1334_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1335_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1330_, 2);
v___f_1336_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1336_, 0, v_toFunctor_1330_);
v___f_1337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1337_, 0, v_toFunctor_1330_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
lean_ctor_set(v___x_1326_, 1, v___f_1337_);
lean_ctor_set(v___x_1326_, 0, v___f_1336_);
v___x_1339_ = v___x_1326_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___f_1336_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___f_1337_);
v___x_1339_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___f_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_toApplicative_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1382_; 
lean_inc(v_toSeqRight_1333_);
v___f_1340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1340_, 0, v_toSeqRight_1333_);
lean_inc(v_toSeqLeft_1332_);
v___f_1341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1341_, 0, v_toSeqLeft_1332_);
lean_inc(v_toSeq_1331_);
v___f_1342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1342_, 0, v_toSeq_1331_);
v___x_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1339_);
lean_ctor_set(v___x_1343_, 1, v___f_1334_);
lean_ctor_set(v___x_1343_, 2, v___f_1342_);
lean_ctor_set(v___x_1343_, 3, v___f_1341_);
lean_ctor_set(v___x_1343_, 4, v___f_1340_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v___f_1335_);
v___x_1345_ = l_StateRefT_x27_instMonad___redArg(v___x_1344_);
v_toApplicative_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1345_, 1);
lean_dec(v_unused_1383_);
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1382_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_toApplicative_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1382_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_toFunctor_1350_; lean_object* v_toSeq_1351_; lean_object* v_toSeqLeft_1352_; lean_object* v_toSeqRight_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1380_; 
v_toFunctor_1350_ = lean_ctor_get(v_toApplicative_1346_, 0);
v_toSeq_1351_ = lean_ctor_get(v_toApplicative_1346_, 2);
v_toSeqLeft_1352_ = lean_ctor_get(v_toApplicative_1346_, 3);
v_toSeqRight_1353_ = lean_ctor_get(v_toApplicative_1346_, 4);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_toApplicative_1346_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v_toApplicative_1346_, 1);
lean_dec(v_unused_1381_);
v___x_1355_ = v_toApplicative_1346_;
v_isShared_1356_ = v_isSharedCheck_1380_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_toSeqRight_1353_);
lean_inc(v_toSeqLeft_1352_);
lean_inc(v_toSeq_1351_);
lean_inc(v_toFunctor_1350_);
lean_dec(v_toApplicative_1346_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1380_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___f_1358_; lean_object* v_cls_1359_; lean_object* v___f_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___x_1369_; 
v___x_1357_ = lean_box(v_nondep_1307_);
lean_inc(v_toBind_1304_);
lean_inc_ref(v_e_1323_);
v___f_1358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_1358_, 0, v_toApplicative_1298_);
lean_closure_set(v___f_1358_, 1, v_e_1323_);
lean_closure_set(v___f_1358_, 2, v_xs_1306_);
lean_closure_set(v___f_1358_, 3, v_h_1324_);
lean_closure_set(v___f_1358_, 4, v___x_1357_);
lean_closure_set(v___f_1358_, 5, v_toBind_1304_);
lean_closure_set(v___f_1358_, 6, v___f_1308_);
v_cls_1359_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1360_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1361_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1350_);
v___f_1362_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1362_, 0, v_toFunctor_1350_);
v___f_1363_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1363_, 0, v_toFunctor_1350_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___f_1362_);
lean_ctor_set(v___x_1364_, 1, v___f_1363_);
v___f_1365_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1365_, 0, v_toSeqRight_1353_);
v___f_1366_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1366_, 0, v_toSeqLeft_1352_);
v___f_1367_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1367_, 0, v_toSeq_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v___f_1365_);
lean_ctor_set(v___x_1355_, 3, v___f_1366_);
lean_ctor_set(v___x_1355_, 2, v___f_1367_);
lean_ctor_set(v___x_1355_, 1, v___f_1360_);
lean_ctor_set(v___x_1355_, 0, v___x_1364_);
v___x_1369_ = v___x_1355_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___f_1360_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v___f_1367_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v___f_1366_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v___f_1365_);
v___x_1369_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___f_1361_);
lean_ctor_set(v___x_1348_, 0, v___x_1369_);
v___x_1371_ = v___x_1348_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___f_1361_);
v___x_1371_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___f_1372_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1374_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__10___boxed), 13, 8);
lean_closure_set(v___f_1375_, 0, v_cls_1359_);
lean_closure_set(v___f_1375_, 1, v___x_1373_);
lean_closure_set(v___f_1375_, 2, v___f_1372_);
lean_closure_set(v___f_1375_, 3, v_declName_1309_);
lean_closure_set(v___f_1375_, 4, v_val_1310_);
lean_closure_set(v___f_1375_, 5, v_e_1323_);
lean_closure_set(v___f_1375_, 6, v___x_1371_);
lean_closure_set(v___f_1375_, 7, v___x_1374_);
v___x_1376_ = lean_apply_2(v_inst_1311_, lean_box(0), v___f_1375_);
v___x_1377_ = lean_apply_4(v_toBind_1304_, lean_box(0), lean_box(0), v___x_1376_, v___f_1358_);
return v___x_1377_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed(lean_object* v_toApplicative_1386_, lean_object* v_level_1387_, lean_object* v___x_1388_, lean_object* v_type_1389_, lean_object* v_value_1390_, lean_object* v___x_1391_, lean_object* v_toBind_1392_, lean_object* v___f_1393_, lean_object* v_xs_1394_, lean_object* v_nondep_1395_, lean_object* v___f_1396_, lean_object* v_declName_1397_, lean_object* v_val_1398_, lean_object* v_inst_1399_, lean_object* v_____do__lift_1400_){
_start:
{
uint8_t v___x_13109__boxed_1401_; uint8_t v_nondep_13111__boxed_1402_; lean_object* v_res_1403_; 
v___x_13109__boxed_1401_ = lean_unbox(v___x_1391_);
v_nondep_13111__boxed_1402_ = lean_unbox(v_nondep_1395_);
v_res_1403_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12(v_toApplicative_1386_, v_level_1387_, v___x_1388_, v_type_1389_, v_value_1390_, v___x_13109__boxed_1401_, v_toBind_1392_, v___f_1393_, v_xs_1394_, v_nondep_13111__boxed_1402_, v___f_1396_, v_declName_1397_, v_val_1398_, v_inst_1399_, v_____do__lift_1400_);
return v_res_1403_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__5));
v___x_1414_ = lean_unsigned_to_nat(8u);
v___x_1415_ = lean_unsigned_to_nat(287u);
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1418_ = l_mkPanicMessageWithDecl(v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_, v___x_1413_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(lean_object* v_declName_1419_, lean_object* v_type_1420_, lean_object* v_fst_1421_, lean_object* v___x_1422_, lean_object* v_value_1423_, uint8_t v_nondep_1424_, uint8_t v_fst_1425_, lean_object* v_toApplicative_1426_, lean_object* v___x_1427_, lean_object* v_us_1428_, lean_object* v_snd_1429_, lean_object* v_inst_1430_, lean_object* v_rb_1431_){
_start:
{
lean_object* v_expr_1432_; lean_object* v_exprType_1433_; lean_object* v_exprInit_1434_; lean_object* v_exprResult_1435_; lean_object* v_proof_1436_; uint8_t v_modified_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1488_; 
v_expr_1432_ = lean_ctor_get(v_rb_1431_, 0);
v_exprType_1433_ = lean_ctor_get(v_rb_1431_, 1);
v_exprInit_1434_ = lean_ctor_get(v_rb_1431_, 2);
v_exprResult_1435_ = lean_ctor_get(v_rb_1431_, 3);
v_proof_1436_ = lean_ctor_get(v_rb_1431_, 4);
v_modified_1437_ = lean_ctor_get_uint8(v_rb_1431_, sizeof(void*)*5);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_rb_1431_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1439_ = v_rb_1431_;
v_isShared_1440_ = v_isSharedCheck_1488_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_proof_1436_);
lean_inc(v_exprResult_1435_);
lean_inc(v_exprInit_1434_);
lean_inc(v_exprType_1433_);
lean_inc(v_expr_1432_);
lean_dec(v_rb_1431_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1488_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_expr_has_loose_bvar(v_exprType_1433_, v___x_1441_);
if (v___x_1442_ == 0)
{
uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v_expr_1445_; lean_object* v_exprType_1446_; lean_object* v___x_1447_; lean_object* v_exprInit_1448_; lean_object* v_exprResult_1449_; 
lean_dec_ref(v_inst_1430_);
v___x_1443_ = 0;
lean_inc_ref_n(v_type_1420_, 3);
lean_inc_n(v_declName_1419_, 3);
v___x_1444_ = l_Lean_mkLambda(v_declName_1419_, v___x_1443_, v_type_1420_, v_expr_1432_);
lean_inc_ref_n(v_fst_1421_, 2);
lean_inc_ref(v___x_1444_);
v_expr_1445_ = l_Lean_Expr_app___override(v___x_1444_, v_fst_1421_);
v_exprType_1446_ = lean_expr_lower_loose_bvars(v_exprType_1433_, v___x_1422_, v___x_1422_);
lean_dec_ref(v_exprType_1433_);
v___x_1447_ = l_Lean_mkLambda(v_declName_1419_, v___x_1443_, v_type_1420_, v_exprInit_1434_);
lean_inc_ref(v_value_1423_);
lean_inc_ref(v___x_1447_);
v_exprInit_1448_ = l_Lean_Expr_app___override(v___x_1447_, v_value_1423_);
v_exprResult_1449_ = l_Lean_Expr_letE___override(v_declName_1419_, v_type_1420_, v_fst_1421_, v_exprResult_1435_, v_nondep_1424_);
if (v_fst_1425_ == 0)
{
lean_dec_ref(v_snd_1429_);
lean_dec_ref(v_fst_1421_);
if (v_modified_1437_ == 0)
{
lean_object* v_toPure_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_proof_1453_; lean_object* v___x_1455_; 
lean_dec_ref(v___x_1447_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v_proof_1436_);
lean_dec(v_us_1428_);
lean_dec_ref(v_value_1423_);
lean_dec_ref(v_type_1420_);
lean_dec(v_declName_1419_);
v_toPure_1450_ = lean_ctor_get(v_toApplicative_1426_, 1);
lean_inc(v_toPure_1450_);
lean_dec_ref(v_toApplicative_1426_);
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_1452_ = l_Lean_mkConst(v___x_1451_, v___x_1427_);
lean_inc_ref(v_expr_1445_);
lean_inc_ref(v_exprType_1446_);
v_proof_1453_ = l_Lean_mkAppB(v___x_1452_, v_exprType_1446_, v_expr_1445_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_proof_1453_);
lean_ctor_set(v___x_1439_, 3, v_exprResult_1449_);
lean_ctor_set(v___x_1439_, 2, v_exprInit_1448_);
lean_ctor_set(v___x_1439_, 1, v_exprType_1446_);
lean_ctor_set(v___x_1439_, 0, v_expr_1445_);
v___x_1455_ = v___x_1439_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_expr_1445_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_exprType_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_exprInit_1448_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_exprResult_1449_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_proof_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*5, v_modified_1437_);
v___x_1455_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1455_);
return v___x_1456_;
}
}
else
{
lean_object* v_toPure_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_proof_1462_; lean_object* v___x_1464_; 
lean_dec(v___x_1427_);
v_toPure_1458_ = lean_ctor_get(v_toApplicative_1426_, 1);
lean_inc(v_toPure_1458_);
lean_dec_ref(v_toApplicative_1426_);
lean_inc_ref(v_type_1420_);
v___x_1459_ = l_Lean_mkLambda(v_declName_1419_, v___x_1443_, v_type_1420_, v_proof_1436_);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__0));
v___x_1461_ = l_Lean_mkConst(v___x_1460_, v_us_1428_);
lean_inc_ref(v_exprType_1446_);
v_proof_1462_ = l_Lean_mkApp6(v___x_1461_, v_type_1420_, v_exprType_1446_, v_value_1423_, v___x_1447_, v___x_1444_, v___x_1459_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_proof_1462_);
lean_ctor_set(v___x_1439_, 3, v_exprResult_1449_);
lean_ctor_set(v___x_1439_, 2, v_exprInit_1448_);
lean_ctor_set(v___x_1439_, 1, v_exprType_1446_);
lean_ctor_set(v___x_1439_, 0, v_expr_1445_);
v___x_1464_ = v___x_1439_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_expr_1445_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_exprType_1446_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_exprInit_1448_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_exprResult_1449_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v_proof_1462_);
v___x_1464_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; 
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*5, v_nondep_1424_);
v___x_1465_ = lean_apply_2(v_toPure_1458_, lean_box(0), v___x_1464_);
return v___x_1465_;
}
}
}
else
{
lean_dec(v___x_1427_);
if (v_modified_1437_ == 0)
{
lean_object* v_toPure_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_proof_1470_; lean_object* v___x_1472_; 
lean_dec_ref(v___x_1444_);
lean_dec_ref(v_proof_1436_);
lean_dec(v_declName_1419_);
v_toPure_1467_ = lean_ctor_get(v_toApplicative_1426_, 1);
lean_inc(v_toPure_1467_);
lean_dec_ref(v_toApplicative_1426_);
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__1));
v___x_1469_ = l_Lean_mkConst(v___x_1468_, v_us_1428_);
lean_inc_ref(v_exprType_1446_);
v_proof_1470_ = l_Lean_mkApp6(v___x_1469_, v_type_1420_, v_exprType_1446_, v_value_1423_, v_fst_1421_, v___x_1447_, v_snd_1429_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_proof_1470_);
lean_ctor_set(v___x_1439_, 3, v_exprResult_1449_);
lean_ctor_set(v___x_1439_, 2, v_exprInit_1448_);
lean_ctor_set(v___x_1439_, 1, v_exprType_1446_);
lean_ctor_set(v___x_1439_, 0, v_expr_1445_);
v___x_1472_ = v___x_1439_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_expr_1445_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_exprType_1446_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_exprInit_1448_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_exprResult_1449_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_proof_1470_);
v___x_1472_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; 
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*5, v_nondep_1424_);
v___x_1473_ = lean_apply_2(v_toPure_1467_, lean_box(0), v___x_1472_);
return v___x_1473_;
}
}
else
{
lean_object* v_toPure_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_proof_1479_; lean_object* v___x_1481_; 
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1426_, 1);
lean_inc(v_toPure_1475_);
lean_dec_ref(v_toApplicative_1426_);
lean_inc_ref(v_type_1420_);
v___x_1476_ = l_Lean_mkLambda(v_declName_1419_, v___x_1443_, v_type_1420_, v_proof_1436_);
v___x_1477_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__2));
v___x_1478_ = l_Lean_mkConst(v___x_1477_, v_us_1428_);
lean_inc_ref(v_exprType_1446_);
v_proof_1479_ = l_Lean_mkApp8(v___x_1478_, v_type_1420_, v_exprType_1446_, v_value_1423_, v_fst_1421_, v___x_1447_, v___x_1444_, v_snd_1429_, v___x_1476_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_proof_1479_);
lean_ctor_set(v___x_1439_, 3, v_exprResult_1449_);
lean_ctor_set(v___x_1439_, 2, v_exprInit_1448_);
lean_ctor_set(v___x_1439_, 1, v_exprType_1446_);
lean_ctor_set(v___x_1439_, 0, v_expr_1445_);
v___x_1481_ = v___x_1439_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_expr_1445_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_exprType_1446_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_exprInit_1448_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_exprResult_1449_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_proof_1479_);
v___x_1481_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; 
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*5, v_nondep_1424_);
v___x_1482_ = lean_apply_2(v_toPure_1475_, lean_box(0), v___x_1481_);
return v___x_1482_;
}
}
}
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_del_object(v___x_1439_);
lean_dec_ref(v_proof_1436_);
lean_dec_ref(v_exprResult_1435_);
lean_dec_ref(v_exprInit_1434_);
lean_dec_ref(v_exprType_1433_);
lean_dec_ref(v_expr_1432_);
lean_dec_ref(v_snd_1429_);
lean_dec(v_us_1428_);
lean_dec(v___x_1427_);
lean_dec_ref(v_toApplicative_1426_);
lean_dec_ref(v_value_1423_);
lean_dec_ref(v_fst_1421_);
lean_dec_ref(v_type_1420_);
lean_dec(v_declName_1419_);
v___x_1484_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1485_ = l_instInhabitedOfMonad___redArg(v_inst_1430_, v___x_1484_);
v___x_1486_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__6);
v___x_1487_ = l_panic___redArg(v___x_1485_, v___x_1486_);
lean_dec(v___x_1485_);
return v___x_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed(lean_object* v_declName_1489_, lean_object* v_type_1490_, lean_object* v_fst_1491_, lean_object* v___x_1492_, lean_object* v_value_1493_, lean_object* v_nondep_1494_, lean_object* v_fst_1495_, lean_object* v_toApplicative_1496_, lean_object* v___x_1497_, lean_object* v_us_1498_, lean_object* v_snd_1499_, lean_object* v_inst_1500_, lean_object* v_rb_1501_){
_start:
{
uint8_t v_nondep_13327__boxed_1502_; uint8_t v_fst_13328__boxed_1503_; lean_object* v_res_1504_; 
v_nondep_13327__boxed_1502_ = lean_unbox(v_nondep_1494_);
v_fst_13328__boxed_1503_ = lean_unbox(v_fst_1495_);
v_res_1504_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7(v_declName_1489_, v_type_1490_, v_fst_1491_, v___x_1492_, v_value_1493_, v_nondep_13327__boxed_1502_, v_fst_13328__boxed_1503_, v_toApplicative_1496_, v___x_1497_, v_us_1498_, v_snd_1499_, v_inst_1500_, v_rb_1501_);
lean_dec(v___x_1492_);
return v_res_1504_;
}
}
static lean_object* _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__0));
v___x_1510_ = lean_unsigned_to_nat(34u);
v___x_1511_ = lean_unsigned_to_nat(217u);
v___x_1512_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__4));
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_1514_ = l_mkPanicMessageWithDecl(v___x_1513_, v___x_1512_, v___x_1511_, v___x_1510_, v___x_1509_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(lean_object* v_declName_1515_, lean_object* v_type_1516_, lean_object* v_value_1517_, uint8_t v_nondep_1518_, lean_object* v_toApplicative_1519_, lean_object* v___x_1520_, lean_object* v_us_1521_, lean_object* v_decl_1522_, lean_object* v_x_1523_, lean_object* v_i_1524_, lean_object* v_xs_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_info_1530_, lean_object* v_fixed_1531_, lean_object* v_used_1532_, lean_object* v_body_1533_, lean_object* v_toBind_1534_, lean_object* v_withNewLemmas_1535_, lean_object* v_val_x27_1536_, lean_object* v_val_1537_, uint8_t v___x_1538_, lean_object* v_____r_1539_){
_start:
{
uint8_t v___y_1541_; lean_object* v___y_1542_; uint8_t v___y_1558_; uint8_t v___x_1560_; 
v___x_1560_ = lean_expr_eqv(v_val_1537_, v_val_x27_1536_);
if (v___x_1560_ == 0)
{
v___y_1558_ = v_nondep_1518_;
goto v___jp_1557_;
}
else
{
v___y_1558_ = v___x_1538_;
goto v___jp_1557_;
}
v___jp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1543_ = lean_box(v_nondep_1518_);
v___x_1544_ = lean_box(v___y_1541_);
v___f_1545_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_1545_, 0, v_declName_1515_);
lean_closure_set(v___f_1545_, 1, v_type_1516_);
lean_closure_set(v___f_1545_, 2, v___y_1542_);
lean_closure_set(v___f_1545_, 3, v_value_1517_);
lean_closure_set(v___f_1545_, 4, v___x_1543_);
lean_closure_set(v___f_1545_, 5, v_toApplicative_1519_);
lean_closure_set(v___f_1545_, 6, v___x_1520_);
lean_closure_set(v___f_1545_, 7, v___x_1544_);
lean_closure_set(v___f_1545_, 8, v_us_1521_);
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_decl_1522_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___x_1548_);
lean_inc_ref(v_x_1523_);
v___x_1550_ = lean_array_push(v___x_1549_, v_x_1523_);
v___x_1551_ = lean_nat_add(v_i_1524_, v___x_1548_);
v___x_1552_ = lean_array_push(v_xs_1525_, v_x_1523_);
lean_inc_ref(v_inst_1528_);
lean_inc_ref(v_inst_1526_);
v___x_1553_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1526_, v_inst_1527_, v_inst_1528_, v_inst_1529_, v_info_1530_, v_fixed_1531_, v_used_1532_, v_body_1533_, v___x_1551_, v___x_1552_);
v___x_1554_ = lean_apply_4(v_toBind_1534_, lean_box(0), lean_box(0), v___x_1553_, v___f_1545_);
v___x_1555_ = lean_apply_3(v_withNewLemmas_1535_, lean_box(0), v___x_1550_, v___x_1554_);
v___x_1556_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1528_, v_inst_1526_, v___x_1547_, v___x_1555_);
return v___x_1556_;
}
v___jp_1557_:
{
if (v___y_1558_ == 0)
{
lean_inc_ref(v_value_1517_);
v___y_1541_ = v___y_1558_;
v___y_1542_ = v_value_1517_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_expr_abstract(v_val_x27_1536_, v_xs_1525_);
v___y_1541_ = v___y_1558_;
v___y_1542_ = v___x_1559_;
goto v___jp_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_declName_1561_ = _args[0];
lean_object* v_type_1562_ = _args[1];
lean_object* v_value_1563_ = _args[2];
lean_object* v_nondep_1564_ = _args[3];
lean_object* v_toApplicative_1565_ = _args[4];
lean_object* v___x_1566_ = _args[5];
lean_object* v_us_1567_ = _args[6];
lean_object* v_decl_1568_ = _args[7];
lean_object* v_x_1569_ = _args[8];
lean_object* v_i_1570_ = _args[9];
lean_object* v_xs_1571_ = _args[10];
lean_object* v_inst_1572_ = _args[11];
lean_object* v_inst_1573_ = _args[12];
lean_object* v_inst_1574_ = _args[13];
lean_object* v_inst_1575_ = _args[14];
lean_object* v_info_1576_ = _args[15];
lean_object* v_fixed_1577_ = _args[16];
lean_object* v_used_1578_ = _args[17];
lean_object* v_body_1579_ = _args[18];
lean_object* v_toBind_1580_ = _args[19];
lean_object* v_withNewLemmas_1581_ = _args[20];
lean_object* v_val_x27_1582_ = _args[21];
lean_object* v_val_1583_ = _args[22];
lean_object* v___x_1584_ = _args[23];
lean_object* v_____r_1585_ = _args[24];
_start:
{
uint8_t v_nondep_13583__boxed_1586_; uint8_t v___x_13590__boxed_1587_; lean_object* v_res_1588_; 
v_nondep_13583__boxed_1586_ = lean_unbox(v_nondep_1564_);
v___x_13590__boxed_1587_ = lean_unbox(v___x_1584_);
v_res_1588_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4(v_declName_1561_, v_type_1562_, v_value_1563_, v_nondep_13583__boxed_1586_, v_toApplicative_1565_, v___x_1566_, v_us_1567_, v_decl_1568_, v_x_1569_, v_i_1570_, v_xs_1571_, v_inst_1572_, v_inst_1573_, v_inst_1574_, v_inst_1575_, v_info_1576_, v_fixed_1577_, v_used_1578_, v_body_1579_, v_toBind_1580_, v_withNewLemmas_1581_, v_val_x27_1582_, v_val_1583_, v___x_13590__boxed_1587_, v_____r_1585_);
lean_dec_ref(v_val_1583_);
lean_dec_ref(v_val_x27_1582_);
lean_dec(v_i_1570_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(lean_object* v_declName_1589_, lean_object* v_type_1590_, lean_object* v_value_1591_, uint8_t v_nondep_1592_, lean_object* v_toApplicative_1593_, lean_object* v___x_1594_, lean_object* v_us_1595_, lean_object* v_decl_1596_, lean_object* v_x_1597_, lean_object* v_i_1598_, lean_object* v_xs_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_info_1604_, lean_object* v_fixed_1605_, lean_object* v_used_1606_, lean_object* v_body_1607_, lean_object* v_toBind_1608_, lean_object* v_withNewLemmas_1609_, lean_object* v_val_1610_, uint8_t v___x_1611_, lean_object* v_val_x27_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v_toApplicative_1614_; lean_object* v_toFunctor_1615_; lean_object* v_toSeq_1616_; lean_object* v_toSeqLeft_1617_; lean_object* v_toSeqRight_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___f_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_toApplicative_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1667_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1614_ = lean_ctor_get(v___x_1613_, 0);
v_toFunctor_1615_ = lean_ctor_get(v_toApplicative_1614_, 0);
v_toSeq_1616_ = lean_ctor_get(v_toApplicative_1614_, 2);
v_toSeqLeft_1617_ = lean_ctor_get(v_toApplicative_1614_, 3);
v_toSeqRight_1618_ = lean_ctor_get(v_toApplicative_1614_, 4);
v___f_1619_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1620_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1615_, 2);
v___f_1621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1621_, 0, v_toFunctor_1615_);
v___f_1622_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1622_, 0, v_toFunctor_1615_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___f_1621_);
lean_ctor_set(v___x_1623_, 1, v___f_1622_);
lean_inc(v_toSeqRight_1618_);
v___f_1624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1624_, 0, v_toSeqRight_1618_);
lean_inc(v_toSeqLeft_1617_);
v___f_1625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1625_, 0, v_toSeqLeft_1617_);
lean_inc(v_toSeq_1616_);
v___f_1626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1626_, 0, v_toSeq_1616_);
v___x_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1623_);
lean_ctor_set(v___x_1627_, 1, v___f_1619_);
lean_ctor_set(v___x_1627_, 2, v___f_1626_);
lean_ctor_set(v___x_1627_, 3, v___f_1625_);
lean_ctor_set(v___x_1627_, 4, v___f_1624_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v___f_1620_);
v___x_1629_ = l_StateRefT_x27_instMonad___redArg(v___x_1628_);
v_toApplicative_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v___x_1629_, 1);
lean_dec(v_unused_1668_);
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1667_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_toApplicative_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1667_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_toFunctor_1634_; lean_object* v_toSeq_1635_; lean_object* v_toSeqLeft_1636_; lean_object* v_toSeqRight_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1665_; 
v_toFunctor_1634_ = lean_ctor_get(v_toApplicative_1630_, 0);
v_toSeq_1635_ = lean_ctor_get(v_toApplicative_1630_, 2);
v_toSeqLeft_1636_ = lean_ctor_get(v_toApplicative_1630_, 3);
v_toSeqRight_1637_ = lean_ctor_get(v_toApplicative_1630_, 4);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_toApplicative_1630_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_toApplicative_1630_, 1);
lean_dec(v_unused_1666_);
v___x_1639_ = v_toApplicative_1630_;
v_isShared_1640_ = v_isSharedCheck_1665_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_toSeqRight_1637_);
lean_inc(v_toSeqLeft_1636_);
lean_inc(v_toSeq_1635_);
lean_inc(v_toFunctor_1634_);
lean_dec(v_toApplicative_1630_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1665_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___f_1643_; lean_object* v_cls_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___x_1654_; 
v___x_1641_ = lean_box(v_nondep_1592_);
v___x_1642_ = lean_box(v___x_1611_);
lean_inc_ref(v_val_1610_);
lean_inc_ref(v_val_x27_1612_);
lean_inc(v_toBind_1608_);
lean_inc(v_inst_1601_);
lean_inc(v_declName_1589_);
v___f_1643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__4___boxed), 25, 24);
lean_closure_set(v___f_1643_, 0, v_declName_1589_);
lean_closure_set(v___f_1643_, 1, v_type_1590_);
lean_closure_set(v___f_1643_, 2, v_value_1591_);
lean_closure_set(v___f_1643_, 3, v___x_1641_);
lean_closure_set(v___f_1643_, 4, v_toApplicative_1593_);
lean_closure_set(v___f_1643_, 5, v___x_1594_);
lean_closure_set(v___f_1643_, 6, v_us_1595_);
lean_closure_set(v___f_1643_, 7, v_decl_1596_);
lean_closure_set(v___f_1643_, 8, v_x_1597_);
lean_closure_set(v___f_1643_, 9, v_i_1598_);
lean_closure_set(v___f_1643_, 10, v_xs_1599_);
lean_closure_set(v___f_1643_, 11, v_inst_1600_);
lean_closure_set(v___f_1643_, 12, v_inst_1601_);
lean_closure_set(v___f_1643_, 13, v_inst_1602_);
lean_closure_set(v___f_1643_, 14, v_inst_1603_);
lean_closure_set(v___f_1643_, 15, v_info_1604_);
lean_closure_set(v___f_1643_, 16, v_fixed_1605_);
lean_closure_set(v___f_1643_, 17, v_used_1606_);
lean_closure_set(v___f_1643_, 18, v_body_1607_);
lean_closure_set(v___f_1643_, 19, v_toBind_1608_);
lean_closure_set(v___f_1643_, 20, v_withNewLemmas_1609_);
lean_closure_set(v___f_1643_, 21, v_val_x27_1612_);
lean_closure_set(v___f_1643_, 22, v_val_1610_);
lean_closure_set(v___f_1643_, 23, v___x_1642_);
v_cls_1644_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1645_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1646_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1634_);
v___f_1647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1647_, 0, v_toFunctor_1634_);
v___f_1648_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1648_, 0, v_toFunctor_1634_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___f_1647_);
lean_ctor_set(v___x_1649_, 1, v___f_1648_);
v___f_1650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1650_, 0, v_toSeqRight_1637_);
v___f_1651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1651_, 0, v_toSeqLeft_1636_);
v___f_1652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1652_, 0, v_toSeq_1635_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 4, v___f_1650_);
lean_ctor_set(v___x_1639_, 3, v___f_1651_);
lean_ctor_set(v___x_1639_, 2, v___f_1652_);
lean_ctor_set(v___x_1639_, 1, v___f_1645_);
lean_ctor_set(v___x_1639_, 0, v___x_1649_);
v___x_1654_ = v___x_1639_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___f_1645_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v___f_1652_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___f_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v___f_1650_);
v___x_1654_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v___f_1646_);
lean_ctor_set(v___x_1632_, 0, v___x_1654_);
v___x_1656_ = v___x_1632_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___f_1646_);
v___x_1656_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___f_1657_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1660_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_1660_, 0, v_cls_1644_);
lean_closure_set(v___f_1660_, 1, v___x_1658_);
lean_closure_set(v___f_1660_, 2, v___f_1657_);
lean_closure_set(v___f_1660_, 3, v_declName_1589_);
lean_closure_set(v___f_1660_, 4, v_val_1610_);
lean_closure_set(v___f_1660_, 5, v_val_x27_1612_);
lean_closure_set(v___f_1660_, 6, v___x_1656_);
lean_closure_set(v___f_1660_, 7, v___x_1659_);
v___x_1661_ = lean_apply_2(v_inst_1601_, lean_box(0), v___f_1660_);
v___x_1662_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1661_, v___f_1643_);
return v___x_1662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_declName_1669_ = _args[0];
lean_object* v_type_1670_ = _args[1];
lean_object* v_value_1671_ = _args[2];
lean_object* v_nondep_1672_ = _args[3];
lean_object* v_toApplicative_1673_ = _args[4];
lean_object* v___x_1674_ = _args[5];
lean_object* v_us_1675_ = _args[6];
lean_object* v_decl_1676_ = _args[7];
lean_object* v_x_1677_ = _args[8];
lean_object* v_i_1678_ = _args[9];
lean_object* v_xs_1679_ = _args[10];
lean_object* v_inst_1680_ = _args[11];
lean_object* v_inst_1681_ = _args[12];
lean_object* v_inst_1682_ = _args[13];
lean_object* v_inst_1683_ = _args[14];
lean_object* v_info_1684_ = _args[15];
lean_object* v_fixed_1685_ = _args[16];
lean_object* v_used_1686_ = _args[17];
lean_object* v_body_1687_ = _args[18];
lean_object* v_toBind_1688_ = _args[19];
lean_object* v_withNewLemmas_1689_ = _args[20];
lean_object* v_val_1690_ = _args[21];
lean_object* v___x_1691_ = _args[22];
lean_object* v_val_x27_1692_ = _args[23];
_start:
{
uint8_t v_nondep_13614__boxed_1693_; uint8_t v___x_13621__boxed_1694_; lean_object* v_res_1695_; 
v_nondep_13614__boxed_1693_ = lean_unbox(v_nondep_1672_);
v___x_13621__boxed_1694_ = lean_unbox(v___x_1691_);
v_res_1695_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6(v_declName_1669_, v_type_1670_, v_value_1671_, v_nondep_13614__boxed_1693_, v_toApplicative_1673_, v___x_1674_, v_us_1675_, v_decl_1676_, v_x_1677_, v_i_1678_, v_xs_1679_, v_inst_1680_, v_inst_1681_, v_inst_1682_, v_inst_1683_, v_info_1684_, v_fixed_1685_, v_used_1686_, v_body_1687_, v_toBind_1688_, v_withNewLemmas_1689_, v_val_1690_, v___x_13621__boxed_1694_, v_val_x27_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(lean_object* v_decl_1696_, lean_object* v_declName_1697_, lean_object* v_type_1698_, lean_object* v_value_1699_, uint8_t v_nondep_1700_, lean_object* v_toApplicative_1701_, lean_object* v___x_1702_, lean_object* v_us_1703_, lean_object* v_inst_1704_, lean_object* v_x_1705_, lean_object* v_i_1706_, lean_object* v_xs_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_info_1711_, lean_object* v_fixed_1712_, lean_object* v_used_1713_, lean_object* v_body_1714_, lean_object* v_toBind_1715_, lean_object* v_withNewLemmas_1716_, lean_object* v_____x_1717_){
_start:
{
lean_object* v_snd_1718_; lean_object* v_fst_1719_; lean_object* v_fst_1720_; lean_object* v_snd_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1740_; 
v_snd_1718_ = lean_ctor_get(v_____x_1717_, 1);
lean_inc(v_snd_1718_);
v_fst_1719_ = lean_ctor_get(v_____x_1717_, 0);
lean_inc(v_fst_1719_);
lean_dec_ref(v_____x_1717_);
v_fst_1720_ = lean_ctor_get(v_snd_1718_, 0);
v_snd_1721_ = lean_ctor_get(v_snd_1718_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_snd_1718_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1723_ = v_snd_1718_;
v_isShared_1724_ = v_isSharedCheck_1740_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_snd_1721_);
lean_inc(v_fst_1720_);
lean_dec(v_snd_1718_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1740_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_box(0);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 1);
lean_ctor_set(v___x_1723_, 1, v___x_1725_);
lean_ctor_set(v___x_1723_, 0, v_decl_1696_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_decl_1696_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_box(v_nondep_1700_);
lean_inc_ref_n(v_inst_1704_, 2);
v___f_1730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___boxed), 13, 12);
lean_closure_set(v___f_1730_, 0, v_declName_1697_);
lean_closure_set(v___f_1730_, 1, v_type_1698_);
lean_closure_set(v___f_1730_, 2, v_fst_1719_);
lean_closure_set(v___f_1730_, 3, v___x_1728_);
lean_closure_set(v___f_1730_, 4, v_value_1699_);
lean_closure_set(v___f_1730_, 5, v___x_1729_);
lean_closure_set(v___f_1730_, 6, v_fst_1720_);
lean_closure_set(v___f_1730_, 7, v_toApplicative_1701_);
lean_closure_set(v___f_1730_, 8, v___x_1702_);
lean_closure_set(v___f_1730_, 9, v_us_1703_);
lean_closure_set(v___f_1730_, 10, v_snd_1721_);
lean_closure_set(v___f_1730_, 11, v_inst_1704_);
v___x_1731_ = lean_mk_empty_array_with_capacity(v___x_1728_);
lean_inc_ref(v_x_1705_);
v___x_1732_ = lean_array_push(v___x_1731_, v_x_1705_);
v___x_1733_ = lean_nat_add(v_i_1706_, v___x_1728_);
v___x_1734_ = lean_array_push(v_xs_1707_, v_x_1705_);
lean_inc_ref(v_inst_1709_);
v___x_1735_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1704_, v_inst_1708_, v_inst_1709_, v_inst_1710_, v_info_1711_, v_fixed_1712_, v_used_1713_, v_body_1714_, v___x_1733_, v___x_1734_);
v___x_1736_ = lean_apply_4(v_toBind_1715_, lean_box(0), lean_box(0), v___x_1735_, v___f_1730_);
v___x_1737_ = lean_apply_3(v_withNewLemmas_1716_, lean_box(0), v___x_1732_, v___x_1736_);
v___x_1738_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_1709_, v_inst_1704_, v___x_1727_, v___x_1737_);
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_decl_1741_ = _args[0];
lean_object* v_declName_1742_ = _args[1];
lean_object* v_type_1743_ = _args[2];
lean_object* v_value_1744_ = _args[3];
lean_object* v_nondep_1745_ = _args[4];
lean_object* v_toApplicative_1746_ = _args[5];
lean_object* v___x_1747_ = _args[6];
lean_object* v_us_1748_ = _args[7];
lean_object* v_inst_1749_ = _args[8];
lean_object* v_x_1750_ = _args[9];
lean_object* v_i_1751_ = _args[10];
lean_object* v_xs_1752_ = _args[11];
lean_object* v_inst_1753_ = _args[12];
lean_object* v_inst_1754_ = _args[13];
lean_object* v_inst_1755_ = _args[14];
lean_object* v_info_1756_ = _args[15];
lean_object* v_fixed_1757_ = _args[16];
lean_object* v_used_1758_ = _args[17];
lean_object* v_body_1759_ = _args[18];
lean_object* v_toBind_1760_ = _args[19];
lean_object* v_withNewLemmas_1761_ = _args[20];
lean_object* v_____x_1762_ = _args[21];
_start:
{
uint8_t v_nondep_13556__boxed_1763_; lean_object* v_res_1764_; 
v_nondep_13556__boxed_1763_ = lean_unbox(v_nondep_1745_);
v_res_1764_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8(v_decl_1741_, v_declName_1742_, v_type_1743_, v_value_1744_, v_nondep_13556__boxed_1763_, v_toApplicative_1746_, v___x_1747_, v_us_1748_, v_inst_1749_, v_x_1750_, v_i_1751_, v_xs_1752_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v_info_1756_, v_fixed_1757_, v_used_1758_, v_body_1759_, v_toBind_1760_, v_withNewLemmas_1761_, v_____x_1762_);
lean_dec(v_i_1751_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_1765_ = _args[0];
lean_object* v_declName_1766_ = _args[1];
lean_object* v_type_1767_ = _args[2];
lean_object* v_value_1768_ = _args[3];
lean_object* v_us_1769_ = _args[4];
lean_object* v___x_1770_ = _args[5];
lean_object* v_toApplicative_1771_ = _args[6];
lean_object* v_nondep_1772_ = _args[7];
lean_object* v_i_1773_ = _args[8];
lean_object* v_xs_1774_ = _args[9];
lean_object* v_inst_1775_ = _args[10];
lean_object* v_inst_1776_ = _args[11];
lean_object* v_inst_1777_ = _args[12];
lean_object* v_inst_1778_ = _args[13];
lean_object* v_info_1779_ = _args[14];
lean_object* v_fixed_1780_ = _args[15];
lean_object* v_used_1781_ = _args[16];
lean_object* v_body_1782_ = _args[17];
lean_object* v_toBind_1783_ = _args[18];
lean_object* v_____r_1784_ = _args[19];
_start:
{
uint8_t v_nondep_13539__boxed_1785_; lean_object* v_res_1786_; 
v_nondep_13539__boxed_1785_ = lean_unbox(v_nondep_1772_);
v_res_1786_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(v___x_1765_, v_declName_1766_, v_type_1767_, v_value_1768_, v_us_1769_, v___x_1770_, v_toApplicative_1771_, v_nondep_13539__boxed_1785_, v_i_1773_, v_xs_1774_, v_inst_1775_, v_inst_1776_, v_inst_1777_, v_inst_1778_, v_info_1779_, v_fixed_1780_, v_used_1781_, v_body_1782_, v_toBind_1783_, v_____r_1784_);
lean_dec(v_i_1773_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_info_1791_, lean_object* v_fixed_1792_, lean_object* v_used_1793_, lean_object* v_e_1794_, lean_object* v_i_1795_, lean_object* v_xs_1796_){
_start:
{
lean_object* v_haveInfo_1802_; lean_object* v_body_1803_; lean_object* v_bodyType_1804_; lean_object* v_level_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_haveInfo_1802_ = lean_ctor_get(v_info_1791_, 0);
v_body_1803_ = lean_ctor_get(v_info_1791_, 3);
v_bodyType_1804_ = lean_ctor_get(v_info_1791_, 4);
v_level_1805_ = lean_ctor_get(v_info_1791_, 5);
v___x_1806_ = lean_array_get_size(v_haveInfo_1802_);
v___x_1807_ = lean_nat_dec_lt(v_i_1795_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v_toApplicative_1808_; lean_object* v_toBind_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1870_; 
lean_inc(v_level_1805_);
lean_inc_ref(v_bodyType_1804_);
lean_inc_ref(v_body_1803_);
lean_dec(v_i_1795_);
lean_dec_ref(v_used_1793_);
lean_dec_ref(v_fixed_1792_);
lean_dec_ref(v_info_1791_);
lean_dec_ref(v_inst_1789_);
v_toApplicative_1808_ = lean_ctor_get(v_inst_1787_, 0);
v_toBind_1809_ = lean_ctor_get(v_inst_1787_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_inst_1787_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1811_ = v_inst_1787_;
v_isShared_1812_ = v_isSharedCheck_1870_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_toBind_1809_);
lean_inc(v_toApplicative_1808_);
lean_dec(v_inst_1787_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1870_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v_toApplicative_1814_; lean_object* v_toFunctor_1815_; lean_object* v_toSeq_1816_; lean_object* v_toSeqLeft_1817_; lean_object* v_toSeqRight_1818_; lean_object* v___f_1819_; lean_object* v___f_1820_; lean_object* v___f_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___f_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1814_ = lean_ctor_get(v___x_1813_, 0);
v_toFunctor_1815_ = lean_ctor_get(v_toApplicative_1814_, 0);
v_toSeq_1816_ = lean_ctor_get(v_toApplicative_1814_, 2);
v_toSeqLeft_1817_ = lean_ctor_get(v_toApplicative_1814_, 3);
v_toSeqRight_1818_ = lean_ctor_get(v_toApplicative_1814_, 4);
v___f_1819_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1820_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1815_, 2);
v___f_1821_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1821_, 0, v_toFunctor_1815_);
v___f_1822_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1822_, 0, v_toFunctor_1815_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___f_1821_);
lean_ctor_set(v___x_1823_, 1, v___f_1822_);
lean_inc(v_toSeqRight_1818_);
v___f_1824_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1824_, 0, v_toSeqRight_1818_);
lean_inc(v_toSeqLeft_1817_);
v___f_1825_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1825_, 0, v_toSeqLeft_1817_);
lean_inc(v_toSeq_1816_);
v___f_1826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1826_, 0, v_toSeq_1816_);
v___x_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1823_);
lean_ctor_set(v___x_1827_, 1, v___f_1819_);
lean_ctor_set(v___x_1827_, 2, v___f_1826_);
lean_ctor_set(v___x_1827_, 3, v___f_1825_);
lean_ctor_set(v___x_1827_, 4, v___f_1824_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___f_1820_);
lean_ctor_set(v___x_1811_, 0, v___x_1827_);
v___x_1829_ = v___x_1811_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___f_1820_);
v___x_1829_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v_toApplicative_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1867_; 
v___x_1830_ = l_StateRefT_x27_instMonad___redArg(v___x_1829_);
v_toApplicative_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v___x_1830_, 1);
lean_dec(v_unused_1868_);
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1867_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_toApplicative_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1867_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_toFunctor_1835_; lean_object* v_toSeq_1836_; lean_object* v_toSeqLeft_1837_; lean_object* v_toSeqRight_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1865_; 
v_toFunctor_1835_ = lean_ctor_get(v_toApplicative_1831_, 0);
v_toSeq_1836_ = lean_ctor_get(v_toApplicative_1831_, 2);
v_toSeqLeft_1837_ = lean_ctor_get(v_toApplicative_1831_, 3);
v_toSeqRight_1838_ = lean_ctor_get(v_toApplicative_1831_, 4);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_toApplicative_1831_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v_toApplicative_1831_, 1);
lean_dec(v_unused_1866_);
v___x_1840_ = v_toApplicative_1831_;
v_isShared_1841_ = v_isSharedCheck_1865_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_toSeqRight_1838_);
lean_inc(v_toSeqLeft_1837_);
lean_inc(v_toSeq_1836_);
lean_inc(v_toFunctor_1835_);
lean_dec(v_toApplicative_1831_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1865_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v_cls_1844_; lean_object* v___f_1845_; lean_object* v___f_1846_; lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___x_1854_; 
v___x_1842_ = lean_box(v___x_1807_);
lean_inc(v_toBind_1809_);
lean_inc_ref(v_body_1803_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_1843_, 0, v_inst_1790_);
lean_closure_set(v___f_1843_, 1, v_bodyType_1804_);
lean_closure_set(v___f_1843_, 2, v_xs_1796_);
lean_closure_set(v___f_1843_, 3, v_toApplicative_1808_);
lean_closure_set(v___f_1843_, 4, v_level_1805_);
lean_closure_set(v___f_1843_, 5, v_e_1794_);
lean_closure_set(v___f_1843_, 6, v___x_1842_);
lean_closure_set(v___f_1843_, 7, v_body_1803_);
lean_closure_set(v___f_1843_, 8, v_toBind_1809_);
v_cls_1844_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1845_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1846_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1835_);
v___f_1847_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1847_, 0, v_toFunctor_1835_);
v___f_1848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1848_, 0, v_toFunctor_1835_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___f_1847_);
lean_ctor_set(v___x_1849_, 1, v___f_1848_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toSeqRight_1838_);
v___f_1851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1851_, 0, v_toSeqLeft_1837_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toSeq_1836_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 4, v___f_1850_);
lean_ctor_set(v___x_1840_, 3, v___f_1851_);
lean_ctor_set(v___x_1840_, 2, v___f_1852_);
lean_ctor_set(v___x_1840_, 1, v___f_1845_);
lean_ctor_set(v___x_1840_, 0, v___x_1849_);
v___x_1854_ = v___x_1840_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___f_1845_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v___f_1852_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v___f_1851_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v___f_1850_);
v___x_1854_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___f_1846_);
lean_ctor_set(v___x_1833_, 0, v___x_1854_);
v___x_1856_ = v___x_1833_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___f_1846_);
v___x_1856_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___f_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___f_1857_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1858_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1859_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1860_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__2___boxed), 11, 6);
lean_closure_set(v___f_1860_, 0, v_cls_1844_);
lean_closure_set(v___f_1860_, 1, v___x_1858_);
lean_closure_set(v___f_1860_, 2, v___f_1857_);
lean_closure_set(v___f_1860_, 3, v_body_1803_);
lean_closure_set(v___f_1860_, 4, v___x_1856_);
lean_closure_set(v___f_1860_, 5, v___x_1859_);
v___x_1861_ = lean_apply_2(v_inst_1788_, lean_box(0), v___f_1860_);
v___x_1862_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___x_1861_, v___f_1843_);
return v___x_1862_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_e_1794_) == 8)
{
uint8_t v_nondep_1871_; 
v_nondep_1871_ = lean_ctor_get_uint8(v_e_1794_, sizeof(void*)*4 + 8);
if (v_nondep_1871_ == 1)
{
lean_object* v_declName_1872_; lean_object* v_type_1873_; lean_object* v_value_1874_; lean_object* v_body_1875_; lean_object* v_hinfo_1876_; lean_object* v_decl_1877_; lean_object* v_level_1878_; lean_object* v_x_1879_; lean_object* v_val_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_us_1883_; uint8_t v___y_1885_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_declName_1872_ = lean_ctor_get(v_e_1794_, 0);
lean_inc(v_declName_1872_);
v_type_1873_ = lean_ctor_get(v_e_1794_, 1);
lean_inc_ref(v_type_1873_);
v_value_1874_ = lean_ctor_get(v_e_1794_, 2);
lean_inc_ref(v_value_1874_);
v_body_1875_ = lean_ctor_get(v_e_1794_, 3);
lean_inc_ref(v_body_1875_);
lean_dec_ref(v_e_1794_);
v_hinfo_1876_ = lean_array_fget_borrowed(v_haveInfo_1802_, v_i_1795_);
v_decl_1877_ = lean_ctor_get(v_hinfo_1876_, 2);
v_level_1878_ = lean_ctor_get(v_hinfo_1876_, 3);
lean_inc_ref(v_decl_1877_);
v_x_1879_ = l_Lean_LocalDecl_toExpr(v_decl_1877_);
v_val_1880_ = l_Lean_LocalDecl_value(v_decl_1877_, v_nondep_1871_);
v___x_1881_ = lean_box(0);
lean_inc(v_level_1805_);
v___x_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_level_1805_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
lean_inc_ref(v___x_1882_);
lean_inc(v_level_1878_);
v_us_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_us_1883_, 0, v_level_1878_);
lean_ctor_set(v_us_1883_, 1, v___x_1882_);
v___x_1912_ = lean_array_get_size(v_used_1793_);
v___x_1913_ = lean_nat_dec_lt(v_i_1795_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_inc_ref(v_decl_1877_);
goto v___jp_1895_;
}
else
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_array_fget_borrowed(v_used_1793_, v_i_1795_);
v___x_1915_ = lean_unbox(v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v_toApplicative_1916_; lean_object* v_toBind_1917_; lean_object* v___x_1918_; lean_object* v_toApplicative_1919_; lean_object* v_toFunctor_1920_; lean_object* v_toSeq_1921_; lean_object* v_toSeqLeft_1922_; lean_object* v_toSeqRight_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v_toApplicative_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_x_1879_);
v_toApplicative_1916_ = lean_ctor_get(v_inst_1787_, 0);
lean_inc_ref(v_toApplicative_1916_);
v_toBind_1917_ = lean_ctor_get(v_inst_1787_, 1);
lean_inc(v_toBind_1917_);
v___x_1918_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__1);
v_toApplicative_1919_ = lean_ctor_get(v___x_1918_, 0);
v_toFunctor_1920_ = lean_ctor_get(v_toApplicative_1919_, 0);
v_toSeq_1921_ = lean_ctor_get(v_toApplicative_1919_, 2);
v_toSeqLeft_1922_ = lean_ctor_get(v_toApplicative_1919_, 3);
v_toSeqRight_1923_ = lean_ctor_get(v_toApplicative_1919_, 4);
v___f_1924_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__2));
v___f_1925_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__3));
lean_inc_ref_n(v_toFunctor_1920_, 2);
v___f_1926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1926_, 0, v_toFunctor_1920_);
v___f_1927_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1927_, 0, v_toFunctor_1920_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___f_1926_);
lean_ctor_set(v___x_1928_, 1, v___f_1927_);
lean_inc(v_toSeqRight_1923_);
v___f_1929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1929_, 0, v_toSeqRight_1923_);
lean_inc(v_toSeqLeft_1922_);
v___f_1930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1930_, 0, v_toSeqLeft_1922_);
lean_inc(v_toSeq_1921_);
v___f_1931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1931_, 0, v_toSeq_1921_);
v___x_1932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1928_);
lean_ctor_set(v___x_1932_, 1, v___f_1924_);
lean_ctor_set(v___x_1932_, 2, v___f_1931_);
lean_ctor_set(v___x_1932_, 3, v___f_1930_);
lean_ctor_set(v___x_1932_, 4, v___f_1929_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___f_1925_);
v___x_1934_ = l_StateRefT_x27_instMonad___redArg(v___x_1933_);
v_toApplicative_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v___x_1934_, 1);
lean_dec(v_unused_1972_);
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1971_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_toApplicative_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1971_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_toFunctor_1939_; lean_object* v_toSeq_1940_; lean_object* v_toSeqLeft_1941_; lean_object* v_toSeqRight_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1969_; 
v_toFunctor_1939_ = lean_ctor_get(v_toApplicative_1935_, 0);
v_toSeq_1940_ = lean_ctor_get(v_toApplicative_1935_, 2);
v_toSeqLeft_1941_ = lean_ctor_get(v_toApplicative_1935_, 3);
v_toSeqRight_1942_ = lean_ctor_get(v_toApplicative_1935_, 4);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_toApplicative_1935_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v_toApplicative_1935_, 1);
lean_dec(v_unused_1970_);
v___x_1944_ = v_toApplicative_1935_;
v_isShared_1945_ = v_isSharedCheck_1969_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_toSeqRight_1942_);
lean_inc(v_toSeqLeft_1941_);
lean_inc(v_toSeq_1940_);
lean_inc(v_toFunctor_1939_);
lean_dec(v_toApplicative_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1969_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___f_1947_; lean_object* v_cls_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___x_1958_; 
v___x_1946_ = lean_box(v_nondep_1871_);
lean_inc(v_toBind_1917_);
lean_inc(v_inst_1788_);
lean_inc(v_declName_1872_);
v___f_1947_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_1947_, 0, v___x_1881_);
lean_closure_set(v___f_1947_, 1, v_declName_1872_);
lean_closure_set(v___f_1947_, 2, v_type_1873_);
lean_closure_set(v___f_1947_, 3, v_value_1874_);
lean_closure_set(v___f_1947_, 4, v_us_1883_);
lean_closure_set(v___f_1947_, 5, v___x_1882_);
lean_closure_set(v___f_1947_, 6, v_toApplicative_1916_);
lean_closure_set(v___f_1947_, 7, v___x_1946_);
lean_closure_set(v___f_1947_, 8, v_i_1795_);
lean_closure_set(v___f_1947_, 9, v_xs_1796_);
lean_closure_set(v___f_1947_, 10, v_inst_1787_);
lean_closure_set(v___f_1947_, 11, v_inst_1788_);
lean_closure_set(v___f_1947_, 12, v_inst_1789_);
lean_closure_set(v___f_1947_, 13, v_inst_1790_);
lean_closure_set(v___f_1947_, 14, v_info_1791_);
lean_closure_set(v___f_1947_, 15, v_fixed_1792_);
lean_closure_set(v___f_1947_, 16, v_used_1793_);
lean_closure_set(v___f_1947_, 17, v_body_1875_);
lean_closure_set(v___f_1947_, 18, v_toBind_1917_);
v_cls_1948_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__8));
v___f_1949_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__9));
v___f_1950_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__10));
lean_inc_ref(v_toFunctor_1939_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toFunctor_1939_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toFunctor_1939_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___f_1951_);
lean_ctor_set(v___x_1953_, 1, v___f_1952_);
v___f_1954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1954_, 0, v_toSeqRight_1942_);
v___f_1955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1955_, 0, v_toSeqLeft_1941_);
v___f_1956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1956_, 0, v_toSeq_1940_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___f_1954_);
lean_ctor_set(v___x_1944_, 3, v___f_1955_);
lean_ctor_set(v___x_1944_, 2, v___f_1956_);
lean_ctor_set(v___x_1944_, 1, v___f_1949_);
lean_ctor_set(v___x_1944_, 0, v___x_1953_);
v___x_1958_ = v___x_1944_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___f_1949_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v___f_1956_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v___f_1955_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v___f_1954_);
v___x_1958_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___f_1950_);
lean_ctor_set(v___x_1937_, 0, v___x_1958_);
v___x_1960_ = v___x_1937_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___f_1950_);
v___x_1960_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___f_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___f_1961_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__11));
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__12));
v___x_1963_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___closed__14);
v___f_1964_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__15___boxed), 12, 7);
lean_closure_set(v___f_1964_, 0, v_cls_1948_);
lean_closure_set(v___f_1964_, 1, v___x_1962_);
lean_closure_set(v___f_1964_, 2, v___f_1961_);
lean_closure_set(v___f_1964_, 3, v_declName_1872_);
lean_closure_set(v___f_1964_, 4, v_val_1880_);
lean_closure_set(v___f_1964_, 5, v___x_1960_);
lean_closure_set(v___f_1964_, 6, v___x_1963_);
v___x_1965_ = lean_apply_2(v_inst_1788_, lean_box(0), v___f_1964_);
v___x_1966_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v___x_1965_, v___f_1947_);
return v___x_1966_;
}
}
}
}
}
else
{
lean_inc_ref(v_decl_1877_);
goto v___jp_1895_;
}
}
v___jp_1884_:
{
lean_object* v_toApplicative_1886_; lean_object* v_toBind_1887_; lean_object* v_withNewLemmas_1888_; lean_object* v_dsimp_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_toApplicative_1886_ = lean_ctor_get(v_inst_1787_, 0);
lean_inc_ref(v_toApplicative_1886_);
v_toBind_1887_ = lean_ctor_get(v_inst_1787_, 1);
lean_inc_n(v_toBind_1887_, 2);
v_withNewLemmas_1888_ = lean_ctor_get(v_inst_1790_, 0);
lean_inc(v_withNewLemmas_1888_);
v_dsimp_1889_ = lean_ctor_get(v_inst_1790_, 1);
lean_inc(v_dsimp_1889_);
v___x_1890_ = lean_box(v_nondep_1871_);
v___x_1891_ = lean_box(v___y_1885_);
lean_inc_ref(v_val_1880_);
v___f_1892_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__6___boxed), 24, 23);
lean_closure_set(v___f_1892_, 0, v_declName_1872_);
lean_closure_set(v___f_1892_, 1, v_type_1873_);
lean_closure_set(v___f_1892_, 2, v_value_1874_);
lean_closure_set(v___f_1892_, 3, v___x_1890_);
lean_closure_set(v___f_1892_, 4, v_toApplicative_1886_);
lean_closure_set(v___f_1892_, 5, v___x_1882_);
lean_closure_set(v___f_1892_, 6, v_us_1883_);
lean_closure_set(v___f_1892_, 7, v_decl_1877_);
lean_closure_set(v___f_1892_, 8, v_x_1879_);
lean_closure_set(v___f_1892_, 9, v_i_1795_);
lean_closure_set(v___f_1892_, 10, v_xs_1796_);
lean_closure_set(v___f_1892_, 11, v_inst_1787_);
lean_closure_set(v___f_1892_, 12, v_inst_1788_);
lean_closure_set(v___f_1892_, 13, v_inst_1789_);
lean_closure_set(v___f_1892_, 14, v_inst_1790_);
lean_closure_set(v___f_1892_, 15, v_info_1791_);
lean_closure_set(v___f_1892_, 16, v_fixed_1792_);
lean_closure_set(v___f_1892_, 17, v_used_1793_);
lean_closure_set(v___f_1892_, 18, v_body_1875_);
lean_closure_set(v___f_1892_, 19, v_toBind_1887_);
lean_closure_set(v___f_1892_, 20, v_withNewLemmas_1888_);
lean_closure_set(v___f_1892_, 21, v_val_1880_);
lean_closure_set(v___f_1892_, 22, v___x_1891_);
v___x_1893_ = lean_apply_1(v_dsimp_1889_, v_val_1880_);
v___x_1894_ = lean_apply_4(v_toBind_1887_, lean_box(0), lean_box(0), v___x_1893_, v___f_1892_);
return v___x_1894_;
}
v___jp_1895_:
{
uint8_t v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = 0;
v___x_1897_ = lean_array_get_size(v_fixed_1792_);
v___x_1898_ = lean_nat_dec_lt(v_i_1795_, v___x_1897_);
if (v___x_1898_ == 0)
{
v___y_1885_ = v___x_1896_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_fget_borrowed(v_fixed_1792_, v_i_1795_);
v___x_1900_ = lean_unbox(v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v_toApplicative_1901_; lean_object* v_toBind_1902_; lean_object* v_withNewLemmas_1903_; lean_object* v_simp_1904_; lean_object* v___x_1905_; lean_object* v___f_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_inc(v___x_1899_);
lean_inc(v_level_1878_);
v_toApplicative_1901_ = lean_ctor_get(v_inst_1787_, 0);
lean_inc_ref_n(v_toApplicative_1901_, 2);
v_toBind_1902_ = lean_ctor_get(v_inst_1787_, 1);
lean_inc_n(v_toBind_1902_, 3);
v_withNewLemmas_1903_ = lean_ctor_get(v_inst_1790_, 0);
lean_inc(v_withNewLemmas_1903_);
v_simp_1904_ = lean_ctor_get(v_inst_1790_, 2);
lean_inc(v_simp_1904_);
v___x_1905_ = lean_box(v_nondep_1871_);
lean_inc(v_inst_1788_);
lean_inc_ref(v_xs_1796_);
lean_inc_ref(v_value_1874_);
lean_inc_ref(v_type_1873_);
lean_inc(v_declName_1872_);
v___f_1906_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__8___boxed), 22, 21);
lean_closure_set(v___f_1906_, 0, v_decl_1877_);
lean_closure_set(v___f_1906_, 1, v_declName_1872_);
lean_closure_set(v___f_1906_, 2, v_type_1873_);
lean_closure_set(v___f_1906_, 3, v_value_1874_);
lean_closure_set(v___f_1906_, 4, v___x_1905_);
lean_closure_set(v___f_1906_, 5, v_toApplicative_1901_);
lean_closure_set(v___f_1906_, 6, v___x_1882_);
lean_closure_set(v___f_1906_, 7, v_us_1883_);
lean_closure_set(v___f_1906_, 8, v_inst_1787_);
lean_closure_set(v___f_1906_, 9, v_x_1879_);
lean_closure_set(v___f_1906_, 10, v_i_1795_);
lean_closure_set(v___f_1906_, 11, v_xs_1796_);
lean_closure_set(v___f_1906_, 12, v_inst_1788_);
lean_closure_set(v___f_1906_, 13, v_inst_1789_);
lean_closure_set(v___f_1906_, 14, v_inst_1790_);
lean_closure_set(v___f_1906_, 15, v_info_1791_);
lean_closure_set(v___f_1906_, 16, v_fixed_1792_);
lean_closure_set(v___f_1906_, 17, v_used_1793_);
lean_closure_set(v___f_1906_, 18, v_body_1875_);
lean_closure_set(v___f_1906_, 19, v_toBind_1902_);
lean_closure_set(v___f_1906_, 20, v_withNewLemmas_1903_);
v___f_1907_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1907_, 0, v___f_1906_);
v___x_1908_ = lean_box(v_nondep_1871_);
lean_inc_ref(v_val_1880_);
lean_inc_ref(v___f_1907_);
v___f_1909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__12___boxed), 15, 14);
lean_closure_set(v___f_1909_, 0, v_toApplicative_1901_);
lean_closure_set(v___f_1909_, 1, v_level_1878_);
lean_closure_set(v___f_1909_, 2, v___x_1881_);
lean_closure_set(v___f_1909_, 3, v_type_1873_);
lean_closure_set(v___f_1909_, 4, v_value_1874_);
lean_closure_set(v___f_1909_, 5, v___x_1899_);
lean_closure_set(v___f_1909_, 6, v_toBind_1902_);
lean_closure_set(v___f_1909_, 7, v___f_1907_);
lean_closure_set(v___f_1909_, 8, v_xs_1796_);
lean_closure_set(v___f_1909_, 9, v___x_1908_);
lean_closure_set(v___f_1909_, 10, v___f_1907_);
lean_closure_set(v___f_1909_, 11, v_declName_1872_);
lean_closure_set(v___f_1909_, 12, v_val_1880_);
lean_closure_set(v___f_1909_, 13, v_inst_1788_);
v___x_1910_ = lean_apply_1(v_simp_1904_, v_val_1880_);
v___x_1911_ = lean_apply_4(v_toBind_1902_, lean_box(0), lean_box(0), v___x_1910_, v___f_1909_);
return v___x_1911_;
}
else
{
v___y_1885_ = v___x_1896_;
goto v___jp_1884_;
}
}
}
}
else
{
lean_dec_ref(v_e_1794_);
lean_dec_ref(v_xs_1796_);
lean_dec(v_i_1795_);
lean_dec_ref(v_used_1793_);
lean_dec_ref(v_fixed_1792_);
lean_dec_ref(v_info_1791_);
lean_dec_ref(v_inst_1790_);
lean_dec_ref(v_inst_1789_);
lean_dec(v_inst_1788_);
goto v___jp_1797_;
}
}
else
{
lean_dec_ref(v_xs_1796_);
lean_dec(v_i_1795_);
lean_dec_ref(v_e_1794_);
lean_dec_ref(v_used_1793_);
lean_dec_ref(v_fixed_1792_);
lean_dec_ref(v_info_1791_);
lean_dec_ref(v_inst_1790_);
lean_dec_ref(v_inst_1789_);
lean_dec(v_inst_1788_);
goto v___jp_1797_;
}
}
v___jp_1797_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_instInhabitedSimpHaveResult_default;
v___x_1799_ = l_instInhabitedOfMonad___redArg(v_inst_1787_, v___x_1798_);
v___x_1800_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___closed__1);
v___x_1801_ = l_panic___redArg(v___x_1799_, v___x_1800_);
lean_dec(v___x_1799_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14(lean_object* v___x_1973_, lean_object* v_declName_1974_, lean_object* v_type_1975_, lean_object* v_value_1976_, lean_object* v_us_1977_, lean_object* v___x_1978_, lean_object* v_toApplicative_1979_, uint8_t v_nondep_1980_, lean_object* v_i_1981_, lean_object* v_xs_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_info_1987_, lean_object* v_fixed_1988_, lean_object* v_used_1989_, lean_object* v_body_1990_, lean_object* v_toBind_1991_, lean_object* v_____r_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v_x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__14___closed__1));
v_x_1994_ = l_Lean_mkConst(v___x_1993_, v___x_1973_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_box(v_nondep_1980_);
v___f_1997_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1997_, 0, v___x_1995_);
lean_closure_set(v___f_1997_, 1, v_declName_1974_);
lean_closure_set(v___f_1997_, 2, v_type_1975_);
lean_closure_set(v___f_1997_, 3, v_value_1976_);
lean_closure_set(v___f_1997_, 4, v_us_1977_);
lean_closure_set(v___f_1997_, 5, v___x_1978_);
lean_closure_set(v___f_1997_, 6, v_toApplicative_1979_);
lean_closure_set(v___f_1997_, 7, v___x_1996_);
v___x_1998_ = lean_nat_add(v_i_1981_, v___x_1995_);
v___x_1999_ = lean_array_push(v_xs_1982_, v_x_1994_);
v___x_2000_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_1983_, v_inst_1984_, v_inst_1985_, v_inst_1986_, v_info_1987_, v_fixed_1988_, v_used_1989_, v_body_1990_, v___x_1998_, v___x_1999_);
v___x_2001_ = lean_apply_4(v_toBind_1991_, lean_box(0), lean_box(0), v___x_2000_, v___f_1997_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux(lean_object* v_m_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_info_2007_, lean_object* v_fixed_2008_, lean_object* v_used_2009_, lean_object* v_e_2010_, lean_object* v_i_2011_, lean_object* v_xs_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2003_, v_inst_2004_, v_inst_2005_, v_inst_2006_, v_info_2007_, v_fixed_2008_, v_used_2009_, v_e_2010_, v_i_2011_, v_xs_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx(uint8_t v_x_2014_){
_start:
{
switch(v_x_2014_)
{
case 0:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_unsigned_to_nat(0u);
return v___x_2015_;
}
case 1:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_unsigned_to_nat(1u);
return v___x_2016_;
}
default: 
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_unsigned_to_nat(2u);
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorIdx___boxed(lean_object* v_x_2018_){
_start:
{
uint8_t v_x_boxed_2019_; lean_object* v_res_2020_; 
v_x_boxed_2019_ = lean_unbox(v_x_2018_);
v_res_2020_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_boxed_2019_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx(uint8_t v_x_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Meta_ZetaUnusedMode_ctorIdx(v_x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_toCtorIdx___boxed(lean_object* v_x_2023_){
_start:
{
uint8_t v_x_4__boxed_2024_; lean_object* v_res_2025_; 
v_x_4__boxed_2024_ = lean_unbox(v_x_2023_);
v_res_2025_ = l_Lean_Meta_ZetaUnusedMode_toCtorIdx(v_x_4__boxed_2024_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(lean_object* v_k_2026_){
_start:
{
lean_inc(v_k_2026_);
return v_k_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg___boxed(lean_object* v_k_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Meta_ZetaUnusedMode_ctorElim___redArg(v_k_2027_);
lean_dec(v_k_2027_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim(lean_object* v_motive_2029_, lean_object* v_ctorIdx_2030_, uint8_t v_t_2031_, lean_object* v_h_2032_, lean_object* v_k_2033_){
_start:
{
lean_inc(v_k_2033_);
return v_k_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_ctorElim___boxed(lean_object* v_motive_2034_, lean_object* v_ctorIdx_2035_, lean_object* v_t_2036_, lean_object* v_h_2037_, lean_object* v_k_2038_){
_start:
{
uint8_t v_t_boxed_2039_; lean_object* v_res_2040_; 
v_t_boxed_2039_ = lean_unbox(v_t_2036_);
v_res_2040_ = l_Lean_Meta_ZetaUnusedMode_ctorElim(v_motive_2034_, v_ctorIdx_2035_, v_t_boxed_2039_, v_h_2037_, v_k_2038_);
lean_dec(v_k_2038_);
lean_dec(v_ctorIdx_2035_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(lean_object* v_no_2041_){
_start:
{
lean_inc(v_no_2041_);
return v_no_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___redArg___boxed(lean_object* v_no_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Meta_ZetaUnusedMode_no_elim___redArg(v_no_2042_);
lean_dec(v_no_2042_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim(lean_object* v_motive_2044_, uint8_t v_t_2045_, lean_object* v_h_2046_, lean_object* v_no_2047_){
_start:
{
lean_inc(v_no_2047_);
return v_no_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_no_elim___boxed(lean_object* v_motive_2048_, lean_object* v_t_2049_, lean_object* v_h_2050_, lean_object* v_no_2051_){
_start:
{
uint8_t v_t_boxed_2052_; lean_object* v_res_2053_; 
v_t_boxed_2052_ = lean_unbox(v_t_2049_);
v_res_2053_ = l_Lean_Meta_ZetaUnusedMode_no_elim(v_motive_2048_, v_t_boxed_2052_, v_h_2050_, v_no_2051_);
lean_dec(v_no_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(lean_object* v_singlePass_2054_){
_start:
{
lean_inc(v_singlePass_2054_);
return v_singlePass_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg___boxed(lean_object* v_singlePass_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim___redArg(v_singlePass_2055_);
lean_dec(v_singlePass_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim(lean_object* v_motive_2057_, uint8_t v_t_2058_, lean_object* v_h_2059_, lean_object* v_singlePass_2060_){
_start:
{
lean_inc(v_singlePass_2060_);
return v_singlePass_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_singlePass_elim___boxed(lean_object* v_motive_2061_, lean_object* v_t_2062_, lean_object* v_h_2063_, lean_object* v_singlePass_2064_){
_start:
{
uint8_t v_t_boxed_2065_; lean_object* v_res_2066_; 
v_t_boxed_2065_ = lean_unbox(v_t_2062_);
v_res_2066_ = l_Lean_Meta_ZetaUnusedMode_singlePass_elim(v_motive_2061_, v_t_boxed_2065_, v_h_2063_, v_singlePass_2064_);
lean_dec(v_singlePass_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(lean_object* v_twoPasses_2067_){
_start:
{
lean_inc(v_twoPasses_2067_);
return v_twoPasses_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg___boxed(lean_object* v_twoPasses_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___redArg(v_twoPasses_2068_);
lean_dec(v_twoPasses_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(lean_object* v_motive_2070_, uint8_t v_t_2071_, lean_object* v_h_2072_, lean_object* v_twoPasses_2073_){
_start:
{
lean_inc(v_twoPasses_2073_);
return v_twoPasses_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ZetaUnusedMode_twoPasses_elim___boxed(lean_object* v_motive_2074_, lean_object* v_t_2075_, lean_object* v_h_2076_, lean_object* v_twoPasses_2077_){
_start:
{
uint8_t v_t_boxed_2078_; lean_object* v_res_2079_; 
v_t_boxed_2078_ = lean_unbox(v_t_2075_);
v_res_2079_ = l_Lean_Meta_ZetaUnusedMode_twoPasses_elim(v_motive_2074_, v_t_boxed_2078_, v_h_2076_, v_twoPasses_2077_);
lean_dec(v_twoPasses_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(lean_object* v_k_2080_, lean_object* v_b_2081_, lean_object* v_c_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; 
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
v___x_2088_ = lean_apply_7(v_k_2080_, v_b_2081_, v_c_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, lean_box(0));
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed(lean_object* v_k_2089_, lean_object* v_b_2090_, lean_object* v_c_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0(v_k_2089_, v_b_2090_, v_c_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(lean_object* v_e_2098_, lean_object* v_k_2099_, uint8_t v_cleanupAnnotations_2100_, uint8_t v_preserveNondepLet_2101_, uint8_t v_nondepLetOnly_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___f_2108_; uint8_t v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2108_, 0, v_k_2099_);
v___x_2109_ = 0;
v___x_2110_ = 1;
v___x_2111_ = lean_box(0);
v___x_2112_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2098_, v___x_2109_, v___x_2110_, v_preserveNondepLet_2101_, v_nondepLetOnly_2102_, v___x_2111_, v___f_2108_, v_cleanupAnnotations_2100_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2121_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2112_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2112_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg___boxed(lean_object* v_e_2129_, lean_object* v_k_2130_, lean_object* v_cleanupAnnotations_2131_, lean_object* v_preserveNondepLet_2132_, lean_object* v_nondepLetOnly_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2139_; uint8_t v_preserveNondepLet_boxed_2140_; uint8_t v_nondepLetOnly_boxed_2141_; lean_object* v_res_2142_; 
v_cleanupAnnotations_boxed_2139_ = lean_unbox(v_cleanupAnnotations_2131_);
v_preserveNondepLet_boxed_2140_ = lean_unbox(v_preserveNondepLet_2132_);
v_nondepLetOnly_boxed_2141_ = lean_unbox(v_nondepLetOnly_2133_);
v_res_2142_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2129_, v_k_2130_, v_cleanupAnnotations_boxed_2139_, v_preserveNondepLet_boxed_2140_, v_nondepLetOnly_boxed_2141_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(lean_object* v_00_u03b1_2143_, lean_object* v_e_2144_, lean_object* v_k_2145_, uint8_t v_cleanupAnnotations_2146_, uint8_t v_preserveNondepLet_2147_, uint8_t v_nondepLetOnly_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2144_, v_k_2145_, v_cleanupAnnotations_2146_, v_preserveNondepLet_2147_, v_nondepLetOnly_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_e_2156_, lean_object* v_k_2157_, lean_object* v_cleanupAnnotations_2158_, lean_object* v_preserveNondepLet_2159_, lean_object* v_nondepLetOnly_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2166_; uint8_t v_preserveNondepLet_boxed_2167_; uint8_t v_nondepLetOnly_boxed_2168_; lean_object* v_res_2169_; 
v_cleanupAnnotations_boxed_2166_ = lean_unbox(v_cleanupAnnotations_2158_);
v_preserveNondepLet_boxed_2167_ = lean_unbox(v_preserveNondepLet_2159_);
v_nondepLetOnly_boxed_2168_ = lean_unbox(v_nondepLetOnly_2160_);
v_res_2169_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1(v_00_u03b1_2155_, v_e_2156_, v_k_2157_, v_cleanupAnnotations_boxed_2166_, v_preserveNondepLet_boxed_2167_, v_nondepLetOnly_boxed_2168_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(lean_object* v_xs_2170_, lean_object* v_b_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_snd_2176_; lean_object* v_fst_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2232_; 
v_snd_2176_ = lean_ctor_get(v_b_2171_, 1);
v_fst_2177_ = lean_ctor_get(v_b_2171_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_b_2171_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2179_ = v_b_2171_;
v_isShared_2180_ = v_isSharedCheck_2232_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2176_);
lean_inc(v_fst_2177_);
lean_dec(v_b_2171_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2232_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_fst_2181_; lean_object* v_snd_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2231_; 
v_fst_2181_ = lean_ctor_get(v_snd_2176_, 0);
v_snd_2182_ = lean_ctor_get(v_snd_2176_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_snd_2176_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2184_ = v_snd_2176_;
v_isShared_2185_ = v_isSharedCheck_2231_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_snd_2182_);
lean_inc(v_fst_2181_);
lean_dec(v_snd_2176_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2231_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_nat_dec_lt(v___x_2186_, v_snd_2182_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2189_; 
if (v_isShared_2185_ == 0)
{
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_fst_2181_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_snd_2182_);
v___x_2189_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2189_);
v___x_2191_ = v___x_2179_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_fst_2177_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
}
else
{
lean_object* v_fvarSet_2195_; lean_object* v___x_2196_; lean_object* v_i_2197_; lean_object* v___x_2198_; lean_object* v_x_2199_; lean_object* v_xFVarId_2200_; uint8_t v___x_2201_; 
v_fvarSet_2195_ = lean_ctor_get(v_fst_2177_, 1);
v___x_2196_ = lean_unsigned_to_nat(1u);
v_i_2197_ = lean_nat_sub(v_snd_2182_, v___x_2196_);
lean_dec(v_snd_2182_);
v___x_2198_ = l_Lean_instInhabitedExpr;
v_x_2199_ = lean_array_get_borrowed(v___x_2198_, v_xs_2170_, v_i_2197_);
v_xFVarId_2200_ = l_Lean_Expr_fvarId_x21(v_x_2199_);
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect_spec__3___redArg(v_xFVarId_2200_, v_fvarSet_2195_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2203_; 
lean_dec(v_xFVarId_2200_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v_i_2197_);
v___x_2203_ = v___x_2184_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_fst_2181_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_i_2197_);
v___x_2203_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2205_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2203_);
v___x_2205_ = v___x_2179_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_fst_2177_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
v_b_2171_ = v___x_2205_;
goto _start;
}
}
}
else
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_FVarId_getDecl___redArg(v_xFVarId_2200_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = l_Lean_LocalDecl_type(v_a_2210_);
v___x_2212_ = l_Lean_collectFVars(v_fst_2177_, v___x_2211_);
v___x_2213_ = l_Lean_LocalDecl_value(v_a_2210_, v___x_2201_);
lean_dec(v_a_2210_);
v___x_2214_ = l_Lean_collectFVars(v___x_2212_, v___x_2213_);
lean_inc(v_x_2199_);
v___x_2215_ = lean_array_push(v_fst_2181_, v_x_2199_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v_i_2197_);
lean_ctor_set(v___x_2184_, 0, v___x_2215_);
v___x_2217_ = v___x_2184_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_i_2197_);
v___x_2217_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2217_);
lean_ctor_set(v___x_2179_, 0, v___x_2214_);
v___x_2219_ = v___x_2179_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
v_b_2171_ = v___x_2219_;
goto _start;
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_i_2197_);
lean_del_object(v___x_2184_);
lean_dec(v_fst_2181_);
lean_del_object(v___x_2179_);
lean_dec(v_fst_2177_);
v_a_2223_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2209_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2209_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg___boxed(lean_object* v_xs_2233_, lean_object* v_b_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2233_, v_b_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_xs_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0(lean_object* v___x_2240_, lean_object* v_e_2241_, lean_object* v_xs_2242_, lean_object* v_body_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_s_2252_; lean_object* v_i_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2249_ = lean_obj_once(&l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1, &l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1_once, _init_l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__1);
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_getHaveTelescopeInfo_collect___lam__1___closed__2));
v___x_2251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2240_);
lean_ctor_set(v___x_2251_, 2, v___x_2250_);
lean_inc_ref(v_body_2243_);
v_s_2252_ = l_Lean_collectFVars(v___x_2251_, v_body_2243_);
v_i_2253_ = lean_array_get_size(v_xs_2242_);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2250_);
lean_ctor_set(v___x_2254_, 1, v_i_2253_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v_s_2252_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2242_, v___x_2255_, v___y_2244_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2272_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2272_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2272_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_snd_2261_; lean_object* v_fst_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v_snd_2261_ = lean_ctor_get(v_a_2257_, 1);
lean_inc(v_snd_2261_);
lean_dec(v_a_2257_);
v_fst_2262_ = lean_ctor_get(v_snd_2261_, 0);
lean_inc(v_fst_2262_);
lean_dec(v_snd_2261_);
v___x_2263_ = lean_array_get_size(v_fst_2262_);
v___x_2264_ = lean_nat_dec_eq(v___x_2263_, v_i_2253_);
if (v___x_2264_ == 0)
{
uint8_t v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; 
lean_del_object(v___x_2259_);
lean_dec_ref(v_e_2241_);
v___x_2265_ = 1;
v___x_2266_ = l_Array_reverse___redArg(v_fst_2262_);
v___x_2267_ = 1;
v___x_2268_ = l_Lean_Meta_mkLetFVars(v___x_2266_, v_body_2243_, v___x_2265_, v___x_2264_, v___x_2267_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec_ref(v___x_2266_);
return v___x_2268_;
}
else
{
lean_object* v___x_2270_; 
lean_dec(v_fst_2262_);
lean_dec_ref(v_body_2243_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_e_2241_);
v___x_2270_ = v___x_2259_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_e_2241_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_body_2243_);
lean_dec_ref(v_e_2241_);
v_a_2273_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2256_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2256_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___lam__0___boxed(lean_object* v___x_2281_, lean_object* v_e_2282_, lean_object* v_xs_2283_, lean_object* v_body_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Meta_zetaUnused___lam__0(v___x_2281_, v_e_2282_, v_xs_2283_, v_body_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec_ref(v_xs_2283_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused(lean_object* v_e_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v___f_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2297_ = lean_box(1);
lean_inc_ref(v_e_2291_);
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaUnused___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2298_, 0, v___x_2297_);
lean_closure_set(v___f_2298_, 1, v_e_2291_);
v___x_2299_ = 0;
v___x_2300_ = 1;
v___x_2301_ = l_Lean_Meta_letTelescope___at___00Lean_Meta_zetaUnused_spec__1___redArg(v_e_2291_, v___f_2298_, v___x_2299_, v___x_2300_, v___x_2299_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaUnused___boxed(lean_object* v_e_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Meta_zetaUnused(v_e_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(lean_object* v_xs_2309_, lean_object* v_b_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___redArg(v_xs_2309_, v_b_2310_, v___y_2311_, v___y_2313_, v___y_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0___boxed(lean_object* v_xs_2317_, lean_object* v_b_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_zetaUnused_spec__0(v_xs_2317_, v_b_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec_ref(v_xs_2317_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(lean_object* v_u_2329_, lean_object* v_source_2330_, lean_object* v_result_2331_, uint8_t v_keepUnused_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
uint8_t v_modified_2338_; 
v_modified_2338_ = lean_ctor_get_uint8(v_result_2331_, sizeof(void*)*5);
if (v_modified_2338_ == 0)
{
if (v_keepUnused_2332_ == 0)
{
lean_object* v_exprType_2339_; lean_object* v___x_2340_; 
v_exprType_2339_ = lean_ctor_get(v_result_2331_, 1);
lean_inc_ref(v_exprType_2339_);
lean_dec_ref(v_result_2331_);
lean_inc_ref(v_source_2330_);
v___x_2340_ = l_Lean_Meta_zetaUnused(v_source_2330_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2359_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2359_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2359_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint8_t v___x_2345_; 
v___x_2345_ = lean_expr_eqv(v_a_2341_, v_source_2330_);
lean_dec_ref(v_source_2330_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_u_2329_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_mkConst(v___x_2346_, v___x_2348_);
lean_inc(v_a_2341_);
v___x_2350_ = l_Lean_mkAppB(v___x_2349_, v_exprType_2339_, v_a_2341_);
v___x_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_a_2341_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2351_);
v___x_2353_ = v___x_2343_;
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
else
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
lean_dec(v_a_2341_);
lean_dec_ref(v_exprType_2339_);
lean_dec(v_u_2329_);
v___x_2355_ = lean_box(0);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2355_);
v___x_2357_ = v___x_2343_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_exprType_2339_);
lean_dec_ref(v_source_2330_);
lean_dec(v_u_2329_);
v_a_2360_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2340_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2340_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v_result_2331_);
lean_dec_ref(v_source_2330_);
lean_dec(v_u_2329_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
else
{
lean_object* v_expr_2370_; lean_object* v_exprType_2371_; lean_object* v_exprInit_2372_; lean_object* v_exprResult_2373_; lean_object* v_proof_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_proof_2382_; 
v_expr_2370_ = lean_ctor_get(v_result_2331_, 0);
lean_inc_ref(v_expr_2370_);
v_exprType_2371_ = lean_ctor_get(v_result_2331_, 1);
lean_inc_ref_n(v_exprType_2371_, 3);
v_exprInit_2372_ = lean_ctor_get(v_result_2331_, 2);
lean_inc_ref(v_exprInit_2372_);
v_exprResult_2373_ = lean_ctor_get(v_result_2331_, 3);
lean_inc_ref_n(v_exprResult_2373_, 2);
v_proof_2374_ = lean_ctor_get(v_result_2331_, 4);
lean_inc_ref(v_proof_2374_);
lean_dec_ref(v_result_2331_);
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__5));
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_u_2329_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
lean_inc_ref(v___x_2377_);
v___x_2378_ = l_Lean_mkConst(v___x_2375_, v___x_2377_);
lean_inc_ref(v___x_2378_);
v___x_2379_ = l_Lean_mkApp3(v___x_2378_, v_exprType_2371_, v_exprInit_2372_, v_expr_2370_);
v___x_2380_ = l_Lean_Meta_mkExpectedPropHint(v_proof_2374_, v___x_2379_);
lean_inc_ref(v_source_2330_);
v___x_2381_ = l_Lean_mkApp3(v___x_2378_, v_exprType_2371_, v_source_2330_, v_exprResult_2373_);
v_proof_2382_ = l_Lean_Meta_mkExpectedPropHint(v___x_2380_, v___x_2381_);
if (v_keepUnused_2332_ == 0)
{
lean_object* v___x_2383_; 
lean_inc_ref(v_exprResult_2373_);
v___x_2383_ = l_Lean_Meta_zetaUnused(v_exprResult_2373_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2403_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2403_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2403_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
uint8_t v___x_2388_; 
v___x_2388_ = lean_expr_eqv(v_a_2384_, v_exprResult_2373_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___closed__1));
lean_inc_ref(v___x_2377_);
v___x_2390_ = l_Lean_mkConst(v___x_2389_, v___x_2377_);
v___x_2391_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__0___closed__2));
v___x_2392_ = l_Lean_mkConst(v___x_2391_, v___x_2377_);
lean_inc_n(v_a_2384_, 2);
lean_inc_ref(v_exprType_2371_);
v___x_2393_ = l_Lean_mkAppB(v___x_2392_, v_exprType_2371_, v_a_2384_);
v___x_2394_ = l_Lean_mkApp6(v___x_2390_, v_exprType_2371_, v_source_2330_, v_exprResult_2373_, v_a_2384_, v_proof_2382_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_a_2384_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2395_);
v___x_2397_ = v___x_2386_;
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
else
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
lean_dec(v_a_2384_);
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_exprType_2371_);
lean_dec_ref(v_source_2330_);
v___x_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_exprResult_2373_);
lean_ctor_set(v___x_2399_, 1, v_proof_2382_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2399_);
v___x_2401_ = v___x_2386_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v_proof_2382_);
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_exprResult_2373_);
lean_dec_ref(v_exprType_2371_);
lean_dec_ref(v_source_2330_);
v_a_2404_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2383_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2383_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_exprType_2371_);
lean_dec_ref(v_source_2330_);
v___x_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2412_, 0, v_exprResult_2373_);
lean_ctor_set(v___x_2412_, 1, v_proof_2382_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed(lean_object* v_u_2414_, lean_object* v_source_2415_, lean_object* v_result_2416_, lean_object* v_keepUnused_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
uint8_t v_keepUnused_boxed_2423_; lean_object* v_res_2424_; 
v_keepUnused_boxed_2423_ = lean_unbox(v_keepUnused_2417_);
v_res_2424_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult(v_u_2414_, v_source_2415_, v_result_2416_, v_keepUnused_boxed_2423_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0(lean_object* v_level_2425_, lean_object* v_e_2426_, lean_object* v_inst_2427_, uint8_t v_zetaUnusedMode_2428_, uint8_t v___x_2429_, uint8_t v___x_2430_, lean_object* v_r_2431_){
_start:
{
uint8_t v___y_2433_; 
switch(v_zetaUnusedMode_2428_)
{
case 0:
{
v___y_2433_ = v___x_2429_;
goto v___jp_2432_;
}
case 1:
{
v___y_2433_ = v___x_2429_;
goto v___jp_2432_;
}
default: 
{
v___y_2433_ = v___x_2430_;
goto v___jp_2432_;
}
}
v___jp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_box(v___y_2433_);
v___x_2435_ = lean_alloc_closure((void*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_SimpHaveResult_toResult___boxed), 9, 4);
lean_closure_set(v___x_2435_, 0, v_level_2425_);
lean_closure_set(v___x_2435_, 1, v_e_2426_);
lean_closure_set(v___x_2435_, 2, v_r_2431_);
lean_closure_set(v___x_2435_, 3, v___x_2434_);
v___x_2436_ = lean_apply_2(v_inst_2427_, lean_box(0), v___x_2435_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed(lean_object* v_level_2437_, lean_object* v_e_2438_, lean_object* v_inst_2439_, lean_object* v_zetaUnusedMode_2440_, lean_object* v___x_2441_, lean_object* v___x_2442_, lean_object* v_r_2443_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2444_; uint8_t v___x_363__boxed_2445_; uint8_t v___x_364__boxed_2446_; lean_object* v_res_2447_; 
v_zetaUnusedMode_boxed_2444_ = lean_unbox(v_zetaUnusedMode_2440_);
v___x_363__boxed_2445_ = lean_unbox(v___x_2441_);
v___x_364__boxed_2446_ = lean_unbox(v___x_2442_);
v_res_2447_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__0(v_level_2437_, v_e_2438_, v_inst_2439_, v_zetaUnusedMode_boxed_2444_, v___x_363__boxed_2445_, v___x_364__boxed_2446_, v_r_2443_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1(lean_object* v___x_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_info_2453_, lean_object* v_e_2454_, lean_object* v___x_2455_, lean_object* v_toBind_2456_, lean_object* v___f_2457_, lean_object* v_____x_2458_){
_start:
{
lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_fst_2459_ = lean_ctor_get(v_____x_2458_, 0);
lean_inc(v_fst_2459_);
v_snd_2460_ = lean_ctor_get(v_____x_2458_, 1);
lean_inc(v_snd_2460_);
lean_dec_ref(v_____x_2458_);
v___x_2461_ = lean_mk_empty_array_with_capacity(v___x_2448_);
v___x_2462_ = l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg(v_inst_2449_, v_inst_2450_, v_inst_2451_, v_inst_2452_, v_info_2453_, v_fst_2459_, v_snd_2460_, v_e_2454_, v___x_2455_, v___x_2461_);
v___x_2463_ = lean_apply_4(v_toBind_2456_, lean_box(0), lean_box(0), v___x_2462_, v___f_2457_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed(lean_object* v___x_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_info_2469_, lean_object* v_e_2470_, lean_object* v___x_2471_, lean_object* v_toBind_2472_, lean_object* v___f_2473_, lean_object* v_____x_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__1(v___x_2464_, v_inst_2465_, v_inst_2466_, v_inst_2467_, v_inst_2468_, v_info_2469_, v_e_2470_, v___x_2471_, v_toBind_2472_, v___f_2473_, v_____x_2474_);
lean_dec(v___x_2464_);
return v_res_2475_;
}
}
static lean_object* _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2478_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__1));
v___x_2479_ = lean_unsigned_to_nat(2u);
v___x_2480_ = lean_unsigned_to_nat(456u);
v___x_2481_ = ((lean_object*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__0));
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_HaveTelescope_0__Lean_Meta_simpHaveTelescopeAux___redArg___lam__7___closed__3));
v___x_2483_ = l_mkPanicMessageWithDecl(v___x_2482_, v___x_2481_, v___x_2480_, v___x_2479_, v___x_2478_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2(lean_object* v_e_2484_, lean_object* v_inst_2485_, uint8_t v_zetaUnusedMode_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_toBind_2490_, lean_object* v_info_2491_){
_start:
{
lean_object* v_haveInfo_2492_; lean_object* v_level_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_haveInfo_2492_ = lean_ctor_get(v_info_2491_, 0);
v_level_2493_ = lean_ctor_get(v_info_2491_, 5);
v___x_2494_ = lean_array_get_size(v_haveInfo_2492_);
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_nat_dec_eq(v___x_2494_, v___x_2495_);
if (v___x_2496_ == 0)
{
uint8_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___f_2501_; lean_object* v___f_2502_; uint8_t v___y_2504_; 
v___x_2497_ = 1;
v___x_2498_ = lean_box(v_zetaUnusedMode_2486_);
v___x_2499_ = lean_box(v___x_2497_);
v___x_2500_ = lean_box(v___x_2496_);
lean_inc_n(v_inst_2485_, 2);
lean_inc_ref(v_e_2484_);
lean_inc(v_level_2493_);
v___f_2501_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_2501_, 0, v_level_2493_);
lean_closure_set(v___f_2501_, 1, v_e_2484_);
lean_closure_set(v___f_2501_, 2, v_inst_2485_);
lean_closure_set(v___f_2501_, 3, v___x_2498_);
lean_closure_set(v___f_2501_, 4, v___x_2499_);
lean_closure_set(v___f_2501_, 5, v___x_2500_);
lean_inc(v_toBind_2490_);
lean_inc_ref(v_info_2491_);
v___f_2502_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_2502_, 0, v___x_2494_);
lean_closure_set(v___f_2502_, 1, v_inst_2487_);
lean_closure_set(v___f_2502_, 2, v_inst_2485_);
lean_closure_set(v___f_2502_, 3, v_inst_2488_);
lean_closure_set(v___f_2502_, 4, v_inst_2489_);
lean_closure_set(v___f_2502_, 5, v_info_2491_);
lean_closure_set(v___f_2502_, 6, v_e_2484_);
lean_closure_set(v___f_2502_, 7, v___x_2495_);
lean_closure_set(v___f_2502_, 8, v_toBind_2490_);
lean_closure_set(v___f_2502_, 9, v___f_2501_);
switch(v_zetaUnusedMode_2486_)
{
case 0:
{
v___y_2504_ = v___x_2497_;
goto v___jp_2503_;
}
case 2:
{
v___y_2504_ = v___x_2497_;
goto v___jp_2503_;
}
default: 
{
v___y_2504_ = v___x_2496_;
goto v___jp_2503_;
}
}
v___jp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = lean_box(v___y_2504_);
v___x_2506_ = lean_alloc_closure((void*)(l_Lean_Meta_HaveTelescopeInfo_computeFixedUsed___boxed), 7, 2);
lean_closure_set(v___x_2506_, 0, v_info_2491_);
lean_closure_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_apply_2(v_inst_2485_, lean_box(0), v___x_2506_);
v___x_2508_ = lean_apply_4(v_toBind_2490_, lean_box(0), lean_box(0), v___x_2507_, v___f_2502_);
return v___x_2508_;
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec_ref(v_info_2491_);
lean_dec(v_toBind_2490_);
lean_dec_ref(v_inst_2489_);
lean_dec_ref(v_inst_2488_);
lean_dec(v_inst_2485_);
lean_dec_ref(v_e_2484_);
v___x_2509_ = lean_box(0);
v___x_2510_ = l_instInhabitedOfMonad___redArg(v_inst_2487_, v___x_2509_);
v___x_2511_ = lean_obj_once(&l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2, &l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_simpHaveTelescope___redArg___lam__2___closed__2);
v___x_2512_ = l_panic___redArg(v___x_2510_, v___x_2511_);
lean_dec(v___x_2510_);
return v___x_2512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed(lean_object* v_e_2513_, lean_object* v_inst_2514_, lean_object* v_zetaUnusedMode_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_toBind_2519_, lean_object* v_info_2520_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2521_; lean_object* v_res_2522_; 
v_zetaUnusedMode_boxed_2521_ = lean_unbox(v_zetaUnusedMode_2515_);
v_res_2522_ = l_Lean_Meta_simpHaveTelescope___redArg___lam__2(v_e_2513_, v_inst_2514_, v_zetaUnusedMode_boxed_2521_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_toBind_2519_, v_info_2520_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg(lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_inst_2526_, lean_object* v_e_2527_, uint8_t v_zetaUnusedMode_2528_){
_start:
{
lean_object* v_toBind_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v_toBind_2529_ = lean_ctor_get(v_inst_2523_, 1);
lean_inc_n(v_toBind_2529_, 2);
v___x_2530_ = lean_box(v_zetaUnusedMode_2528_);
lean_inc(v_inst_2524_);
lean_inc_ref(v_e_2527_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Meta_simpHaveTelescope___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2531_, 0, v_e_2527_);
lean_closure_set(v___f_2531_, 1, v_inst_2524_);
lean_closure_set(v___f_2531_, 2, v___x_2530_);
lean_closure_set(v___f_2531_, 3, v_inst_2523_);
lean_closure_set(v___f_2531_, 4, v_inst_2525_);
lean_closure_set(v___f_2531_, 5, v_inst_2526_);
lean_closure_set(v___f_2531_, 6, v_toBind_2529_);
v___x_2532_ = lean_alloc_closure((void*)(l_Lean_Meta_getHaveTelescopeInfo___boxed), 6, 1);
lean_closure_set(v___x_2532_, 0, v_e_2527_);
v___x_2533_ = lean_apply_2(v_inst_2524_, lean_box(0), v___x_2532_);
v___x_2534_ = lean_apply_4(v_toBind_2529_, lean_box(0), lean_box(0), v___x_2533_, v___f_2531_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___redArg___boxed(lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_e_2539_, lean_object* v_zetaUnusedMode_2540_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2541_; lean_object* v_res_2542_; 
v_zetaUnusedMode_boxed_2541_ = lean_unbox(v_zetaUnusedMode_2540_);
v_res_2542_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2535_, v_inst_2536_, v_inst_2537_, v_inst_2538_, v_e_2539_, v_zetaUnusedMode_boxed_2541_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope(lean_object* v_m_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_e_2548_, uint8_t v_zetaUnusedMode_2549_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_Meta_simpHaveTelescope___redArg(v_inst_2544_, v_inst_2545_, v_inst_2546_, v_inst_2547_, v_e_2548_, v_zetaUnusedMode_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpHaveTelescope___boxed(lean_object* v_m_2551_, lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_e_2556_, lean_object* v_zetaUnusedMode_2557_){
_start:
{
uint8_t v_zetaUnusedMode_boxed_2558_; lean_object* v_res_2559_; 
v_zetaUnusedMode_boxed_2558_ = lean_unbox(v_zetaUnusedMode_2557_);
v_res_2559_ = l_Lean_Meta_simpHaveTelescope(v_m_2551_, v_inst_2552_, v_inst_2553_, v_inst_2554_, v_inst_2555_, v_e_2556_, v_zetaUnusedMode_boxed_2558_);
return v_res_2559_;
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
