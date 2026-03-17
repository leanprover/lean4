// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Have
// Imports: public import Lean.Meta.Sym.Simp.Lambda import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.ReplaceS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.InferType import Lean.Meta.AppBuilder import Lean.Meta.HaveTelescope import Lean.Util.CollectFVars import Init.Omega import Init.While
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
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_letNondep_x21(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2;
static const lean_array_object l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1;
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: !t.hasLooseBVars\n      "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.toBetaApp.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Sym.Simp.Have"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_Simp_toBetaApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_toBetaApp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.elimAuxApps"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: numArgs == expectedNumArgs\n            "};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.toHave.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.toHave"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congrFun'"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 239, 156, 219, 118, 185, 235, 192)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.simpBetaApp.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpLambda___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpLet___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpLet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3));
v___x_10_ = lean_box(0);
v___x_11_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2, &l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2);
v___x_12_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
lean_ctor_set(v___x_12_, 3, v___x_11_);
lean_ctor_set(v___x_12_, 4, v___x_9_);
lean_ctor_set(v___x_12_, 5, v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4, &l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default;
return v___x_14_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(lean_object* v_k_15_, lean_object* v_t_16_){
_start:
{
if (lean_obj_tag(v_t_16_) == 0)
{
lean_object* v_k_17_; lean_object* v_l_18_; lean_object* v_r_19_; uint8_t v___x_20_; 
v_k_17_ = lean_ctor_get(v_t_16_, 1);
v_l_18_ = lean_ctor_get(v_t_16_, 3);
v_r_19_ = lean_ctor_get(v_t_16_, 4);
v___x_20_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_15_, v_k_17_);
switch(v___x_20_)
{
case 0:
{
v_t_16_ = v_l_18_;
goto _start;
}
case 1:
{
uint8_t v___x_22_; 
v___x_22_ = 1;
return v___x_22_;
}
default: 
{
v_t_16_ = v_r_19_;
goto _start;
}
}
}
else
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg___boxed(lean_object* v_k_25_, lean_object* v_t_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_25_, v_t_26_);
lean_dec(v_t_26_);
lean_dec(v_k_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(lean_object* v_fvarIdToPos_29_, lean_object* v_as_30_, size_t v_i_31_, size_t v_stop_32_, lean_object* v_b_33_){
_start:
{
lean_object* v___y_35_; uint8_t v___x_39_; 
v___x_39_ = lean_usize_dec_eq(v_i_31_, v_stop_32_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_array_uget_borrowed(v_as_30_, v_i_31_);
v___x_41_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v___x_40_, v_fvarIdToPos_29_);
if (v___x_41_ == 0)
{
v___y_35_ = v_b_33_;
goto v___jp_34_;
}
else
{
lean_object* v___x_42_; 
lean_inc(v___x_40_);
v___x_42_ = lean_array_push(v_b_33_, v___x_40_);
v___y_35_ = v___x_42_;
goto v___jp_34_;
}
}
else
{
return v_b_33_;
}
v___jp_34_:
{
size_t v___x_36_; size_t v___x_37_; 
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_add(v_i_31_, v___x_36_);
v_i_31_ = v___x_37_;
v_b_33_ = v___y_35_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3___boxed(lean_object* v_fvarIdToPos_43_, lean_object* v_as_44_, lean_object* v_i_45_, lean_object* v_stop_46_, lean_object* v_b_47_){
_start:
{
size_t v_i_boxed_48_; size_t v_stop_boxed_49_; lean_object* v_res_50_; 
v_i_boxed_48_ = lean_unbox_usize(v_i_45_);
lean_dec(v_i_45_);
v_stop_boxed_49_ = lean_unbox_usize(v_stop_46_);
lean_dec(v_stop_46_);
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_43_, v_as_44_, v_i_boxed_48_, v_stop_boxed_49_, v_b_47_);
lean_dec_ref(v_as_44_);
lean_dec(v_fvarIdToPos_43_);
return v_res_50_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_54_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2));
v___x_55_ = lean_unsigned_to_nat(13u);
v___x_56_ = lean_unsigned_to_nat(227u);
v___x_57_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1));
v___x_58_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0));
v___x_59_ = l_mkPanicMessageWithDecl(v___x_58_, v___x_57_, v___x_56_, v___x_55_, v___x_54_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(lean_object* v_inst_60_, lean_object* v_t_61_, lean_object* v_k_62_){
_start:
{
if (lean_obj_tag(v_t_61_) == 0)
{
lean_object* v_k_63_; lean_object* v_v_64_; lean_object* v_l_65_; lean_object* v_r_66_; uint8_t v___x_67_; 
v_k_63_ = lean_ctor_get(v_t_61_, 1);
v_v_64_ = lean_ctor_get(v_t_61_, 2);
v_l_65_ = lean_ctor_get(v_t_61_, 3);
v_r_66_ = lean_ctor_get(v_t_61_, 4);
v___x_67_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_62_, v_k_63_);
switch(v___x_67_)
{
case 0:
{
v_t_61_ = v_l_65_;
goto _start;
}
case 1:
{
lean_dec(v_inst_60_);
lean_inc(v_v_64_);
return v_v_64_;
}
default: 
{
v_t_61_ = v_r_66_;
goto _start;
}
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3);
v___x_71_ = lean_panic_fn(v_inst_60_, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___boxed(lean_object* v_inst_72_, lean_object* v_t_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v_inst_72_, v_t_73_, v_k_74_);
lean_dec(v_k_74_);
lean_dec(v_t_73_);
return v_res_75_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object* v___x_76_, lean_object* v_fvarIdToPos_77_, lean_object* v_fvarId_u2081_78_, lean_object* v_fvarId_u2082_79_){
_start:
{
lean_object* v_pos_u2081_80_; lean_object* v_pos_u2082_81_; uint8_t v___x_82_; 
lean_inc(v___x_76_);
v_pos_u2081_80_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_76_, v_fvarIdToPos_77_, v_fvarId_u2081_78_);
v_pos_u2082_81_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_76_, v_fvarIdToPos_77_, v_fvarId_u2082_79_);
v___x_82_ = lean_nat_dec_lt(v_pos_u2081_80_, v_pos_u2082_81_);
lean_dec(v_pos_u2082_81_);
lean_dec(v_pos_u2081_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object* v___x_83_, lean_object* v_fvarIdToPos_84_, lean_object* v_fvarId_u2081_85_, lean_object* v_fvarId_u2082_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v___x_83_, v_fvarIdToPos_84_, v_fvarId_u2081_85_, v_fvarId_u2082_86_);
lean_dec(v_fvarId_u2082_86_);
lean_dec(v_fvarId_u2081_85_);
lean_dec(v_fvarIdToPos_84_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object* v_fvarIdToPos_89_, lean_object* v_as_90_, lean_object* v_lo_91_, lean_object* v_hi_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_nat_dec_lt(v_lo_91_, v_hi_92_);
if (v___x_93_ == 0)
{
lean_dec(v_lo_91_);
lean_dec(v_fvarIdToPos_89_);
return v_as_90_;
}
else
{
lean_object* v___x_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v_fst_97_; lean_object* v_snd_98_; uint8_t v___x_99_; 
v___x_94_ = lean_unsigned_to_nat(0u);
lean_inc(v_fvarIdToPos_89_);
v___f_95_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_95_, 0, v___x_94_);
lean_closure_set(v___f_95_, 1, v_fvarIdToPos_89_);
lean_inc(v_lo_91_);
v___x_96_ = l_Array_qpartition___redArg(v_as_90_, v___f_95_, v_lo_91_, v_hi_92_);
v_fst_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_fst_97_);
v_snd_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_snd_98_);
lean_dec_ref(v___x_96_);
v___x_99_ = lean_nat_dec_le(v_hi_92_, v_fst_97_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc(v_fvarIdToPos_89_);
v___x_100_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_89_, v_snd_98_, v_lo_91_, v_fst_97_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_fst_97_, v___x_101_);
lean_dec(v_fst_97_);
v_as_90_ = v___x_100_;
v_lo_91_ = v___x_102_;
goto _start;
}
else
{
lean_dec(v_fst_97_);
lean_dec(v_lo_91_);
lean_dec(v_fvarIdToPos_89_);
return v_snd_98_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object* v_fvarIdToPos_104_, lean_object* v_as_105_, lean_object* v_lo_106_, lean_object* v_hi_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_104_, v_as_105_, v_lo_106_, v_hi_107_);
lean_dec(v_hi_107_);
return v_res_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
v___x_110_ = lean_unsigned_to_nat(16u);
v___x_111_ = lean_mk_array(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_118_ = lean_box(1);
v___x_119_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_121_, lean_object* v_fvarIdToPos_122_){
_start:
{
lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_s_141_; lean_object* v_fvarIds_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3);
v_s_141_ = l_Lean_collectFVars(v___x_140_, v_e_121_);
v_fvarIds_142_ = lean_ctor_get(v_s_141_, 2);
lean_inc_ref(v_fvarIds_142_);
lean_dec_ref(v_s_141_);
v___x_143_ = lean_array_get_size(v_fvarIds_142_);
v___x_144_ = lean_nat_dec_lt(v___x_131_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_139_;
goto v___jp_132_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_145_ == 0)
{
if (v___x_144_ == 0)
{
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_139_;
goto v___jp_132_;
}
else
{
size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_143_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_122_, v_fvarIds_142_, v___x_146_, v___x_147_, v___x_139_);
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_148_;
goto v___jp_132_;
}
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_143_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_122_, v_fvarIds_142_, v___x_149_, v___x_150_, v___x_139_);
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_151_;
goto v___jp_132_;
}
}
v___jp_123_:
{
uint8_t v___x_128_; 
lean_dec(v___y_124_);
v___x_128_ = lean_nat_dec_le(v___y_127_, v___y_125_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec(v___y_125_);
lean_inc(v___y_127_);
v___x_129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_122_, v___y_126_, v___y_127_, v___y_127_);
lean_dec(v___y_127_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_122_, v___y_126_, v___y_127_, v___y_125_);
lean_dec(v___y_125_);
return v___x_130_;
}
}
v___jp_132_:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_array_get_size(v___y_133_);
v___x_135_ = lean_nat_dec_eq(v___x_134_, v___x_131_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_sub(v___x_134_, v___x_136_);
v___x_138_ = lean_nat_dec_le(v___x_131_, v___x_137_);
if (v___x_138_ == 0)
{
lean_inc(v___x_137_);
v___y_124_ = v___x_134_;
v___y_125_ = v___x_137_;
v___y_126_ = v___y_133_;
v___y_127_ = v___x_137_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_134_;
v___y_125_ = v___x_137_;
v___y_126_ = v___y_133_;
v___y_127_ = v___x_131_;
goto v___jp_123_;
}
}
else
{
lean_dec(v_fvarIdToPos_122_);
return v___y_133_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_152_, lean_object* v_k_153_, lean_object* v_t_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_153_, v_t_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_156_, lean_object* v_k_157_, lean_object* v_t_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_156_, v_k_157_, v_t_158_);
lean_dec(v_t_158_);
lean_dec(v_k_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg(lean_object* v_inst_161_, lean_object* v_msg_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_panic_fn(v_inst_161_, v_msg_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object* v_00_u03b4_164_, lean_object* v_inst_165_, lean_object* v_msg_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_panic_fn(v_inst_165_, v_msg_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object* v_00_u03b4_168_, lean_object* v_inst_169_, lean_object* v_t_170_, lean_object* v_k_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v_inst_169_, v_t_170_, v_k_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object* v_00_u03b4_173_, lean_object* v_inst_174_, lean_object* v_t_175_, lean_object* v_k_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_00_u03b4_173_, v_inst_174_, v_t_175_, v_k_176_);
lean_dec(v_k_176_);
lean_dec(v_t_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_178_, lean_object* v_n_179_, lean_object* v_as_180_, lean_object* v_lo_181_, lean_object* v_hi_182_, lean_object* v_w_183_, lean_object* v_hlo_184_, lean_object* v_hhi_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_178_, v_as_180_, v_lo_181_, v_hi_182_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_187_, lean_object* v_n_188_, lean_object* v_as_189_, lean_object* v_lo_190_, lean_object* v_hi_191_, lean_object* v_w_192_, lean_object* v_hlo_193_, lean_object* v_hhi_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_187_, v_n_188_, v_as_189_, v_lo_190_, v_hi_191_, v_w_192_, v_hlo_193_, v_hhi_194_);
lean_dec(v_hi_191_);
lean_dec(v_n_188_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_196_, uint8_t v_bi_197_, lean_object* v_t_198_, lean_object* v_b_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___y_208_; lean_object* v___x_211_; uint8_t v_debug_212_; 
v___x_211_ = lean_st_ref_get(v___y_201_);
v_debug_212_ = lean_ctor_get_uint8(v___x_211_, sizeof(void*)*7);
lean_dec(v___x_211_);
if (v_debug_212_ == 0)
{
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec_ref(v___y_200_);
v___y_208_ = v___y_201_;
goto v___jp_207_;
}
else
{
lean_object* v___x_213_; 
lean_inc(v___y_205_);
lean_inc_ref(v___y_204_);
lean_inc(v___y_203_);
lean_inc_ref(v___y_202_);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
lean_inc_ref(v_t_198_);
v___x_213_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_198_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; 
lean_dec_ref(v___x_213_);
lean_inc(v___y_201_);
lean_inc_ref(v_b_199_);
v___x_214_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_dec_ref(v___x_214_);
v___y_208_ = v___y_201_;
goto v___jp_207_;
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v___y_201_);
lean_dec_ref(v_b_199_);
lean_dec_ref(v_t_198_);
lean_dec(v_x_196_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec_ref(v_b_199_);
lean_dec_ref(v_t_198_);
lean_dec(v_x_196_);
v_a_223_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_213_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_213_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = l_Lean_Expr_forallE___override(v_x_196_, v_t_198_, v_b_199_, v_bi_197_);
v___x_210_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_209_, v___y_208_);
lean_dec(v___y_208_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_231_, lean_object* v_bi_232_, lean_object* v_t_233_, lean_object* v_b_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v_bi_boxed_242_; lean_object* v_res_243_; 
v_bi_boxed_242_ = lean_unbox(v_bi_232_);
v_res_243_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_231_, v_bi_boxed_242_, v_t_233_, v_b_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_247_, lean_object* v_i_248_, lean_object* v_00_u03b2_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_zero_257_; uint8_t v_isZero_258_; 
v_zero_257_ = lean_unsigned_to_nat(0u);
v_isZero_258_ = lean_nat_dec_eq(v_i_248_, v_zero_257_);
if (v_isZero_258_ == 1)
{
lean_object* v___x_259_; 
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_i_248_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_00_u03b2_249_);
return v___x_259_;
}
else
{
lean_object* v_one_260_; lean_object* v_n_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_one_260_ = lean_unsigned_to_nat(1u);
v_n_261_ = lean_nat_sub(v_i_248_, v_one_260_);
lean_dec(v_i_248_);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_263_ = 0;
v___x_264_ = lean_array_fget_borrowed(v_00_u03b1s_247_, v_n_261_);
lean_inc(v_a_255_);
lean_inc_ref(v_a_254_);
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
lean_inc(v_a_251_);
lean_inc_ref(v_a_250_);
lean_inc(v___x_264_);
v___x_265_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_262_, v___x_263_, v___x_264_, v_00_u03b2_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref(v___x_265_);
v_i_248_ = v_n_261_;
v_00_u03b2_249_ = v_a_266_;
goto _start;
}
else
{
lean_dec(v_n_261_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_268_, lean_object* v_i_269_, lean_object* v_00_u03b2_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_268_, v_i_269_, v_00_u03b2_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec_ref(v_00_u03b1s_268_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_279_, lean_object* v_i_280_, lean_object* v_00_u03b2_281_, lean_object* v_h_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_279_, v_i_280_, v_00_u03b2_281_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_291_, lean_object* v_i_292_, lean_object* v_00_u03b2_293_, lean_object* v_h_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_291_, v_i_292_, v_00_u03b2_293_, v_h_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec_ref(v_00_u03b1s_291_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_303_, lean_object* v_00_u03b2_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_array_get_size(v_00_u03b1s_303_);
v___x_313_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_303_, v___x_312_, v_00_u03b2_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_314_, lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_314_, v_00_u03b2_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec_ref(v_00_u03b1s_314_);
return v_res_323_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_toApplicative_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_402_; 
v___x_337_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0);
v___x_338_ = l_ReaderT_instMonad___redArg(v___x_337_);
v_toApplicative_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v___x_338_, 1);
lean_dec(v_unused_403_);
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_402_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_toApplicative_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_402_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_toFunctor_343_; lean_object* v_toSeq_344_; lean_object* v_toSeqLeft_345_; lean_object* v_toSeqRight_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_400_; 
v_toFunctor_343_ = lean_ctor_get(v_toApplicative_339_, 0);
v_toSeq_344_ = lean_ctor_get(v_toApplicative_339_, 2);
v_toSeqLeft_345_ = lean_ctor_get(v_toApplicative_339_, 3);
v_toSeqRight_346_ = lean_ctor_get(v_toApplicative_339_, 4);
v_isSharedCheck_400_ = !lean_is_exclusive(v_toApplicative_339_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_toApplicative_339_, 1);
lean_dec(v_unused_401_);
v___x_348_ = v_toApplicative_339_;
v_isShared_349_ = v_isSharedCheck_400_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_toSeqRight_346_);
lean_inc(v_toSeqLeft_345_);
lean_inc(v_toSeq_344_);
lean_inc(v_toFunctor_343_);
lean_dec(v_toApplicative_339_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_400_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___f_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___x_359_; 
v___f_350_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__1));
v___f_351_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__2));
lean_inc_ref(v_toFunctor_343_);
v___f_352_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_352_, 0, v_toFunctor_343_);
v___f_353_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_353_, 0, v_toFunctor_343_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___f_352_);
lean_ctor_set(v___x_354_, 1, v___f_353_);
v___f_355_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_355_, 0, v_toSeqRight_346_);
v___f_356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_356_, 0, v_toSeqLeft_345_);
v___f_357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_357_, 0, v_toSeq_344_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 4, v___f_355_);
lean_ctor_set(v___x_348_, 3, v___f_356_);
lean_ctor_set(v___x_348_, 2, v___f_357_);
lean_ctor_set(v___x_348_, 1, v___f_350_);
lean_ctor_set(v___x_348_, 0, v___x_354_);
v___x_359_ = v___x_348_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___f_350_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___f_357_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v___f_356_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v___f_355_);
v___x_359_ = v_reuseFailAlloc_399_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___f_351_);
lean_ctor_set(v___x_341_, 0, v___x_359_);
v___x_361_ = v___x_341_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___f_351_);
v___x_361_ = v_reuseFailAlloc_398_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v_toApplicative_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_396_; 
v___x_362_ = l_ReaderT_instMonad___redArg(v___x_361_);
v_toApplicative_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_362_, 1);
lean_dec(v_unused_397_);
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_396_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_toApplicative_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_396_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_toFunctor_367_; lean_object* v_toSeq_368_; lean_object* v_toSeqLeft_369_; lean_object* v_toSeqRight_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_394_; 
v_toFunctor_367_ = lean_ctor_get(v_toApplicative_363_, 0);
v_toSeq_368_ = lean_ctor_get(v_toApplicative_363_, 2);
v_toSeqLeft_369_ = lean_ctor_get(v_toApplicative_363_, 3);
v_toSeqRight_370_ = lean_ctor_get(v_toApplicative_363_, 4);
v_isSharedCheck_394_ = !lean_is_exclusive(v_toApplicative_363_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v_toApplicative_363_, 1);
lean_dec(v_unused_395_);
v___x_372_ = v_toApplicative_363_;
v_isShared_373_ = v_isSharedCheck_394_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_toSeqRight_370_);
lean_inc(v_toSeqLeft_369_);
lean_inc(v_toSeq_368_);
lean_inc(v_toFunctor_367_);
lean_dec(v_toApplicative_363_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_394_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_383_; 
v___f_374_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__3));
v___f_375_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__4));
lean_inc_ref(v_toFunctor_367_);
v___f_376_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_376_, 0, v_toFunctor_367_);
v___f_377_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_377_, 0, v_toFunctor_367_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___f_376_);
lean_ctor_set(v___x_378_, 1, v___f_377_);
v___f_379_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_379_, 0, v_toSeqRight_370_);
v___f_380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_380_, 0, v_toSeqLeft_369_);
v___f_381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_381_, 0, v_toSeq_368_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___f_379_);
lean_ctor_set(v___x_372_, 3, v___f_380_);
lean_ctor_set(v___x_372_, 2, v___f_381_);
lean_ctor_set(v___x_372_, 1, v___f_374_);
lean_ctor_set(v___x_372_, 0, v___x_378_);
v___x_383_ = v___x_372_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___f_374_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v___f_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v___f_380_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v___f_379_);
v___x_383_ = v_reuseFailAlloc_393_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_385_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___f_375_);
lean_ctor_set(v___x_365_, 0, v___x_383_);
v___x_385_ = v___x_365_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___f_375_);
v___x_385_ = v_reuseFailAlloc_392_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___f_389_; lean_object* v___x_5958__overap_390_; lean_object* v___x_391_; 
v___x_386_ = l_ReaderT_instMonad___redArg(v___x_385_);
v___x_387_ = l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default;
v___x_388_ = l_instInhabitedOfMonad___redArg(v___x_386_, v___x_387_);
v___f_389_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_389_, 0, v___x_388_);
v___x_5958__overap_390_ = lean_panic_fn(v___f_389_, v_msg_329_);
v___x_391_ = lean_apply_7(v___x_5958__overap_390_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
return v___x_391_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_413_, lean_object* v_subst_414_, size_t v_sz_415_, size_t v_i_416_, lean_object* v_bs_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_416_, v_sz_415_);
if (v___x_418_ == 0)
{
return v_bs_417_;
}
else
{
lean_object* v_v_419_; lean_object* v___x_420_; lean_object* v_bs_x27_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v_v_419_ = lean_array_uget(v_bs_417_, v_i_416_);
v___x_420_ = lean_unsigned_to_nat(0u);
v_bs_x27_421_ = lean_array_uset(v_bs_417_, v_i_416_, v___x_420_);
v___x_422_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_420_, v_fvarIdToPos_413_, v_v_419_);
lean_dec(v_v_419_);
v___x_423_ = l_Lean_instInhabitedExpr;
v___x_424_ = lean_array_get_borrowed(v___x_423_, v_subst_414_, v___x_422_);
lean_dec(v___x_422_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_416_, v___x_425_);
lean_inc(v___x_424_);
v___x_427_ = lean_array_uset(v_bs_x27_421_, v_i_416_, v___x_424_);
v_i_416_ = v___x_426_;
v_bs_417_ = v___x_427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_429_, lean_object* v_subst_430_, lean_object* v_sz_431_, lean_object* v_i_432_, lean_object* v_bs_433_){
_start:
{
size_t v_sz_boxed_434_; size_t v_i_boxed_435_; lean_object* v_res_436_; 
v_sz_boxed_434_ = lean_unbox_usize(v_sz_431_);
lean_dec(v_sz_431_);
v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_429_, v_subst_430_, v_sz_boxed_434_, v_i_boxed_435_, v_bs_433_);
lean_dec_ref(v_subst_430_);
lean_dec(v_fvarIdToPos_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_437_, size_t v_i_438_, lean_object* v_bs_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_440_ == 0)
{
return v_bs_439_;
}
else
{
lean_object* v_v_441_; lean_object* v___x_442_; lean_object* v_bs_x27_443_; lean_object* v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_v_441_ = lean_array_uget(v_bs_439_, v_i_438_);
v___x_442_ = lean_unsigned_to_nat(0u);
v_bs_x27_443_ = lean_array_uset(v_bs_439_, v_i_438_, v___x_442_);
v___x_444_ = l_Lean_mkFVar(v_v_441_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_438_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_443_, v_i_438_, v___x_444_);
v_i_438_ = v___x_446_;
v_bs_439_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_449_, lean_object* v_i_450_, lean_object* v_bs_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_449_);
lean_dec(v_sz_449_);
v_i_boxed_453_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_452_, v_i_boxed_453_, v_bs_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_apply_8(v_k_455_, v_b_458_, v___y_456_, v___y_457_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, lean_box(0));
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_465_, v___y_466_, v___y_467_, v_b_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_475_, uint8_t v_bi_476_, lean_object* v_type_477_, lean_object* v_k_478_, uint8_t v_kind_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___f_487_; lean_object* v___x_488_; 
v___f_487_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_487_, 0, v_k_478_);
lean_closure_set(v___f_487_, 1, v___y_480_);
lean_closure_set(v___f_487_, 2, v___y_481_);
v___x_488_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_475_, v_bi_476_, v_type_477_, v___f_487_, v_kind_479_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_488_) == 0)
{
return v___x_488_;
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_497_, lean_object* v_bi_498_, lean_object* v_type_499_, lean_object* v_k_500_, lean_object* v_kind_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_bi_boxed_509_; uint8_t v_kind_boxed_510_; lean_object* v_res_511_; 
v_bi_boxed_509_ = lean_unbox(v_bi_498_);
v_kind_boxed_510_ = lean_unbox(v_kind_501_);
v_res_511_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_497_, v_bi_boxed_509_, v_type_499_, v_k_500_, v_kind_boxed_510_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_512_, lean_object* v_type_513_, lean_object* v_k_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = 0;
v___x_523_ = 0;
v___x_524_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_512_, v___x_522_, v_type_513_, v_k_514_, v___x_523_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_525_, lean_object* v_type_526_, lean_object* v_k_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_525_, v_type_526_, v_k_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_536_, lean_object* v_k_537_, lean_object* v_fallback_538_){
_start:
{
if (lean_obj_tag(v_t_536_) == 0)
{
lean_object* v_k_539_; lean_object* v_v_540_; lean_object* v_l_541_; lean_object* v_r_542_; uint8_t v___x_543_; 
v_k_539_ = lean_ctor_get(v_t_536_, 1);
v_v_540_ = lean_ctor_get(v_t_536_, 2);
v_l_541_ = lean_ctor_get(v_t_536_, 3);
v_r_542_ = lean_ctor_get(v_t_536_, 4);
v___x_543_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_537_, v_k_539_);
switch(v___x_543_)
{
case 0:
{
v_t_536_ = v_l_541_;
goto _start;
}
case 1:
{
lean_inc(v_v_540_);
return v_v_540_;
}
default: 
{
v_t_536_ = v_r_542_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_538_);
return v_fallback_538_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_546_, lean_object* v_k_547_, lean_object* v_fallback_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_546_, v_k_547_, v_fallback_548_);
lean_dec(v_fallback_548_);
lean_dec(v_k_547_);
lean_dec(v_t_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_bs_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_554_ == 0)
{
return v_bs_553_;
}
else
{
lean_object* v_v_555_; lean_object* v___x_556_; lean_object* v_bs_x27_557_; lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
v_v_555_ = lean_array_uget(v_bs_553_, v_i_552_);
v___x_556_ = lean_unsigned_to_nat(0u);
v_bs_x27_557_ = lean_array_uset(v_bs_553_, v_i_552_, v___x_556_);
v___x_558_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_550_, v_v_555_, v___x_556_);
lean_dec(v_v_555_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_552_, v___x_559_);
v___x_561_ = lean_array_uset(v_bs_x27_557_, v_i_552_, v___x_558_);
v_i_552_ = v___x_560_;
v_bs_553_ = v___x_561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_563_, lean_object* v_sz_564_, lean_object* v_i_565_, lean_object* v_bs_566_){
_start:
{
size_t v_sz_boxed_567_; size_t v_i_boxed_568_; lean_object* v_res_569_; 
v_sz_boxed_567_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_568_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_563_, v_sz_boxed_567_, v_i_boxed_568_, v_bs_566_);
lean_dec(v_fvarIdToPos_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_579_ = _args[0];
lean_object* v_subst_580_ = _args[1];
lean_object* v_sz_581_ = _args[2];
lean_object* v___x_582_ = _args[3];
lean_object* v_fvarIds_583_ = _args[4];
lean_object* v_x_584_ = _args[5];
lean_object* v_xs_585_ = _args[6];
lean_object* v_xs_x27_586_ = _args[7];
lean_object* v_args_587_ = _args[8];
lean_object* v_a_588_ = _args[9];
lean_object* v_types_589_ = _args[10];
lean_object* v_a_590_ = _args[11];
lean_object* v_varDeps_591_ = _args[12];
lean_object* v_varPos_592_ = _args[13];
lean_object* v_haveExpr_593_ = _args[14];
lean_object* v_body_594_ = _args[15];
lean_object* v_x_x27_595_ = _args[16];
lean_object* v___y_596_ = _args[17];
lean_object* v___y_597_ = _args[18];
lean_object* v___y_598_ = _args[19];
lean_object* v___y_599_ = _args[20];
lean_object* v___y_600_ = _args[21];
lean_object* v___y_601_ = _args[22];
lean_object* v___y_602_ = _args[23];
_start:
{
size_t v_sz_boxed_603_; size_t v___x_7367__boxed_604_; lean_object* v_res_605_; 
v_sz_boxed_603_ = lean_unbox_usize(v_sz_581_);
lean_dec(v_sz_581_);
v___x_7367__boxed_604_ = lean_unbox_usize(v___x_582_);
lean_dec(v___x_582_);
v_res_605_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_579_, v_subst_580_, v_sz_boxed_603_, v___x_7367__boxed_604_, v_fvarIds_583_, v_x_584_, v_xs_585_, v_xs_x27_586_, v_args_587_, v_a_588_, v_types_589_, v_a_590_, v_varDeps_591_, v_varPos_592_, v_haveExpr_593_, v_body_594_, v_x_x27_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_value_606_, lean_object* v_xs_607_, lean_object* v_fvarIdToPos_608_, uint8_t v___x_609_, uint8_t v_nondep_610_, lean_object* v_type_611_, lean_object* v_subst_612_, lean_object* v_xs_x27_613_, lean_object* v_args_614_, lean_object* v_types_615_, lean_object* v_varDeps_616_, lean_object* v_haveExpr_617_, lean_object* v_body_618_, lean_object* v_declName_619_, lean_object* v_x_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_v_628_; lean_object* v_fvarIds_629_; size_t v_sz_630_; size_t v___x_631_; lean_object* v_varPos_632_; lean_object* v_ys_633_; uint8_t v___x_634_; lean_object* v___x_635_; 
v_v_628_ = lean_expr_instantiate_rev(v_value_606_, v_xs_607_);
lean_inc(v_fvarIdToPos_608_);
lean_inc_ref(v_v_628_);
v_fvarIds_629_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_628_, v_fvarIdToPos_608_);
v_sz_630_ = lean_array_size(v_fvarIds_629_);
v___x_631_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_629_);
v_varPos_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_608_, v_sz_630_, v___x_631_, v_fvarIds_629_);
lean_inc_ref(v_fvarIds_629_);
v_ys_633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_630_, v___x_631_, v_fvarIds_629_);
v___x_634_ = 1;
v___x_635_ = l_Lean_Meta_mkLambdaFVars(v_ys_633_, v_v_628_, v___x_609_, v_nondep_610_, v___x_609_, v_nondep_610_, v___x_634_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = l_Lean_Meta_mkForallFVars(v_ys_633_, v_type_611_, v___x_609_, v_nondep_610_, v_nondep_610_, v___x_634_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec_ref(v_ys_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref(v___x_637_);
v___x_639_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_638_, v___y_622_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___f_643_; lean_object* v___x_644_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = lean_box_usize(v_sz_630_);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
lean_inc(v_a_640_);
v___f_643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_643_, 0, v_fvarIdToPos_608_);
lean_closure_set(v___f_643_, 1, v_subst_612_);
lean_closure_set(v___f_643_, 2, v___x_641_);
lean_closure_set(v___f_643_, 3, v___x_642_);
lean_closure_set(v___f_643_, 4, v_fvarIds_629_);
lean_closure_set(v___f_643_, 5, v_x_620_);
lean_closure_set(v___f_643_, 6, v_xs_607_);
lean_closure_set(v___f_643_, 7, v_xs_x27_613_);
lean_closure_set(v___f_643_, 8, v_args_614_);
lean_closure_set(v___f_643_, 9, v_a_636_);
lean_closure_set(v___f_643_, 10, v_types_615_);
lean_closure_set(v___f_643_, 11, v_a_640_);
lean_closure_set(v___f_643_, 12, v_varDeps_616_);
lean_closure_set(v___f_643_, 13, v_varPos_632_);
lean_closure_set(v___f_643_, 14, v_haveExpr_617_);
lean_closure_set(v___f_643_, 15, v_body_618_);
v___x_644_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_619_, v_a_640_, v___f_643_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_644_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_a_636_);
lean_dec_ref(v_varPos_632_);
lean_dec_ref(v_fvarIds_629_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_x_620_);
lean_dec(v_declName_619_);
lean_dec_ref(v_body_618_);
lean_dec_ref(v_haveExpr_617_);
lean_dec_ref(v_varDeps_616_);
lean_dec_ref(v_types_615_);
lean_dec_ref(v_args_614_);
lean_dec_ref(v_xs_x27_613_);
lean_dec_ref(v_subst_612_);
lean_dec(v_fvarIdToPos_608_);
lean_dec_ref(v_xs_607_);
v_a_645_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_639_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_639_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_636_);
lean_dec_ref(v_varPos_632_);
lean_dec_ref(v_fvarIds_629_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_x_620_);
lean_dec(v_declName_619_);
lean_dec_ref(v_body_618_);
lean_dec_ref(v_haveExpr_617_);
lean_dec_ref(v_varDeps_616_);
lean_dec_ref(v_types_615_);
lean_dec_ref(v_args_614_);
lean_dec_ref(v_xs_x27_613_);
lean_dec_ref(v_subst_612_);
lean_dec(v_fvarIdToPos_608_);
lean_dec_ref(v_xs_607_);
v_a_653_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_637_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_637_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_ys_633_);
lean_dec_ref(v_varPos_632_);
lean_dec_ref(v_fvarIds_629_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_x_620_);
lean_dec(v_declName_619_);
lean_dec_ref(v_body_618_);
lean_dec_ref(v_haveExpr_617_);
lean_dec_ref(v_varDeps_616_);
lean_dec_ref(v_types_615_);
lean_dec_ref(v_args_614_);
lean_dec_ref(v_xs_x27_613_);
lean_dec_ref(v_subst_612_);
lean_dec_ref(v_type_611_);
lean_dec(v_fvarIdToPos_608_);
lean_dec_ref(v_xs_607_);
v_a_661_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_635_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_635_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_value_669_ = _args[0];
lean_object* v_xs_670_ = _args[1];
lean_object* v_fvarIdToPos_671_ = _args[2];
lean_object* v___x_672_ = _args[3];
lean_object* v_nondep_673_ = _args[4];
lean_object* v_type_674_ = _args[5];
lean_object* v_subst_675_ = _args[6];
lean_object* v_xs_x27_676_ = _args[7];
lean_object* v_args_677_ = _args[8];
lean_object* v_types_678_ = _args[9];
lean_object* v_varDeps_679_ = _args[10];
lean_object* v_haveExpr_680_ = _args[11];
lean_object* v_body_681_ = _args[12];
lean_object* v_declName_682_ = _args[13];
lean_object* v_x_683_ = _args[14];
lean_object* v___y_684_ = _args[15];
lean_object* v___y_685_ = _args[16];
lean_object* v___y_686_ = _args[17];
lean_object* v___y_687_ = _args[18];
lean_object* v___y_688_ = _args[19];
lean_object* v___y_689_ = _args[20];
lean_object* v___y_690_ = _args[21];
_start:
{
uint8_t v___x_7395__boxed_691_; uint8_t v_nondep_7396__boxed_692_; lean_object* v_res_693_; 
v___x_7395__boxed_691_ = lean_unbox(v___x_672_);
v_nondep_7396__boxed_692_ = lean_unbox(v_nondep_673_);
v_res_693_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_value_669_, v_xs_670_, v_fvarIdToPos_671_, v___x_7395__boxed_691_, v_nondep_7396__boxed_692_, v_type_674_, v_subst_675_, v_xs_x27_676_, v_args_677_, v_types_678_, v_varDeps_679_, v_haveExpr_680_, v_body_681_, v_declName_682_, v_x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec_ref(v_value_669_);
return v_res_693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6));
v___x_698_ = lean_unsigned_to_nat(6u);
v___x_699_ = lean_unsigned_to_nat(168u);
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5));
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_702_ = l_mkPanicMessageWithDecl(v___x_701_, v___x_700_, v___x_699_, v___x_698_, v___x_697_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_703_, lean_object* v_e_704_, lean_object* v_xs_705_, lean_object* v_xs_x27_706_, lean_object* v_args_707_, lean_object* v_subst_708_, lean_object* v_types_709_, lean_object* v_varDeps_710_, lean_object* v_fvarIdToPos_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; 
if (lean_obj_tag(v_e_704_) == 8)
{
uint8_t v_nondep_806_; 
v_nondep_806_ = lean_ctor_get_uint8(v_e_704_, sizeof(void*)*4 + 8);
if (v_nondep_806_ == 1)
{
lean_object* v_declName_807_; lean_object* v_type_808_; lean_object* v_value_809_; lean_object* v_body_810_; uint8_t v___x_811_; 
v_declName_807_ = lean_ctor_get(v_e_704_, 0);
lean_inc(v_declName_807_);
v_type_808_ = lean_ctor_get(v_e_704_, 1);
lean_inc_ref(v_type_808_);
v_value_809_ = lean_ctor_get(v_e_704_, 2);
lean_inc_ref(v_value_809_);
v_body_810_ = lean_ctor_get(v_e_704_, 3);
lean_inc_ref(v_body_810_);
lean_dec_ref(v_e_704_);
v___x_811_ = l_Lean_Expr_hasLooseBVars(v_type_808_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___x_815_; 
v___x_812_ = lean_box(v___x_811_);
v___x_813_ = lean_box(v_nondep_806_);
lean_inc(v_declName_807_);
lean_inc_ref(v_type_808_);
v___f_814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 22, 14);
lean_closure_set(v___f_814_, 0, v_value_809_);
lean_closure_set(v___f_814_, 1, v_xs_705_);
lean_closure_set(v___f_814_, 2, v_fvarIdToPos_711_);
lean_closure_set(v___f_814_, 3, v___x_812_);
lean_closure_set(v___f_814_, 4, v___x_813_);
lean_closure_set(v___f_814_, 5, v_type_808_);
lean_closure_set(v___f_814_, 6, v_subst_708_);
lean_closure_set(v___f_814_, 7, v_xs_x27_706_);
lean_closure_set(v___f_814_, 8, v_args_707_);
lean_closure_set(v___f_814_, 9, v_types_709_);
lean_closure_set(v___f_814_, 10, v_varDeps_710_);
lean_closure_set(v___f_814_, 11, v_haveExpr_703_);
lean_closure_set(v___f_814_, 12, v_body_810_);
lean_closure_set(v___f_814_, 13, v_declName_807_);
v___x_815_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_807_, v_type_808_, v___f_814_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v_body_810_);
lean_dec_ref(v_value_809_);
lean_dec_ref(v_type_808_);
lean_dec(v_declName_807_);
lean_dec(v_fvarIdToPos_711_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_types_709_);
lean_dec_ref(v_subst_708_);
lean_dec_ref(v_args_707_);
lean_dec_ref(v_xs_x27_706_);
lean_dec_ref(v_xs_705_);
lean_dec_ref(v_haveExpr_703_);
v___x_816_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7);
v___x_817_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v___x_816_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_817_;
}
}
else
{
lean_dec(v_fvarIdToPos_711_);
lean_dec_ref(v_xs_705_);
v___y_720_ = v_a_712_;
v___y_721_ = v_a_713_;
v___y_722_ = v_a_714_;
v___y_723_ = v_a_715_;
v___y_724_ = v_a_716_;
v___y_725_ = v_a_717_;
goto v___jp_719_;
}
}
else
{
lean_dec(v_fvarIdToPos_711_);
lean_dec_ref(v_xs_705_);
v___y_720_ = v_a_712_;
v___y_721_ = v_a_713_;
v___y_722_ = v_a_714_;
v___y_723_ = v_a_715_;
v___y_724_ = v_a_716_;
v___y_725_ = v_a_717_;
goto v___jp_719_;
}
v___jp_719_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_array_get_size(v_subst_708_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_728_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_704_, v___x_726_, v___x_727_, v_subst_708_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v_subst_708_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_728_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v_a_729_);
v___x_730_ = l_Lean_Meta_Sym_inferType___redArg(v_a_729_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref(v___x_730_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v_a_731_);
v___x_732_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_731_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref(v___x_732_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v_a_731_);
v___x_734_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_709_, v_a_731_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v_types_709_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_734_);
lean_inc(v___y_721_);
v___x_736_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_706_, v_a_729_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v_xs_x27_706_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_mkAppN(v_a_737_, v_args_707_);
lean_dec_ref(v_args_707_);
v___x_739_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_738_, v___y_721_);
lean_dec(v___y_721_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_757_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_757_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_757_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_757_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_745_ = lean_box(0);
lean_inc(v_a_733_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v_a_733_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
lean_inc_ref(v___x_746_);
v___x_747_ = l_Lean_mkConst(v___x_744_, v___x_746_);
lean_inc(v_a_740_);
lean_inc_ref(v_haveExpr_703_);
lean_inc(v_a_731_);
v___x_748_ = l_Lean_mkApp3(v___x_747_, v_a_731_, v_haveExpr_703_, v_a_740_);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_750_ = l_Lean_mkConst(v___x_749_, v___x_746_);
lean_inc(v_a_731_);
v___x_751_ = l_Lean_mkAppB(v___x_750_, v_a_731_, v_haveExpr_703_);
v___x_752_ = l_Lean_Meta_mkExpectedPropHint(v___x_751_, v___x_748_);
v___x_753_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_753_, 0, v_a_731_);
lean_ctor_set(v___x_753_, 1, v_a_733_);
lean_ctor_set(v___x_753_, 2, v_a_740_);
lean_ctor_set(v___x_753_, 3, v___x_752_);
lean_ctor_set(v___x_753_, 4, v_varDeps_710_);
lean_ctor_set(v___x_753_, 5, v_a_735_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_753_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_735_);
lean_dec(v_a_733_);
lean_dec(v_a_731_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_haveExpr_703_);
v_a_758_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_739_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_739_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_735_);
lean_dec(v_a_733_);
lean_dec(v_a_731_);
lean_dec(v___y_721_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_args_707_);
lean_dec_ref(v_haveExpr_703_);
v_a_766_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_736_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_736_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_a_733_);
lean_dec(v_a_731_);
lean_dec(v_a_729_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_args_707_);
lean_dec_ref(v_xs_x27_706_);
lean_dec_ref(v_haveExpr_703_);
v_a_774_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_734_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_734_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_731_);
lean_dec(v_a_729_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_types_709_);
lean_dec_ref(v_args_707_);
lean_dec_ref(v_xs_x27_706_);
lean_dec_ref(v_haveExpr_703_);
v_a_782_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_732_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_732_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_a_729_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_types_709_);
lean_dec_ref(v_args_707_);
lean_dec_ref(v_xs_x27_706_);
lean_dec_ref(v_haveExpr_703_);
v_a_790_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_730_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_730_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v_varDeps_710_);
lean_dec_ref(v_types_709_);
lean_dec_ref(v_args_707_);
lean_dec_ref(v_xs_x27_706_);
lean_dec_ref(v_haveExpr_703_);
v_a_798_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_728_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_728_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_818_, lean_object* v_subst_819_, size_t v_sz_820_, size_t v___x_821_, lean_object* v_fvarIds_822_, lean_object* v_x_823_, lean_object* v_xs_824_, lean_object* v_xs_x27_825_, lean_object* v_args_826_, lean_object* v_a_827_, lean_object* v_types_828_, lean_object* v_a_829_, lean_object* v_varDeps_830_, lean_object* v_varPos_831_, lean_object* v_haveExpr_832_, lean_object* v_body_833_, lean_object* v_x_x27_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_818_, v_subst_819_, v_sz_820_, v___x_821_, v_fvarIds_822_);
lean_inc_ref(v_x_x27_834_);
v___x_843_ = l_Lean_mkAppN(v_x_x27_834_, v___x_842_);
lean_dec_ref(v___x_842_);
v___x_844_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_843_, v___y_836_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_844_);
v___x_846_ = l_Lean_Expr_fvarId_x21(v_x_823_);
v___x_847_ = lean_array_get_size(v_xs_824_);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v___x_846_, v___x_847_, v_fvarIdToPos_818_);
v___x_849_ = lean_array_push(v_xs_824_, v_x_823_);
v___x_850_ = lean_array_push(v_xs_x27_825_, v_x_x27_834_);
v___x_851_ = lean_array_push(v_args_826_, v_a_827_);
v___x_852_ = lean_array_push(v_subst_819_, v_a_845_);
v___x_853_ = lean_array_push(v_types_828_, v_a_829_);
v___x_854_ = lean_array_push(v_varDeps_830_, v_varPos_831_);
v___x_855_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_832_, v_body_833_, v___x_849_, v___x_850_, v___x_851_, v___x_852_, v___x_853_, v___x_854_, v___x_848_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_855_;
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v_x_x27_834_);
lean_dec_ref(v_body_833_);
lean_dec_ref(v_haveExpr_832_);
lean_dec_ref(v_varPos_831_);
lean_dec_ref(v_varDeps_830_);
lean_dec_ref(v_a_829_);
lean_dec_ref(v_types_828_);
lean_dec_ref(v_a_827_);
lean_dec_ref(v_args_826_);
lean_dec_ref(v_xs_x27_825_);
lean_dec_ref(v_xs_824_);
lean_dec_ref(v_x_823_);
lean_dec_ref(v_subst_819_);
lean_dec(v_fvarIdToPos_818_);
v_a_856_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_844_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_844_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_864_, lean_object* v_e_865_, lean_object* v_xs_866_, lean_object* v_xs_x27_867_, lean_object* v_args_868_, lean_object* v_subst_869_, lean_object* v_types_870_, lean_object* v_varDeps_871_, lean_object* v_fvarIdToPos_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_864_, v_e_865_, v_xs_866_, v_xs_x27_867_, v_args_868_, v_subst_869_, v_types_870_, v_varDeps_871_, v_fvarIdToPos_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_881_, lean_object* v_t_882_, lean_object* v_k_883_, lean_object* v_fallback_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_882_, v_k_883_, v_fallback_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_886_, lean_object* v_t_887_, lean_object* v_k_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_886_, v_t_887_, v_k_888_, v_fallback_889_);
lean_dec(v_fallback_889_);
lean_dec(v_k_888_);
lean_dec(v_t_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_891_, lean_object* v_name_892_, uint8_t v_bi_893_, lean_object* v_type_894_, lean_object* v_k_895_, uint8_t v_kind_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_892_, v_bi_893_, v_type_894_, v_k_895_, v_kind_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_905_, lean_object* v_name_906_, lean_object* v_bi_907_, lean_object* v_type_908_, lean_object* v_k_909_, lean_object* v_kind_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
uint8_t v_bi_boxed_918_; uint8_t v_kind_boxed_919_; lean_object* v_res_920_; 
v_bi_boxed_918_ = lean_unbox(v_bi_907_);
v_kind_boxed_919_ = lean_unbox(v_kind_910_);
v_res_920_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_905_, v_name_906_, v_bi_boxed_918_, v_type_908_, v_k_909_, v_kind_boxed_919_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_921_, lean_object* v_name_922_, lean_object* v_type_923_, lean_object* v_k_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_922_, v_type_923_, v_k_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_933_, lean_object* v_name_934_, lean_object* v_type_935_, lean_object* v_k_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_933_, v_name_934_, v_type_935_, v_k_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_956_ = lean_box(1);
lean_inc_ref(v_haveExpr_947_);
v___x_957_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_947_, v_haveExpr_947_, v___x_955_, v___x_955_, v___x_955_, v___x_955_, v___x_955_, v___x_955_, v___x_956_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_967_, lean_object* v_n_968_){
_start:
{
lean_object* v_zero_969_; uint8_t v_isZero_970_; 
v_zero_969_ = lean_unsigned_to_nat(0u);
v_isZero_970_ = lean_nat_dec_eq(v_n_968_, v_zero_969_);
if (v_isZero_970_ == 1)
{
lean_dec(v_n_968_);
return v_type_967_;
}
else
{
lean_object* v_one_971_; lean_object* v_n_972_; lean_object* v___x_973_; 
v_one_971_ = lean_unsigned_to_nat(1u);
v_n_972_ = lean_nat_sub(v_n_968_, v_one_971_);
lean_dec(v_n_968_);
v___x_973_ = l_Lean_Expr_bindingBody_x21(v_type_967_);
lean_dec_ref(v_type_967_);
v_type_967_ = v___x_973_;
v_n_968_ = v_n_972_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0(void){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_975_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_00_u03b2_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object* v_idx_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = l_Lean_Expr_bvar___override(v_idx_980_);
v___x_983_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_982_, v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_idx_984_, uint8_t v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v_idx_984_, v___y_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_idx_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___y_21817__boxed_991_; lean_object* v_res_992_; 
v___y_21817__boxed_991_ = lean_unbox(v___y_989_);
v_res_992_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_idx_988_, v___y_21817__boxed_991_, v___y_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_msg_1000_, uint8_t v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___x_1737__overap_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___f_1003_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_1004_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_1005_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_1006_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1007_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1008_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1009_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___f_1003_);
lean_ctor_set(v___x_1010_, 1, v___f_1004_);
v___x_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___f_1005_);
lean_ctor_set(v___x_1011_, 2, v___f_1006_);
lean_ctor_set(v___x_1011_, 3, v___f_1007_);
lean_ctor_set(v___x_1011_, 4, v___f_1008_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___f_1009_);
lean_inc_ref(v___x_1012_);
v___f_1013_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1013_, 0, v___x_1012_);
lean_inc_ref(v___x_1012_);
v___f_1014_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1014_, 0, v___x_1012_);
lean_inc_ref(v___x_1012_);
v___f_1015_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1015_, 0, v___x_1012_);
lean_inc_ref(v___x_1012_);
v___f_1016_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1016_, 0, v___x_1012_);
lean_inc_ref(v___x_1012_);
v___x_1017_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1017_, 0, lean_box(0));
lean_closure_set(v___x_1017_, 1, lean_box(0));
lean_closure_set(v___x_1017_, 2, v___x_1012_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___f_1013_);
lean_inc_ref(v___x_1012_);
v___x_1019_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1019_, 0, lean_box(0));
lean_closure_set(v___x_1019_, 1, lean_box(0));
lean_closure_set(v___x_1019_, 2, v___x_1012_);
v___x_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
lean_ctor_set(v___x_1020_, 2, v___f_1014_);
lean_ctor_set(v___x_1020_, 3, v___f_1015_);
lean_ctor_set(v___x_1020_, 4, v___f_1016_);
v___x_1021_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1021_, 0, lean_box(0));
lean_closure_set(v___x_1021_, 1, lean_box(0));
lean_closure_set(v___x_1021_, 2, v___x_1012_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_box(0);
v___x_1024_ = l_instInhabitedOfMonad___redArg(v___x_1022_, v___x_1023_);
v___f_1025_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1025_, 0, v___x_1024_);
v___x_1737__overap_1026_ = lean_panic_fn(v___f_1025_, v_msg_1000_);
v___x_1027_ = lean_box(v___y_1001_);
v___x_1028_ = lean_apply_2(v___x_1737__overap_1026_, v___x_1027_, v___y_1002_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
uint8_t v___y_21839__boxed_1032_; lean_object* v_res_1033_; 
v___y_21839__boxed_1032_ = lean_unbox(v___y_1030_);
v_res_1033_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_msg_1029_, v___y_21839__boxed_1032_, v___y_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object* v_structName_1034_, lean_object* v_idx_1035_, lean_object* v_struct_1036_, lean_object* v___y_1037_, uint8_t v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___y_1041_; lean_object* v___y_1042_; 
if (v___y_1038_ == 0)
{
v___y_1041_ = v___y_1037_;
v___y_1042_ = v___y_1039_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1055_; lean_object* v_snd_1056_; 
lean_inc_ref(v_struct_1036_);
v___x_1055_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1036_, v___y_1038_, v___y_1039_);
v_snd_1056_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1055_);
v___y_1041_ = v___y_1037_;
v___y_1042_ = v_snd_1056_;
goto v___jp_1040_;
}
v___jp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v___x_1043_ = l_Lean_Expr_proj___override(v_structName_1034_, v_idx_1035_, v_struct_1036_);
v___x_1044_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1043_, v___y_1042_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___y_1041_);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_fst_1045_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___y_1041_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_snd_1046_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object* v_structName_1057_, lean_object* v_idx_1058_, lean_object* v_struct_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___y_21903__boxed_1063_; lean_object* v_res_1064_; 
v___y_21903__boxed_1063_ = lean_unbox(v___y_1061_);
v_res_1064_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_structName_1057_, v_idx_1058_, v_struct_1059_, v___y_1060_, v___y_21903__boxed_1063_, v___y_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object* v_x_1065_, uint8_t v_bi_1066_, lean_object* v_t_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, uint8_t v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___y_1073_; lean_object* v___y_1074_; 
if (v___y_1070_ == 0)
{
v___y_1073_ = v___y_1069_;
v___y_1074_ = v___y_1071_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1087_; lean_object* v_snd_1088_; lean_object* v___x_1089_; lean_object* v_snd_1090_; 
lean_inc_ref(v_t_1067_);
v___x_1087_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1067_, v___y_1070_, v___y_1071_);
v_snd_1088_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_snd_1088_);
lean_dec_ref(v___x_1087_);
lean_inc_ref(v_b_1068_);
v___x_1089_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1068_, v___y_1070_, v_snd_1088_);
v_snd_1090_ = lean_ctor_get(v___x_1089_, 1);
lean_inc(v_snd_1090_);
lean_dec_ref(v___x_1089_);
v___y_1073_ = v___y_1069_;
v___y_1074_ = v_snd_1090_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v___x_1075_ = l_Lean_Expr_lam___override(v_x_1065_, v_t_1067_, v_b_1068_, v_bi_1066_);
v___x_1076_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1075_, v___y_1074_);
v_fst_1077_ = lean_ctor_get(v___x_1076_, 0);
v_snd_1078_ = lean_ctor_get(v___x_1076_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v___x_1076_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_inc(v_fst_1077_);
lean_dec(v___x_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___y_1073_);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___y_1073_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_snd_1078_);
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object* v_x_1091_, lean_object* v_bi_1092_, lean_object* v_t_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_bi_boxed_1098_; uint8_t v___y_21947__boxed_1099_; lean_object* v_res_1100_; 
v_bi_boxed_1098_ = lean_unbox(v_bi_1092_);
v___y_21947__boxed_1099_ = lean_unbox(v___y_1096_);
v_res_1100_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_x_1091_, v_bi_boxed_1098_, v_t_1093_, v_b_1094_, v___y_1095_, v___y_21947__boxed_1099_, v___y_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object* v_msg_1101_, lean_object* v___y_1102_, uint8_t v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_21475__overap_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___f_1105_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_1106_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_1107_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_1108_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1109_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1110_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1111_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___f_1105_);
lean_ctor_set(v___x_1112_, 1, v___f_1106_);
v___x_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___f_1107_);
lean_ctor_set(v___x_1113_, 2, v___f_1108_);
lean_ctor_set(v___x_1113_, 3, v___f_1109_);
lean_ctor_set(v___x_1113_, 4, v___f_1110_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___f_1111_);
lean_inc_ref(v___x_1114_);
v___f_1115_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1115_, 0, v___x_1114_);
lean_inc_ref(v___x_1114_);
v___f_1116_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1116_, 0, v___x_1114_);
lean_inc_ref(v___x_1114_);
v___f_1117_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1117_, 0, v___x_1114_);
lean_inc_ref(v___x_1114_);
v___f_1118_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1118_, 0, v___x_1114_);
lean_inc_ref(v___x_1114_);
v___x_1119_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1119_, 0, lean_box(0));
lean_closure_set(v___x_1119_, 1, lean_box(0));
lean_closure_set(v___x_1119_, 2, v___x_1114_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___f_1115_);
lean_inc_ref(v___x_1114_);
v___x_1121_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1121_, 0, lean_box(0));
lean_closure_set(v___x_1121_, 1, lean_box(0));
lean_closure_set(v___x_1121_, 2, v___x_1114_);
v___x_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
lean_ctor_set(v___x_1122_, 2, v___f_1116_);
lean_ctor_set(v___x_1122_, 3, v___f_1117_);
lean_ctor_set(v___x_1122_, 4, v___f_1118_);
v___x_1123_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1123_, 0, lean_box(0));
lean_closure_set(v___x_1123_, 1, lean_box(0));
lean_closure_set(v___x_1123_, 2, v___x_1114_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_ReaderT_instMonad___redArg(v___x_1124_);
lean_inc_ref(v___x_1125_);
v___f_1126_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1126_, 0, v___x_1125_);
lean_inc_ref(v___x_1125_);
v___f_1127_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1127_, 0, v___x_1125_);
lean_inc_ref(v___x_1125_);
v___f_1128_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1128_, 0, v___x_1125_);
lean_inc_ref(v___x_1125_);
v___f_1129_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1129_, 0, v___x_1125_);
lean_inc_ref(v___x_1125_);
v___x_1130_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1130_, 0, lean_box(0));
lean_closure_set(v___x_1130_, 1, lean_box(0));
lean_closure_set(v___x_1130_, 2, v___x_1125_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___f_1126_);
lean_inc_ref(v___x_1125_);
v___x_1132_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1132_, 0, lean_box(0));
lean_closure_set(v___x_1132_, 1, lean_box(0));
lean_closure_set(v___x_1132_, 2, v___x_1125_);
v___x_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
lean_ctor_set(v___x_1133_, 2, v___f_1127_);
lean_ctor_set(v___x_1133_, 3, v___f_1128_);
lean_ctor_set(v___x_1133_, 4, v___f_1129_);
v___x_1134_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1134_, 0, lean_box(0));
lean_closure_set(v___x_1134_, 1, lean_box(0));
lean_closure_set(v___x_1134_, 2, v___x_1125_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_instInhabitedExpr;
v___x_1137_ = l_instInhabitedOfMonad___redArg(v___x_1135_, v___x_1136_);
v___x_21475__overap_1138_ = lean_panic_fn(v___x_1137_, v_msg_1101_);
v___x_1139_ = lean_box(v___y_1103_);
v___x_1140_ = lean_apply_3(v___x_21475__overap_1138_, v___y_1102_, v___x_1139_, v___y_1104_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v___y_22003__boxed_1145_; lean_object* v_res_1146_; 
v___y_22003__boxed_1145_ = lean_unbox(v___y_1143_);
v_res_1146_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v_msg_1141_, v___y_1142_, v___y_22003__boxed_1145_, v___y_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object* v_f_1147_, lean_object* v_a_1148_, lean_object* v___y_1149_, uint8_t v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___y_1153_; lean_object* v___y_1154_; 
if (v___y_1150_ == 0)
{
v___y_1153_ = v___y_1149_;
v___y_1154_ = v___y_1151_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1167_; lean_object* v_snd_1168_; lean_object* v___x_1169_; lean_object* v_snd_1170_; 
lean_inc_ref(v_f_1147_);
v___x_1167_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1147_, v___y_1150_, v___y_1151_);
v_snd_1168_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_snd_1168_);
lean_dec_ref(v___x_1167_);
lean_inc_ref(v_a_1148_);
v___x_1169_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1148_, v___y_1150_, v_snd_1168_);
v_snd_1170_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_snd_1170_);
lean_dec_ref(v___x_1169_);
v___y_1153_ = v___y_1149_;
v___y_1154_ = v_snd_1170_;
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
v___x_1155_ = l_Lean_Expr_app___override(v_f_1147_, v_a_1148_);
v___x_1156_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1155_, v___y_1154_);
v_fst_1157_ = lean_ctor_get(v___x_1156_, 0);
v_snd_1158_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1160_ = v___x_1156_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_inc(v_fst_1157_);
lean_dec(v___x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___y_1153_);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_fst_1157_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___y_1153_);
v___x_1163_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v_snd_1158_);
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object* v_f_1171_, lean_object* v_a_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v___y_22082__boxed_1176_; lean_object* v_res_1177_; 
v___y_22082__boxed_1176_ = lean_unbox(v___y_1174_);
v_res_1177_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_f_1171_, v_a_1172_, v___y_1173_, v___y_22082__boxed_1176_, v___y_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object* v_x_1178_, uint8_t v_bi_1179_, lean_object* v_t_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, uint8_t v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___y_1186_; lean_object* v___y_1187_; 
if (v___y_1183_ == 0)
{
v___y_1186_ = v___y_1182_;
v___y_1187_ = v___y_1184_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; lean_object* v_snd_1203_; 
lean_inc_ref(v_t_1180_);
v___x_1200_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1180_, v___y_1183_, v___y_1184_);
v_snd_1201_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_snd_1201_);
lean_dec_ref(v___x_1200_);
lean_inc_ref(v_b_1181_);
v___x_1202_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1181_, v___y_1183_, v_snd_1201_);
v_snd_1203_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_snd_1203_);
lean_dec_ref(v___x_1202_);
v___y_1186_ = v___y_1182_;
v___y_1187_ = v_snd_1203_;
goto v___jp_1185_;
}
v___jp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_fst_1190_; lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v___x_1188_ = l_Lean_Expr_forallE___override(v_x_1178_, v_t_1180_, v_b_1181_, v_bi_1179_);
v___x_1189_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1188_, v___y_1187_);
v_fst_1190_ = lean_ctor_get(v___x_1189_, 0);
v_snd_1191_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v___x_1189_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_inc(v_fst_1190_);
lean_dec(v___x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___y_1186_);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_fst_1190_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___y_1186_);
v___x_1196_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v_snd_1191_);
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object* v_x_1204_, lean_object* v_bi_1205_, lean_object* v_t_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_bi_boxed_1211_; uint8_t v___y_22131__boxed_1212_; lean_object* v_res_1213_; 
v_bi_boxed_1211_ = lean_unbox(v_bi_1205_);
v___y_22131__boxed_1212_ = lean_unbox(v___y_1209_);
v_res_1213_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_x_1204_, v_bi_boxed_1211_, v_t_1206_, v_b_1207_, v___y_1208_, v___y_22131__boxed_1212_, v___y_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object* v_x_1214_, lean_object* v_t_1215_, lean_object* v_v_1216_, lean_object* v_b_1217_, uint8_t v_nondep_1218_, lean_object* v___y_1219_, uint8_t v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___y_1223_; lean_object* v___y_1224_; 
if (v___y_1220_ == 0)
{
v___y_1223_ = v___y_1219_;
v___y_1224_ = v___y_1221_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1237_; lean_object* v_snd_1238_; lean_object* v___x_1239_; lean_object* v_snd_1240_; lean_object* v___x_1241_; lean_object* v_snd_1242_; 
lean_inc_ref(v_t_1215_);
v___x_1237_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1215_, v___y_1220_, v___y_1221_);
v_snd_1238_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_snd_1238_);
lean_dec_ref(v___x_1237_);
lean_inc_ref(v_v_1216_);
v___x_1239_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1216_, v___y_1220_, v_snd_1238_);
v_snd_1240_ = lean_ctor_get(v___x_1239_, 1);
lean_inc(v_snd_1240_);
lean_dec_ref(v___x_1239_);
lean_inc_ref(v_b_1217_);
v___x_1241_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1217_, v___y_1220_, v_snd_1240_);
v_snd_1242_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_snd_1242_);
lean_dec_ref(v___x_1241_);
v___y_1223_ = v___y_1219_;
v___y_1224_ = v_snd_1242_;
goto v___jp_1222_;
}
v___jp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1236_; 
v___x_1225_ = l_Lean_Expr_letE___override(v_x_1214_, v_t_1215_, v_v_1216_, v_b_1217_, v_nondep_1218_);
v___x_1226_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1225_, v___y_1224_);
v_fst_1227_ = lean_ctor_get(v___x_1226_, 0);
v_snd_1228_ = lean_ctor_get(v___x_1226_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1230_ = v___x_1226_;
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1228_);
lean_inc(v_fst_1227_);
lean_dec(v___x_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___y_1223_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fst_1227_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___y_1223_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_snd_1228_);
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object* v_x_1243_, lean_object* v_t_1244_, lean_object* v_v_1245_, lean_object* v_b_1246_, lean_object* v_nondep_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v_nondep_boxed_1251_; uint8_t v___y_22180__boxed_1252_; lean_object* v_res_1253_; 
v_nondep_boxed_1251_ = lean_unbox(v_nondep_1247_);
v___y_22180__boxed_1252_ = lean_unbox(v___y_1249_);
v_res_1253_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_x_1243_, v_t_1244_, v_v_1245_, v_b_1246_, v_nondep_boxed_1251_, v___y_1248_, v___y_22180__boxed_1252_, v___y_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_a_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_box(0);
return v___x_1256_;
}
else
{
lean_object* v_key_1257_; lean_object* v_value_1258_; lean_object* v_tail_1259_; uint8_t v___y_1261_; lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v_fst_1266_; lean_object* v_snd_1267_; uint8_t v___x_1268_; 
v_key_1257_ = lean_ctor_get(v_x_1255_, 0);
v_value_1258_ = lean_ctor_get(v_x_1255_, 1);
v_tail_1259_ = lean_ctor_get(v_x_1255_, 2);
v_fst_1264_ = lean_ctor_get(v_key_1257_, 0);
v_snd_1265_ = lean_ctor_get(v_key_1257_, 1);
v_fst_1266_ = lean_ctor_get(v_a_1254_, 0);
v_snd_1267_ = lean_ctor_get(v_a_1254_, 1);
v___x_1268_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1264_, v_fst_1266_);
if (v___x_1268_ == 0)
{
v___y_1261_ = v___x_1268_;
goto v___jp_1260_;
}
else
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_eq(v_snd_1265_, v_snd_1267_);
v___y_1261_ = v___x_1269_;
goto v___jp_1260_;
}
v___jp_1260_:
{
if (v___y_1261_ == 0)
{
v_x_1255_ = v_tail_1259_;
goto _start;
}
else
{
lean_object* v___x_1263_; 
lean_inc(v_value_1258_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_value_1258_);
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object* v_a_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1270_, v_x_1271_);
lean_dec(v_x_1271_);
lean_dec_ref(v_a_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object* v_m_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_buckets_1275_; lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1278_; uint64_t v___x_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; uint64_t v_fold_1284_; uint64_t v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_buckets_1275_ = lean_ctor_get(v_m_1273_, 1);
v_fst_1276_ = lean_ctor_get(v_a_1274_, 0);
v_snd_1277_ = lean_ctor_get(v_a_1274_, 1);
v___x_1278_ = lean_array_get_size(v_buckets_1275_);
v___x_1279_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1276_);
v___x_1280_ = lean_uint64_of_nat(v_snd_1277_);
v___x_1281_ = lean_uint64_mix_hash(v___x_1279_, v___x_1280_);
v___x_1282_ = 32ULL;
v___x_1283_ = lean_uint64_shift_right(v___x_1281_, v___x_1282_);
v_fold_1284_ = lean_uint64_xor(v___x_1281_, v___x_1283_);
v___x_1285_ = 16ULL;
v___x_1286_ = lean_uint64_shift_right(v_fold_1284_, v___x_1285_);
v___x_1287_ = lean_uint64_xor(v_fold_1284_, v___x_1286_);
v___x_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = lean_usize_of_nat(v___x_1278_);
v___x_1290_ = ((size_t)1ULL);
v___x_1291_ = lean_usize_sub(v___x_1289_, v___x_1290_);
v___x_1292_ = lean_usize_land(v___x_1288_, v___x_1291_);
v___x_1293_ = lean_array_uget_borrowed(v_buckets_1275_, v___x_1292_);
v___x_1294_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1274_, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1295_, v_a_1296_);
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_m_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object* v_d_1298_, lean_object* v_e_1299_, lean_object* v___y_1300_, uint8_t v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___y_1304_; lean_object* v___y_1305_; 
if (v___y_1301_ == 0)
{
v___y_1304_ = v___y_1300_;
v___y_1305_ = v___y_1302_;
goto v___jp_1303_;
}
else
{
lean_object* v___x_1318_; lean_object* v_snd_1319_; 
lean_inc_ref(v_e_1299_);
v___x_1318_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1299_, v___y_1301_, v___y_1302_);
v_snd_1319_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_snd_1319_);
lean_dec_ref(v___x_1318_);
v___y_1304_ = v___y_1300_;
v___y_1305_ = v_snd_1319_;
goto v___jp_1303_;
}
v___jp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v___x_1306_ = l_Lean_Expr_mdata___override(v_d_1298_, v_e_1299_);
v___x_1307_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1306_, v___y_1305_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
v_snd_1309_ = lean_ctor_get(v___x_1307_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v___x_1307_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_snd_1309_);
lean_inc(v_fst_1308_);
lean_dec(v___x_1307_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v___y_1304_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_fst_1308_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___y_1304_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_snd_1309_);
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object* v_d_1320_, lean_object* v_e_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v___y_22303__boxed_1325_; lean_object* v_res_1326_; 
v___y_22303__boxed_1325_ = lean_unbox(v___y_1323_);
v_res_1326_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_d_1320_, v_e_1321_, v___y_1322_, v___y_22303__boxed_1325_, v___y_1324_);
return v_res_1326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Array_instInhabited(lean_box(0));
return v___x_1327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2));
v___x_1331_ = lean_unsigned_to_nat(12u);
v___x_1332_ = lean_unsigned_to_nat(234u);
v___x_1333_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1));
v___x_1334_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1335_ = l_mkPanicMessageWithDecl(v___x_1334_, v___x_1333_, v___x_1332_, v___x_1331_, v___x_1330_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1340_ = lean_unsigned_to_nat(67u);
v___x_1341_ = lean_unsigned_to_nat(35u);
v___x_1342_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1));
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0));
v___x_1344_ = l_mkPanicMessageWithDecl(v___x_1343_, v___x_1342_, v___x_1341_, v___x_1340_, v___x_1339_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_n_1345_, lean_object* v_varDeps_1346_, lean_object* v_xs_1347_, lean_object* v_e_1348_, lean_object* v_offset_1349_, lean_object* v_a_1350_, uint8_t v_a_1351_, lean_object* v_a_1352_){
_start:
{
switch(lean_obj_tag(v_e_1348_))
{
case 5:
{
lean_object* v_fn_1353_; lean_object* v_arg_1354_; lean_object* v___x_1355_; lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1383_; 
v_fn_1353_ = lean_ctor_get(v_e_1348_, 0);
v_arg_1354_ = lean_ctor_get(v_e_1348_, 1);
lean_inc(v_offset_1349_);
lean_inc_ref(v_fn_1353_);
v___x_1355_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_fn_1353_, v_offset_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
v_fst_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_fst_1356_);
v_snd_1357_ = lean_ctor_get(v___x_1355_, 1);
lean_inc(v_snd_1357_);
lean_dec_ref(v___x_1355_);
v_fst_1358_ = lean_ctor_get(v_fst_1356_, 0);
lean_inc(v_fst_1358_);
v_snd_1359_ = lean_ctor_get(v_fst_1356_, 1);
lean_inc(v_snd_1359_);
lean_dec(v_fst_1356_);
lean_inc_ref(v_arg_1354_);
v___x_1360_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_arg_1354_, v_offset_1349_, v_snd_1359_, v_a_1351_, v_snd_1357_);
v_fst_1361_ = lean_ctor_get(v___x_1360_, 0);
v_snd_1362_ = lean_ctor_get(v___x_1360_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1364_ = v___x_1360_;
v_isShared_1365_ = v_isSharedCheck_1383_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snd_1362_);
lean_inc(v_fst_1361_);
lean_dec(v___x_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1383_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1382_; 
v_fst_1366_ = lean_ctor_get(v_fst_1361_, 0);
v_snd_1367_ = lean_ctor_get(v_fst_1361_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_fst_1361_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1369_ = v_fst_1361_;
v_isShared_1370_ = v_isSharedCheck_1382_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_fst_1361_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1382_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v___y_1372_; uint8_t v___x_1380_; 
v___x_1380_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1353_, v_fst_1358_);
if (v___x_1380_ == 0)
{
v___y_1372_ = v___x_1380_;
goto v___jp_1371_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1354_, v_fst_1366_);
v___y_1372_ = v___x_1381_;
goto v___jp_1371_;
}
v___jp_1371_:
{
if (v___y_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_del_object(v___x_1369_);
lean_del_object(v___x_1364_);
lean_dec_ref(v_e_1348_);
v___x_1373_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_fst_1358_, v_fst_1366_, v_snd_1367_, v_a_1351_, v_snd_1362_);
return v___x_1373_;
}
else
{
lean_object* v___x_1375_; 
lean_dec(v_fst_1366_);
lean_dec(v_fst_1358_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v_e_1348_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_e_1348_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_snd_1367_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1375_);
v___x_1377_ = v___x_1364_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_snd_1362_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_1384_; lean_object* v_binderType_1385_; lean_object* v_body_1386_; uint8_t v_binderInfo_1387_; lean_object* v___x_1388_; lean_object* v_fst_1389_; lean_object* v_snd_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1418_; 
v_binderName_1384_ = lean_ctor_get(v_e_1348_, 0);
v_binderType_1385_ = lean_ctor_get(v_e_1348_, 1);
v_body_1386_ = lean_ctor_get(v_e_1348_, 2);
v_binderInfo_1387_ = lean_ctor_get_uint8(v_e_1348_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1349_);
lean_inc_ref(v_binderType_1385_);
v___x_1388_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_binderType_1385_, v_offset_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
v_fst_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_fst_1389_);
v_snd_1390_ = lean_ctor_get(v___x_1388_, 1);
lean_inc(v_snd_1390_);
lean_dec_ref(v___x_1388_);
v_fst_1391_ = lean_ctor_get(v_fst_1389_, 0);
lean_inc(v_fst_1391_);
v_snd_1392_ = lean_ctor_get(v_fst_1389_, 1);
lean_inc(v_snd_1392_);
lean_dec(v_fst_1389_);
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_add(v_offset_1349_, v___x_1393_);
lean_dec(v_offset_1349_);
lean_inc_ref(v_body_1386_);
v___x_1395_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_body_1386_, v___x_1394_, v_snd_1392_, v_a_1351_, v_snd_1390_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1399_ = v___x_1395_;
v_isShared_1400_ = v_isSharedCheck_1418_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snd_1397_);
lean_inc(v_fst_1396_);
lean_dec(v___x_1395_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1418_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1417_; 
v_fst_1401_ = lean_ctor_get(v_fst_1396_, 0);
v_snd_1402_ = lean_ctor_get(v_fst_1396_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_fst_1396_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1404_ = v_fst_1396_;
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_fst_1396_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___y_1407_; uint8_t v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1385_, v_fst_1391_);
if (v___x_1415_ == 0)
{
v___y_1407_ = v___x_1415_;
goto v___jp_1406_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1386_, v_fst_1401_);
v___y_1407_ = v___x_1416_;
goto v___jp_1406_;
}
v___jp_1406_:
{
if (v___y_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_inc(v_binderName_1384_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_dec_ref(v_e_1348_);
v___x_1408_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_binderName_1384_, v_binderInfo_1387_, v_fst_1391_, v_fst_1401_, v_snd_1402_, v_a_1351_, v_snd_1397_);
return v___x_1408_;
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_fst_1401_);
lean_dec(v_fst_1391_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_e_1348_);
v___x_1410_ = v___x_1404_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_e_1348_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_snd_1402_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1410_);
v___x_1412_ = v___x_1399_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_snd_1397_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1419_; lean_object* v_binderType_1420_; lean_object* v_body_1421_; uint8_t v_binderInfo_1422_; lean_object* v___x_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1453_; 
v_binderName_1419_ = lean_ctor_get(v_e_1348_, 0);
v_binderType_1420_ = lean_ctor_get(v_e_1348_, 1);
v_body_1421_ = lean_ctor_get(v_e_1348_, 2);
v_binderInfo_1422_ = lean_ctor_get_uint8(v_e_1348_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1349_);
lean_inc_ref(v_binderType_1420_);
v___x_1423_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_binderType_1420_, v_offset_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
v_fst_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_fst_1424_);
v_snd_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc(v_snd_1425_);
lean_dec_ref(v___x_1423_);
v_fst_1426_ = lean_ctor_get(v_fst_1424_, 0);
lean_inc(v_fst_1426_);
v_snd_1427_ = lean_ctor_get(v_fst_1424_, 1);
lean_inc(v_snd_1427_);
lean_dec(v_fst_1424_);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v_offset_1349_, v___x_1428_);
lean_dec(v_offset_1349_);
lean_inc_ref(v_body_1421_);
v___x_1430_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_body_1421_, v___x_1429_, v_snd_1427_, v_a_1351_, v_snd_1425_);
v_fst_1431_ = lean_ctor_get(v___x_1430_, 0);
v_snd_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1453_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1453_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1452_; 
v_fst_1436_ = lean_ctor_get(v_fst_1431_, 0);
v_snd_1437_ = lean_ctor_get(v_fst_1431_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_fst_1431_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1439_ = v_fst_1431_;
v_isShared_1440_ = v_isSharedCheck_1452_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_snd_1437_);
lean_inc(v_fst_1436_);
lean_dec(v_fst_1431_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1452_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___y_1442_; uint8_t v___x_1450_; 
v___x_1450_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1420_, v_fst_1426_);
if (v___x_1450_ == 0)
{
v___y_1442_ = v___x_1450_;
goto v___jp_1441_;
}
else
{
uint8_t v___x_1451_; 
v___x_1451_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1421_, v_fst_1436_);
v___y_1442_ = v___x_1451_;
goto v___jp_1441_;
}
v___jp_1441_:
{
if (v___y_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_binderName_1419_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1434_);
lean_dec_ref(v_e_1348_);
v___x_1443_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_binderName_1419_, v_binderInfo_1422_, v_fst_1426_, v_fst_1436_, v_snd_1437_, v_a_1351_, v_snd_1432_);
return v___x_1443_;
}
else
{
lean_object* v___x_1445_; 
lean_dec(v_fst_1436_);
lean_dec(v_fst_1426_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v_e_1348_);
v___x_1445_ = v___x_1439_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_e_1348_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1437_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1445_);
v___x_1447_ = v___x_1434_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1432_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1454_; lean_object* v_type_1455_; lean_object* v_value_1456_; lean_object* v_body_1457_; uint8_t v_nondep_1458_; lean_object* v___x_1459_; lean_object* v_fst_1460_; lean_object* v_snd_1461_; lean_object* v_fst_1462_; lean_object* v_snd_1463_; lean_object* v___x_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v_fst_1467_; lean_object* v_snd_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_fst_1472_; lean_object* v_snd_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1496_; 
v_declName_1454_ = lean_ctor_get(v_e_1348_, 0);
v_type_1455_ = lean_ctor_get(v_e_1348_, 1);
v_value_1456_ = lean_ctor_get(v_e_1348_, 2);
v_body_1457_ = lean_ctor_get(v_e_1348_, 3);
v_nondep_1458_ = lean_ctor_get_uint8(v_e_1348_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1349_);
lean_inc_ref(v_type_1455_);
v___x_1459_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_type_1455_, v_offset_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
v_fst_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_fst_1460_);
v_snd_1461_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_snd_1461_);
lean_dec_ref(v___x_1459_);
v_fst_1462_ = lean_ctor_get(v_fst_1460_, 0);
lean_inc(v_fst_1462_);
v_snd_1463_ = lean_ctor_get(v_fst_1460_, 1);
lean_inc(v_snd_1463_);
lean_dec(v_fst_1460_);
lean_inc(v_offset_1349_);
lean_inc_ref(v_value_1456_);
v___x_1464_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_value_1456_, v_offset_1349_, v_snd_1463_, v_a_1351_, v_snd_1461_);
v_fst_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_fst_1465_);
v_snd_1466_ = lean_ctor_get(v___x_1464_, 1);
lean_inc(v_snd_1466_);
lean_dec_ref(v___x_1464_);
v_fst_1467_ = lean_ctor_get(v_fst_1465_, 0);
lean_inc(v_fst_1467_);
v_snd_1468_ = lean_ctor_get(v_fst_1465_, 1);
lean_inc(v_snd_1468_);
lean_dec(v_fst_1465_);
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = lean_nat_add(v_offset_1349_, v___x_1469_);
lean_dec(v_offset_1349_);
lean_inc_ref(v_body_1457_);
v___x_1471_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_body_1457_, v___x_1470_, v_snd_1468_, v_a_1351_, v_snd_1466_);
v_fst_1472_ = lean_ctor_get(v___x_1471_, 0);
v_snd_1473_ = lean_ctor_get(v___x_1471_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1475_ = v___x_1471_;
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snd_1473_);
lean_inc(v_fst_1472_);
lean_dec(v___x_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_fst_1477_; lean_object* v_snd_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1495_; 
v_fst_1477_ = lean_ctor_get(v_fst_1472_, 0);
v_snd_1478_ = lean_ctor_get(v_fst_1472_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_fst_1472_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1480_ = v_fst_1472_;
v_isShared_1481_ = v_isSharedCheck_1495_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snd_1478_);
lean_inc(v_fst_1477_);
lean_dec(v_fst_1472_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1495_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___y_1483_; uint8_t v___x_1493_; 
v___x_1493_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1455_, v_fst_1462_);
if (v___x_1493_ == 0)
{
v___y_1483_ = v___x_1493_;
goto v___jp_1482_;
}
else
{
uint8_t v___x_1494_; 
v___x_1494_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1456_, v_fst_1467_);
v___y_1483_ = v___x_1494_;
goto v___jp_1482_;
}
v___jp_1482_:
{
if (v___y_1483_ == 0)
{
lean_object* v___x_1484_; 
lean_inc(v_declName_1454_);
lean_del_object(v___x_1480_);
lean_del_object(v___x_1475_);
lean_dec_ref(v_e_1348_);
v___x_1484_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1454_, v_fst_1462_, v_fst_1467_, v_fst_1477_, v_nondep_1458_, v_snd_1478_, v_a_1351_, v_snd_1473_);
return v___x_1484_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1457_, v_fst_1477_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
lean_inc(v_declName_1454_);
lean_del_object(v___x_1480_);
lean_del_object(v___x_1475_);
lean_dec_ref(v_e_1348_);
v___x_1486_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1454_, v_fst_1462_, v_fst_1467_, v_fst_1477_, v_nondep_1458_, v_snd_1478_, v_a_1351_, v_snd_1473_);
return v___x_1486_;
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_fst_1477_);
lean_dec(v_fst_1467_);
lean_dec(v_fst_1462_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v_e_1348_);
v___x_1488_ = v___x_1480_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_e_1348_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1478_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1488_);
v___x_1490_ = v___x_1475_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1473_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_1497_; lean_object* v_expr_1498_; lean_object* v___x_1499_; lean_object* v_fst_1500_; lean_object* v_snd_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1519_; 
v_data_1497_ = lean_ctor_get(v_e_1348_, 0);
v_expr_1498_ = lean_ctor_get(v_e_1348_, 1);
lean_inc_ref(v_expr_1498_);
v___x_1499_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_expr_1498_, v_offset_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
v_fst_1500_ = lean_ctor_get(v___x_1499_, 0);
v_snd_1501_ = lean_ctor_get(v___x_1499_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1519_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1501_);
lean_inc(v_fst_1500_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1519_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1518_; 
v_fst_1505_ = lean_ctor_get(v_fst_1500_, 0);
v_snd_1506_ = lean_ctor_get(v_fst_1500_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_fst_1500_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1508_ = v_fst_1500_;
v_isShared_1509_ = v_isSharedCheck_1518_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_inc(v_fst_1505_);
lean_dec(v_fst_1500_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1518_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint8_t v___x_1510_; 
v___x_1510_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1498_, v_fst_1505_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_inc(v_data_1497_);
lean_del_object(v___x_1508_);
lean_del_object(v___x_1503_);
lean_dec_ref(v_e_1348_);
v___x_1511_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_data_1497_, v_fst_1505_, v_snd_1506_, v_a_1351_, v_snd_1501_);
return v___x_1511_;
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_fst_1505_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v_e_1348_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_e_1348_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_snd_1506_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1513_);
v___x_1515_ = v___x_1503_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_snd_1501_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1520_; lean_object* v_idx_1521_; lean_object* v_struct_1522_; lean_object* v___x_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1543_; 
v_typeName_1520_ = lean_ctor_get(v_e_1348_, 0);
v_idx_1521_ = lean_ctor_get(v_e_1348_, 1);
v_struct_1522_ = lean_ctor_get(v_e_1348_, 2);
lean_inc_ref(v_struct_1522_);
v___x_1523_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1345_, v_varDeps_1346_, v_xs_1347_, v_struct_1522_, v_offset_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
v_fst_1524_ = lean_ctor_get(v___x_1523_, 0);
v_snd_1525_ = lean_ctor_get(v___x_1523_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1527_ = v___x_1523_;
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_inc(v_fst_1524_);
lean_dec(v___x_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_fst_1529_; lean_object* v_snd_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1542_; 
v_fst_1529_ = lean_ctor_get(v_fst_1524_, 0);
v_snd_1530_ = lean_ctor_get(v_fst_1524_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_fst_1524_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1532_ = v_fst_1524_;
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_snd_1530_);
lean_inc(v_fst_1529_);
lean_dec(v_fst_1524_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1522_, v_fst_1529_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_idx_1521_);
lean_inc(v_typeName_1520_);
lean_del_object(v___x_1532_);
lean_del_object(v___x_1527_);
lean_dec_ref(v_e_1348_);
v___x_1535_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_typeName_1520_, v_idx_1521_, v_fst_1529_, v_snd_1530_, v_a_1351_, v_snd_1525_);
return v___x_1535_;
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_fst_1529_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_e_1348_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_e_1348_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_snd_1530_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1537_);
v___x_1539_ = v___x_1527_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_snd_1525_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_offset_1349_);
lean_dec_ref(v_e_1348_);
v___x_1544_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3);
v___x_1545_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v___x_1544_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object* v_n_1546_, lean_object* v_varDeps_1547_, lean_object* v_xs_1548_, lean_object* v_e_1549_, lean_object* v_offset_1550_, lean_object* v_a_1551_, uint8_t v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_key_1554_; lean_object* v_snd_1556_; lean_object* v___x_1569_; 
lean_inc(v_offset_1550_);
lean_inc_ref(v_e_1549_);
v_key_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1554_, 0, v_e_1549_);
lean_ctor_set(v_key_1554_, 1, v_offset_1550_);
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_a_1551_, v_key_1554_);
if (lean_obj_tag(v___x_1569_) == 1)
{
lean_object* v_val_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_key_1554_);
lean_dec(v_offset_1550_);
lean_dec_ref(v_e_1549_);
v_val_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_val_1570_);
lean_ctor_set(v___x_1571_, 1, v_a_1551_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1553_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
lean_dec(v___x_1569_);
v___x_1573_ = l_Lean_Expr_looseBVarRange(v_e_1549_);
v___x_1574_ = lean_nat_dec_le(v___x_1573_, v_offset_1550_);
lean_dec(v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Expr_getAppFn(v_e_1549_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_deBruijnIndex_1576_; uint8_t v___x_1577_; 
v_deBruijnIndex_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_deBruijnIndex_1576_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = lean_nat_dec_le(v_offset_1550_, v_deBruijnIndex_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec(v_deBruijnIndex_1576_);
lean_dec(v_offset_1550_);
v___x_1578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_a_1553_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_nat_add(v_offset_1550_, v_n_1546_);
v___x_1580_ = lean_nat_dec_lt(v_deBruijnIndex_1576_, v___x_1579_);
lean_dec(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1585_; 
lean_dec(v_offset_1550_);
lean_dec_ref(v_e_1549_);
v___x_1581_ = lean_nat_sub(v_deBruijnIndex_1576_, v_n_1546_);
lean_dec(v_deBruijnIndex_1576_);
v___x_1582_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1581_, v_a_1553_);
v_fst_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_fst_1583_);
v_snd_1584_ = lean_ctor_get(v___x_1582_, 1);
lean_inc(v_snd_1584_);
lean_dec_ref(v___x_1582_);
v___x_1585_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_fst_1583_, v_a_1551_, v_a_1552_, v_snd_1584_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_i_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v_expectedNumArgs_1592_; lean_object* v_numArgs_1593_; uint8_t v___x_1594_; 
v___x_1586_ = lean_nat_sub(v_deBruijnIndex_1576_, v_offset_1550_);
lean_dec(v_deBruijnIndex_1576_);
v___x_1587_ = lean_nat_sub(v_n_1546_, v___x_1586_);
lean_dec(v___x_1586_);
v___x_1588_ = lean_unsigned_to_nat(1u);
v_i_1589_ = lean_nat_sub(v___x_1587_, v___x_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1591_ = lean_array_get_borrowed(v___x_1590_, v_varDeps_1547_, v_i_1589_);
v_expectedNumArgs_1592_ = lean_array_get_size(v___x_1591_);
v_numArgs_1593_ = l_Lean_Expr_getAppNumArgs(v_e_1549_);
v___x_1594_ = lean_nat_dec_lt(v_expectedNumArgs_1592_, v_numArgs_1593_);
if (v___x_1594_ == 0)
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_nat_dec_eq(v_numArgs_1593_, v_expectedNumArgs_1592_);
lean_dec(v_numArgs_1593_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_fst_1598_; 
lean_dec(v_i_1589_);
v___x_1596_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1597_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1596_, v_a_1552_, v_a_1553_);
v_fst_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_fst_1598_);
if (lean_obj_tag(v_fst_1598_) == 1)
{
lean_object* v_snd_1599_; lean_object* v_val_1600_; lean_object* v___x_1601_; 
lean_dec(v_offset_1550_);
lean_dec_ref(v_e_1549_);
v_snd_1599_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_snd_1599_);
lean_dec_ref(v___x_1597_);
v_val_1600_ = lean_ctor_get(v_fst_1598_, 0);
lean_inc(v_val_1600_);
lean_dec_ref(v_fst_1598_);
v___x_1601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_val_1600_, v_a_1551_, v_a_1552_, v_snd_1599_);
return v___x_1601_;
}
else
{
lean_object* v_snd_1602_; 
lean_dec(v_fst_1598_);
v_snd_1602_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_snd_1602_);
lean_dec_ref(v___x_1597_);
v_snd_1556_ = v_snd_1602_;
goto v___jp_1555_;
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_offset_1550_);
lean_dec_ref(v_e_1549_);
v___x_1603_ = lean_array_fget_borrowed(v_xs_1548_, v_i_1589_);
lean_dec(v_i_1589_);
lean_inc(v___x_1603_);
v___x_1604_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v___x_1603_, v_a_1551_, v_a_1552_, v_a_1553_);
return v___x_1604_;
}
}
else
{
lean_dec(v_numArgs_1593_);
lean_dec(v_i_1589_);
v_snd_1556_ = v_a_1553_;
goto v___jp_1555_;
}
}
}
}
else
{
lean_dec_ref(v___x_1575_);
v_snd_1556_ = v_a_1553_;
goto v___jp_1555_;
}
}
else
{
lean_object* v___x_1605_; 
lean_dec(v_offset_1550_);
v___x_1605_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_a_1553_);
return v___x_1605_;
}
}
v___jp_1555_:
{
switch(lean_obj_tag(v_e_1549_))
{
case 9:
{
lean_object* v___x_1557_; 
lean_dec(v_offset_1550_);
v___x_1557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_snd_1556_);
return v___x_1557_;
}
case 2:
{
lean_object* v___x_1558_; 
lean_dec(v_offset_1550_);
v___x_1558_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_snd_1556_);
return v___x_1558_;
}
case 0:
{
lean_object* v___x_1559_; 
lean_dec(v_offset_1550_);
v___x_1559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_snd_1556_);
return v___x_1559_;
}
case 1:
{
lean_object* v___x_1560_; 
lean_dec(v_offset_1550_);
v___x_1560_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_snd_1556_);
return v___x_1560_;
}
case 4:
{
lean_object* v___x_1561_; 
lean_dec(v_offset_1550_);
v___x_1561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_snd_1556_);
return v___x_1561_;
}
case 3:
{
lean_object* v___x_1562_; 
lean_dec(v_offset_1550_);
v___x_1562_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_e_1549_, v_a_1551_, v_a_1552_, v_snd_1556_);
return v___x_1562_;
}
default: 
{
lean_object* v___x_1563_; lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1568_; 
v___x_1563_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_e_1549_, v_offset_1550_, v_a_1551_, v_a_1552_, v_snd_1556_);
v_fst_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_fst_1564_);
v_snd_1565_ = lean_ctor_get(v___x_1563_, 1);
lean_inc(v_snd_1565_);
lean_dec_ref(v___x_1563_);
v_fst_1566_ = lean_ctor_get(v_fst_1564_, 0);
lean_inc(v_fst_1566_);
v_snd_1567_ = lean_ctor_get(v_fst_1564_, 1);
lean_inc(v_snd_1567_);
lean_dec(v_fst_1564_);
v___x_1568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1554_, v_fst_1566_, v_snd_1567_, v_a_1552_, v_snd_1565_);
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object* v_n_1606_, lean_object* v_varDeps_1607_, lean_object* v_xs_1608_, lean_object* v_e_1609_, lean_object* v_offset_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
uint8_t v_a_22375__boxed_1614_; lean_object* v_res_1615_; 
v_a_22375__boxed_1614_ = lean_unbox(v_a_1612_);
v_res_1615_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1606_, v_varDeps_1607_, v_xs_1608_, v_e_1609_, v_offset_1610_, v_a_1611_, v_a_22375__boxed_1614_, v_a_1613_);
lean_dec_ref(v_xs_1608_);
lean_dec_ref(v_varDeps_1607_);
lean_dec(v_n_1606_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_n_1616_, lean_object* v_varDeps_1617_, lean_object* v_xs_1618_, lean_object* v_e_1619_, lean_object* v_offset_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
uint8_t v_a_22442__boxed_1624_; lean_object* v_res_1625_; 
v_a_22442__boxed_1624_ = lean_unbox(v_a_1622_);
v_res_1625_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1616_, v_varDeps_1617_, v_xs_1618_, v_e_1619_, v_offset_1620_, v_a_1621_, v_a_22442__boxed_1624_, v_a_1623_);
lean_dec_ref(v_xs_1618_);
lean_dec_ref(v_varDeps_1617_);
lean_dec(v_n_1616_);
return v_res_1625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0(void){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_box(0));
return v___x_1626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_unsigned_to_nat(16u);
v___x_1629_ = lean_mk_array(v___x_1628_, v___x_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object* v_e_1633_, lean_object* v_xs_1634_, lean_object* v_varDeps_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_share_1639_; lean_object* v_maxFVar_1640_; lean_object* v_proofInstInfo_1641_; lean_object* v_inferType_1642_; lean_object* v_getLevel_1643_; lean_object* v_congrInfo_1644_; lean_object* v_defEqI_1645_; uint8_t v_debug_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1713_; 
v___x_1638_ = lean_st_ref_take(v_a_1636_);
v_share_1639_ = lean_ctor_get(v___x_1638_, 0);
v_maxFVar_1640_ = lean_ctor_get(v___x_1638_, 1);
v_proofInstInfo_1641_ = lean_ctor_get(v___x_1638_, 2);
v_inferType_1642_ = lean_ctor_get(v___x_1638_, 3);
v_getLevel_1643_ = lean_ctor_get(v___x_1638_, 4);
v_congrInfo_1644_ = lean_ctor_get(v___x_1638_, 5);
v_defEqI_1645_ = lean_ctor_get(v___x_1638_, 6);
v_debug_1646_ = lean_ctor_get_uint8(v___x_1638_, sizeof(void*)*7);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1648_ = v___x_1638_;
v_isShared_1649_ = v_isSharedCheck_1713_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_defEqI_1645_);
lean_inc(v_congrInfo_1644_);
lean_inc(v_getLevel_1643_);
lean_inc(v_inferType_1642_);
lean_inc(v_proofInstInfo_1641_);
lean_inc(v_maxFVar_1640_);
lean_inc(v_share_1639_);
lean_dec(v___x_1638_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1713_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_maxFVar_1640_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_proofInstInfo_1641_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_inferType_1642_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v_getLevel_1643_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_congrInfo_1644_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_defEqI_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*7, v_debug_1646_);
v___x_1652_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_fst_1656_; lean_object* v_snd_1657_; uint8_t v_debug_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1653_ = lean_st_ref_set(v_a_1636_, v___x_1652_);
v___x_1654_ = lean_st_ref_get(v_a_1636_);
v_debug_1676_ = lean_ctor_get_uint8(v___x_1654_, sizeof(void*)*7);
lean_dec(v___x_1654_);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = l_Lean_Expr_looseBVarRange(v_e_1633_);
v___x_1679_ = lean_nat_dec_le(v___x_1678_, v___x_1677_);
lean_dec(v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v_n_1680_; lean_object* v_snd_1682_; lean_object* v___x_1688_; 
v_n_1680_ = lean_array_get_size(v_xs_1634_);
v___x_1688_ = l_Lean_Expr_getAppFn(v_e_1633_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_deBruijnIndex_1689_; uint8_t v___x_1690_; 
v_deBruijnIndex_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_deBruijnIndex_1689_);
lean_dec_ref(v___x_1688_);
v___x_1690_ = lean_nat_dec_le(v___x_1677_, v_deBruijnIndex_1689_);
if (v___x_1690_ == 0)
{
lean_dec(v_deBruijnIndex_1689_);
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_share_1639_;
goto v___jp_1655_;
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_nat_dec_lt(v_deBruijnIndex_1689_, v_n_1680_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v_fst_1694_; lean_object* v_snd_1695_; 
lean_dec_ref(v_e_1633_);
v___x_1692_ = lean_nat_sub(v_deBruijnIndex_1689_, v_n_1680_);
lean_dec(v_deBruijnIndex_1689_);
v___x_1693_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1692_, v_share_1639_);
v_fst_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_fst_1694_);
v_snd_1695_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_snd_1695_);
lean_dec_ref(v___x_1693_);
v_fst_1656_ = v_fst_1694_;
v_snd_1657_ = v_snd_1695_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_i_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_expectedNumArgs_1701_; lean_object* v_numArgs_1702_; uint8_t v___x_1703_; 
v___x_1696_ = lean_nat_sub(v_n_1680_, v_deBruijnIndex_1689_);
lean_dec(v_deBruijnIndex_1689_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v_i_1698_ = lean_nat_sub(v___x_1696_, v___x_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1700_ = lean_array_get_borrowed(v___x_1699_, v_varDeps_1635_, v_i_1698_);
v_expectedNumArgs_1701_ = lean_array_get_size(v___x_1700_);
v_numArgs_1702_ = l_Lean_Expr_getAppNumArgs(v_e_1633_);
v___x_1703_ = lean_nat_dec_lt(v_expectedNumArgs_1701_, v_numArgs_1702_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_nat_dec_eq(v_numArgs_1702_, v_expectedNumArgs_1701_);
lean_dec(v_numArgs_1702_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_fst_1707_; 
lean_dec(v_i_1698_);
v___x_1705_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1706_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1705_, v_debug_1676_, v_share_1639_);
v_fst_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_fst_1707_);
if (lean_obj_tag(v_fst_1707_) == 1)
{
lean_object* v_snd_1708_; lean_object* v_val_1709_; 
lean_dec_ref(v_e_1633_);
v_snd_1708_ = lean_ctor_get(v___x_1706_, 1);
lean_inc(v_snd_1708_);
lean_dec_ref(v___x_1706_);
v_val_1709_ = lean_ctor_get(v_fst_1707_, 0);
lean_inc(v_val_1709_);
lean_dec_ref(v_fst_1707_);
v_fst_1656_ = v_val_1709_;
v_snd_1657_ = v_snd_1708_;
goto v___jp_1655_;
}
else
{
lean_object* v_snd_1710_; 
lean_dec(v_fst_1707_);
v_snd_1710_ = lean_ctor_get(v___x_1706_, 1);
lean_inc(v_snd_1710_);
lean_dec_ref(v___x_1706_);
v_snd_1682_ = v_snd_1710_;
goto v___jp_1681_;
}
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v_e_1633_);
v___x_1711_ = lean_array_fget_borrowed(v_xs_1634_, v_i_1698_);
lean_dec(v_i_1698_);
lean_inc(v___x_1711_);
v_fst_1656_ = v___x_1711_;
v_snd_1657_ = v_share_1639_;
goto v___jp_1655_;
}
}
else
{
lean_dec(v_numArgs_1702_);
lean_dec(v_i_1698_);
v_snd_1682_ = v_share_1639_;
goto v___jp_1681_;
}
}
}
}
else
{
lean_dec_ref(v___x_1688_);
v_snd_1682_ = v_share_1639_;
goto v___jp_1681_;
}
v___jp_1681_:
{
switch(lean_obj_tag(v_e_1633_))
{
case 9:
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_snd_1682_;
goto v___jp_1655_;
}
case 2:
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_snd_1682_;
goto v___jp_1655_;
}
case 0:
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_snd_1682_;
goto v___jp_1655_;
}
case 1:
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_snd_1682_;
goto v___jp_1655_;
}
case 4:
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_snd_1682_;
goto v___jp_1655_;
}
case 3:
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_snd_1682_;
goto v___jp_1655_;
}
default: 
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_fst_1685_; lean_object* v_snd_1686_; lean_object* v_fst_1687_; 
v___x_1683_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2);
v___x_1684_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1680_, v_varDeps_1635_, v_xs_1634_, v_e_1633_, v___x_1677_, v___x_1683_, v_debug_1676_, v_snd_1682_);
v_fst_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_fst_1685_);
v_snd_1686_ = lean_ctor_get(v___x_1684_, 1);
lean_inc(v_snd_1686_);
lean_dec_ref(v___x_1684_);
v_fst_1687_ = lean_ctor_get(v_fst_1685_, 0);
lean_inc(v_fst_1687_);
lean_dec(v_fst_1685_);
v_fst_1656_ = v_fst_1687_;
v_snd_1657_ = v_snd_1686_;
goto v___jp_1655_;
}
}
}
}
else
{
v_fst_1656_ = v_e_1633_;
v_snd_1657_ = v_share_1639_;
goto v___jp_1655_;
}
v___jp_1655_:
{
lean_object* v___x_1658_; lean_object* v_maxFVar_1659_; lean_object* v_proofInstInfo_1660_; lean_object* v_inferType_1661_; lean_object* v_getLevel_1662_; lean_object* v_congrInfo_1663_; lean_object* v_defEqI_1664_; uint8_t v_debug_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1674_; 
v___x_1658_ = lean_st_ref_take(v_a_1636_);
v_maxFVar_1659_ = lean_ctor_get(v___x_1658_, 1);
v_proofInstInfo_1660_ = lean_ctor_get(v___x_1658_, 2);
v_inferType_1661_ = lean_ctor_get(v___x_1658_, 3);
v_getLevel_1662_ = lean_ctor_get(v___x_1658_, 4);
v_congrInfo_1663_ = lean_ctor_get(v___x_1658_, 5);
v_defEqI_1664_ = lean_ctor_get(v___x_1658_, 6);
v_debug_1665_ = lean_ctor_get_uint8(v___x_1658_, sizeof(void*)*7);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v___x_1658_, 0);
lean_dec(v_unused_1675_);
v___x_1667_ = v___x_1658_;
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_defEqI_1664_);
lean_inc(v_congrInfo_1663_);
lean_inc(v_getLevel_1662_);
lean_inc(v_inferType_1661_);
lean_inc(v_proofInstInfo_1660_);
lean_inc(v_maxFVar_1659_);
lean_dec(v___x_1658_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v_snd_1657_);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_snd_1657_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_maxFVar_1659_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_proofInstInfo_1660_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_inferType_1661_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_getLevel_1662_);
lean_ctor_set(v_reuseFailAlloc_1673_, 5, v_congrInfo_1663_);
lean_ctor_set(v_reuseFailAlloc_1673_, 6, v_defEqI_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1673_, sizeof(void*)*7, v_debug_1665_);
v___x_1670_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_st_ref_set(v_a_1636_, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_fst_1656_);
return v___x_1672_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object* v_e_1714_, lean_object* v_xs_1715_, lean_object* v_varDeps_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1714_, v_xs_1715_, v_varDeps_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_varDeps_1716_);
lean_dec_ref(v_xs_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1720_, lean_object* v_xs_1721_, lean_object* v_varDeps_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1720_, v_xs_1721_, v_varDeps_1722_, v_a_1724_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1731_, lean_object* v_xs_1732_, lean_object* v_varDeps_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1731_, v_xs_1732_, v_varDeps_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec_ref(v_varDeps_1733_);
lean_dec_ref(v_xs_1732_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1742_, lean_object* v_m_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1743_, v_a_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1746_, lean_object* v_m_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(v_00_u03b2_1746_, v_m_1747_, v_a_1748_);
lean_dec_ref(v_a_1748_);
lean_dec_ref(v_m_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_1750_, lean_object* v_a_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1751_, v_x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1754_, lean_object* v_a_1755_, lean_object* v_x_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(v_00_u03b2_1754_, v_a_1755_, v_x_1756_);
lean_dec(v_x_1756_);
lean_dec_ref(v_a_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1758_, lean_object* v_type_1759_, lean_object* v_val_1760_, lean_object* v_k_1761_, uint8_t v_nondep_1762_, uint8_t v_kind_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___f_1771_; lean_object* v___x_1772_; 
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1771_, 0, v_k_1761_);
lean_closure_set(v___f_1771_, 1, v___y_1764_);
lean_closure_set(v___f_1771_, 2, v___y_1765_);
v___x_1772_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1758_, v_type_1759_, v_val_1760_, v___f_1771_, v_nondep_1762_, v_kind_1763_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1772_) == 0)
{
return v___x_1772_;
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1781_, lean_object* v_type_1782_, lean_object* v_val_1783_, lean_object* v_k_1784_, lean_object* v_nondep_1785_, lean_object* v_kind_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
uint8_t v_nondep_boxed_1794_; uint8_t v_kind_boxed_1795_; lean_object* v_res_1796_; 
v_nondep_boxed_1794_ = lean_unbox(v_nondep_1785_);
v_kind_boxed_1795_ = lean_unbox(v_kind_1786_);
v_res_1796_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1781_, v_type_1782_, v_val_1783_, v_k_1784_, v_nondep_boxed_1794_, v_kind_boxed_1795_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1797_, lean_object* v_name_1798_, lean_object* v_type_1799_, lean_object* v_val_1800_, lean_object* v_k_1801_, uint8_t v_nondep_1802_, uint8_t v_kind_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1798_, v_type_1799_, v_val_1800_, v_k_1801_, v_nondep_1802_, v_kind_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_name_1813_, lean_object* v_type_1814_, lean_object* v_val_1815_, lean_object* v_k_1816_, lean_object* v_nondep_1817_, lean_object* v_kind_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v_nondep_boxed_1826_; uint8_t v_kind_boxed_1827_; lean_object* v_res_1828_; 
v_nondep_boxed_1826_ = lean_unbox(v_nondep_1817_);
v_kind_boxed_1827_ = lean_unbox(v_kind_1818_);
v_res_1828_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_1812_, v_name_1813_, v_type_1814_, v_val_1815_, v_k_1816_, v_nondep_boxed_1826_, v_kind_boxed_1827_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object* v_msg_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v_toApplicative_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1902_; 
v___x_1837_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0);
v___x_1838_ = l_ReaderT_instMonad___redArg(v___x_1837_);
v_toApplicative_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1838_, 1);
lean_dec(v_unused_1903_);
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1902_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_toApplicative_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1902_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_toFunctor_1843_; lean_object* v_toSeq_1844_; lean_object* v_toSeqLeft_1845_; lean_object* v_toSeqRight_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1900_; 
v_toFunctor_1843_ = lean_ctor_get(v_toApplicative_1839_, 0);
v_toSeq_1844_ = lean_ctor_get(v_toApplicative_1839_, 2);
v_toSeqLeft_1845_ = lean_ctor_get(v_toApplicative_1839_, 3);
v_toSeqRight_1846_ = lean_ctor_get(v_toApplicative_1839_, 4);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_toApplicative_1839_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_toApplicative_1839_, 1);
lean_dec(v_unused_1901_);
v___x_1848_ = v_toApplicative_1839_;
v_isShared_1849_ = v_isSharedCheck_1900_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_toSeqRight_1846_);
lean_inc(v_toSeqLeft_1845_);
lean_inc(v_toSeq_1844_);
lean_inc(v_toFunctor_1843_);
lean_dec(v_toApplicative_1839_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1900_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___f_1856_; lean_object* v___f_1857_; lean_object* v___x_1859_; 
v___f_1850_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__1));
v___f_1851_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__2));
lean_inc_ref(v_toFunctor_1843_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toFunctor_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1853_, 0, v_toFunctor_1843_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___f_1852_);
lean_ctor_set(v___x_1854_, 1, v___f_1853_);
v___f_1855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1855_, 0, v_toSeqRight_1846_);
v___f_1856_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1856_, 0, v_toSeqLeft_1845_);
v___f_1857_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1857_, 0, v_toSeq_1844_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 4, v___f_1855_);
lean_ctor_set(v___x_1848_, 3, v___f_1856_);
lean_ctor_set(v___x_1848_, 2, v___f_1857_);
lean_ctor_set(v___x_1848_, 1, v___f_1850_);
lean_ctor_set(v___x_1848_, 0, v___x_1854_);
v___x_1859_ = v___x_1848_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___f_1850_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___f_1857_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v___f_1856_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v___f_1855_);
v___x_1859_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___f_1851_);
lean_ctor_set(v___x_1841_, 0, v___x_1859_);
v___x_1861_ = v___x_1841_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___f_1851_);
v___x_1861_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v_toApplicative_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1896_; 
v___x_1862_ = l_ReaderT_instMonad___redArg(v___x_1861_);
v_toApplicative_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1862_, 1);
lean_dec(v_unused_1897_);
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1896_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_toApplicative_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1896_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_toFunctor_1867_; lean_object* v_toSeq_1868_; lean_object* v_toSeqLeft_1869_; lean_object* v_toSeqRight_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1894_; 
v_toFunctor_1867_ = lean_ctor_get(v_toApplicative_1863_, 0);
v_toSeq_1868_ = lean_ctor_get(v_toApplicative_1863_, 2);
v_toSeqLeft_1869_ = lean_ctor_get(v_toApplicative_1863_, 3);
v_toSeqRight_1870_ = lean_ctor_get(v_toApplicative_1863_, 4);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_toApplicative_1863_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v_toApplicative_1863_, 1);
lean_dec(v_unused_1895_);
v___x_1872_ = v_toApplicative_1863_;
v_isShared_1873_ = v_isSharedCheck_1894_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_toSeqRight_1870_);
lean_inc(v_toSeqLeft_1869_);
lean_inc(v_toSeq_1868_);
lean_inc(v_toFunctor_1867_);
lean_dec(v_toApplicative_1863_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1894_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___f_1874_; lean_object* v___f_1875_; lean_object* v___f_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___f_1881_; lean_object* v___x_1883_; 
v___f_1874_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__3));
v___f_1875_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__4));
lean_inc_ref(v_toFunctor_1867_);
v___f_1876_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1876_, 0, v_toFunctor_1867_);
v___f_1877_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1877_, 0, v_toFunctor_1867_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___f_1876_);
lean_ctor_set(v___x_1878_, 1, v___f_1877_);
v___f_1879_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1879_, 0, v_toSeqRight_1870_);
v___f_1880_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1880_, 0, v_toSeqLeft_1869_);
v___f_1881_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1881_, 0, v_toSeq_1868_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___f_1879_);
lean_ctor_set(v___x_1872_, 3, v___f_1880_);
lean_ctor_set(v___x_1872_, 2, v___f_1881_);
lean_ctor_set(v___x_1872_, 1, v___f_1874_);
lean_ctor_set(v___x_1872_, 0, v___x_1878_);
v___x_1883_ = v___x_1872_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___f_1874_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v___f_1881_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v___f_1880_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___f_1879_);
v___x_1883_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___f_1875_);
lean_ctor_set(v___x_1865_, 0, v___x_1883_);
v___x_1885_ = v___x_1865_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___f_1875_);
v___x_1885_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___f_1889_; lean_object* v___x_2398__overap_1890_; lean_object* v___x_1891_; 
v___x_1886_ = l_ReaderT_instMonad___redArg(v___x_1885_);
v___x_1887_ = l_Lean_instInhabitedExpr;
v___x_1888_ = l_instInhabitedOfMonad___redArg(v___x_1886_, v___x_1887_);
v___f_1889_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1889_, 0, v___x_1888_);
v___x_2398__overap_1890_ = lean_panic_fn(v___f_1889_, v_msg_1829_);
v___x_1891_ = lean_apply_7(v___x_2398__overap_1890_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, lean_box(0));
return v___x_1891_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v_msg_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_1913_, size_t v_sz_1914_, size_t v_i_1915_, lean_object* v_bs_1916_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_lt(v_i_1915_, v_sz_1914_);
if (v___x_1917_ == 0)
{
return v_bs_1916_;
}
else
{
lean_object* v_v_1918_; lean_object* v___x_1919_; lean_object* v_bs_x27_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v_v_1918_ = lean_array_uget(v_bs_1916_, v_i_1915_);
v___x_1919_ = lean_unsigned_to_nat(0u);
v_bs_x27_1920_ = lean_array_uset(v_bs_1916_, v_i_1915_, v___x_1919_);
v___x_1921_ = l_Lean_instInhabitedExpr;
v___x_1922_ = lean_array_get_borrowed(v___x_1921_, v_xs_1913_, v_v_1918_);
lean_dec(v_v_1918_);
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_i_1915_, v___x_1923_);
lean_inc(v___x_1922_);
v___x_1925_ = lean_array_uset(v_bs_x27_1920_, v_i_1915_, v___x_1922_);
v_i_1915_ = v___x_1924_;
v_bs_1916_ = v___x_1925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_1927_, lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_bs_1930_){
_start:
{
size_t v_sz_boxed_1931_; size_t v_i_boxed_1932_; lean_object* v_res_1933_; 
v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1932_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1927_, v_sz_boxed_1931_, v_i_boxed_1932_, v_bs_1930_);
lean_dec_ref(v_xs_1927_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_1934_, lean_object* v_i_1935_, lean_object* v_varDeps_1936_, lean_object* v_args_1937_, lean_object* v_body_1938_, lean_object* v_x_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_1934_, v_i_1935_, v_varDeps_1936_, v_args_1937_, v_body_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v_i_1935_);
return v_res_1947_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1950_ = lean_unsigned_to_nat(30u);
v___x_1951_ = lean_unsigned_to_nat(254u);
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1954_ = l_mkPanicMessageWithDecl(v___x_1953_, v___x_1952_, v___x_1951_, v___x_1950_, v___x_1949_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_1955_, lean_object* v_args_1956_, lean_object* v_f_1957_, lean_object* v_xs_1958_, lean_object* v_i_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_array_get_size(v_args_1956_);
v___x_1968_ = lean_nat_dec_lt(v_i_1959_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v_a_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; 
lean_dec_ref(v_a_1960_);
lean_dec(v_i_1959_);
lean_dec_ref(v_args_1956_);
v___x_1969_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_f_1957_, v_xs_1958_, v_varDeps_1955_, v_a_1961_);
lean_dec_ref(v_varDeps_1955_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = 1;
v___x_1972_ = l_Lean_Meta_mkLetFVars(v_xs_1958_, v_a_1970_, v___x_1968_, v___x_1968_, v___x_1971_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec_ref(v_xs_1958_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_1973_, v_a_1961_);
lean_dec(v_a_1961_);
return v___x_1974_;
}
else
{
lean_dec(v_a_1961_);
return v___x_1972_;
}
}
else
{
if (lean_obj_tag(v_f_1957_) == 6)
{
lean_object* v_binderName_1975_; lean_object* v_binderType_1976_; lean_object* v_body_1977_; lean_object* v_varPos_1978_; size_t v_sz_1979_; size_t v___x_1980_; lean_object* v_ys_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_binderName_1975_ = lean_ctor_get(v_f_1957_, 0);
lean_inc(v_binderName_1975_);
v_binderType_1976_ = lean_ctor_get(v_f_1957_, 1);
lean_inc_ref(v_binderType_1976_);
v_body_1977_ = lean_ctor_get(v_f_1957_, 2);
lean_inc_ref(v_body_1977_);
lean_dec_ref(v_f_1957_);
v_varPos_1978_ = lean_array_fget(v_varDeps_1955_, v_i_1959_);
v_sz_1979_ = lean_array_size(v_varPos_1978_);
v___x_1980_ = ((size_t)0ULL);
lean_inc(v_varPos_1978_);
v_ys_1981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1958_, v_sz_1979_, v___x_1980_, v_varPos_1978_);
v___x_1982_ = lean_array_fget_borrowed(v_args_1956_, v_i_1959_);
v___x_1983_ = 0;
lean_inc(v___x_1982_);
v___x_1984_ = l_Lean_Expr_betaRev(v___x_1982_, v_ys_1981_, v___x_1983_, v___x_1983_);
lean_dec_ref(v_ys_1981_);
v___x_1985_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1984_, v_a_1961_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___f_1987_; lean_object* v___x_1988_; lean_object* v_type_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref(v___x_1985_);
v___f_1987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1987_, 0, v_xs_1958_);
lean_closure_set(v___f_1987_, 1, v_i_1959_);
lean_closure_set(v___f_1987_, 2, v_varDeps_1955_);
lean_closure_set(v___f_1987_, 3, v_args_1956_);
lean_closure_set(v___f_1987_, 4, v_body_1977_);
v___x_1988_ = lean_array_get_size(v_varPos_1978_);
lean_dec(v_varPos_1978_);
v_type_1989_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_1976_, v___x_1988_);
v___x_1990_ = 0;
v___x_1991_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_1975_, v_type_1989_, v_a_1986_, v___f_1987_, v___x_1968_, v___x_1990_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_1991_;
}
else
{
lean_dec(v_varPos_1978_);
lean_dec_ref(v_body_1977_);
lean_dec_ref(v_binderType_1976_);
lean_dec(v_binderName_1975_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_i_1959_);
lean_dec_ref(v_xs_1958_);
lean_dec_ref(v_args_1956_);
lean_dec_ref(v_varDeps_1955_);
return v___x_1985_;
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_dec(v_i_1959_);
lean_dec_ref(v_xs_1958_);
lean_dec_ref(v_f_1957_);
lean_dec_ref(v_args_1956_);
lean_dec_ref(v_varDeps_1955_);
v___x_1992_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_1993_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1992_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_1994_, lean_object* v_i_1995_, lean_object* v_varDeps_1996_, lean_object* v_args_1997_, lean_object* v_body_1998_, lean_object* v_x_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_x_1999_, v___y_2001_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = lean_array_push(v_xs_1994_, v_a_2008_);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v_i_1995_, v___x_2010_);
v___x_2012_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1996_, v_args_1997_, v_body_1998_, v___x_2009_, v___x_2011_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
return v___x_2012_;
}
else
{
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v_body_1998_);
lean_dec_ref(v_args_1997_);
lean_dec_ref(v_varDeps_1996_);
lean_dec_ref(v_xs_1994_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_2013_, lean_object* v_args_2014_, lean_object* v_f_2015_, lean_object* v_xs_2016_, lean_object* v_i_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2013_, v_args_2014_, v_f_2015_, v_xs_2016_, v_i_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_2026_, lean_object* v_args_2027_, lean_object* v___h_2028_, lean_object* v_f_2029_, lean_object* v_xs_2030_, lean_object* v_i_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2026_, v_args_2027_, v_f_2029_, v_xs_2030_, v_i_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_2040_, lean_object* v_args_2041_, lean_object* v___h_2042_, lean_object* v_f_2043_, lean_object* v_xs_2044_, lean_object* v_i_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2040_, v_args_2041_, v___h_2042_, v_f_2043_, v_xs_2044_, v_i_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v_res_2053_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_2056_ = lean_unsigned_to_nat(40u);
v___x_2057_ = lean_unsigned_to_nat(251u);
v___x_2058_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_2060_ = l_mkPanicMessageWithDecl(v___x_2059_, v___x_2058_, v___x_2057_, v___x_2056_, v___x_2055_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
if (lean_obj_tag(v_x_2062_) == 5)
{
lean_object* v_fn_2072_; lean_object* v_arg_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_fn_2072_ = lean_ctor_get(v_x_2062_, 0);
lean_inc_ref(v_fn_2072_);
v_arg_2073_ = lean_ctor_get(v_x_2062_, 1);
lean_inc_ref(v_arg_2073_);
lean_dec_ref(v_x_2062_);
v___x_2074_ = lean_array_set(v_x_2063_, v_x_2064_, v_arg_2073_);
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = lean_nat_sub(v_x_2064_, v___x_2075_);
lean_dec(v_x_2064_);
v_x_2062_ = v_fn_2072_;
v_x_2063_ = v___x_2074_;
v_x_2064_ = v___x_2076_;
goto _start;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
lean_dec(v_x_2064_);
v___x_2078_ = lean_array_get_size(v_x_2063_);
v___x_2079_ = lean_array_get_size(v_varDeps_2061_);
v___x_2080_ = lean_nat_dec_eq(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v_x_2063_);
lean_dec_ref(v_x_2062_);
lean_dec_ref(v_varDeps_2061_);
v___x_2081_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2082_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_2081_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2085_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2061_, v_x_2063_, v_x_2062_, v___x_2084_, v___x_2083_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2086_, v_x_2087_, v_x_2088_, v_x_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
return v_res_2097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2098_; lean_object* v_dummy_2099_; 
v___x_2098_ = lean_box(0);
v_dummy_2099_ = l_Lean_Expr_sort___override(v___x_2098_);
return v_dummy_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2100_, lean_object* v_varDeps_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_dummy_2109_; lean_object* v_nargs_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_dummy_2109_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2110_ = l_Lean_Expr_getAppNumArgs(v_e_2100_);
lean_inc(v_nargs_2110_);
v___x_2111_ = lean_mk_array(v_nargs_2110_, v_dummy_2109_);
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_nat_sub(v_nargs_2110_, v___x_2112_);
lean_dec(v_nargs_2110_);
v___x_2114_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2101_, v_e_2100_, v___x_2111_, v___x_2113_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2115_, lean_object* v_varDeps_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2115_, v_varDeps_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2125_, lean_object* v_b_2126_){
_start:
{
lean_object* v_snd_2128_; lean_object* v_fst_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2162_; 
v_snd_2128_ = lean_ctor_get(v_b_2126_, 1);
v_fst_2129_ = lean_ctor_get(v_b_2126_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_b_2126_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2131_ = v_b_2126_;
v_isShared_2132_ = v_isSharedCheck_2162_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_snd_2128_);
lean_inc(v_fst_2129_);
lean_dec(v_b_2126_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2162_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_fst_2133_; lean_object* v_snd_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2161_; 
v_fst_2133_ = lean_ctor_get(v_snd_2128_, 0);
v_snd_2134_ = lean_ctor_get(v_snd_2128_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_snd_2128_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2136_ = v_snd_2128_;
v_isShared_2137_ = v_isSharedCheck_2161_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snd_2134_);
lean_inc(v_fst_2133_);
lean_dec(v_snd_2128_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2161_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_nat_dec_lt(v___x_2138_, v_fst_2133_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2141_; 
if (v_isShared_2137_ == 0)
{
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_fst_2133_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_snd_2134_);
v___x_2141_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v___x_2141_);
v___x_2143_ = v___x_2131_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_fst_2129_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_sub(v_fst_2133_, v___x_2147_);
lean_dec(v_fst_2133_);
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_array_get_borrowed(v___x_2149_, v_argUnivs_2125_, v___x_2148_);
lean_inc(v___x_2150_);
v___x_2151_ = l_Lean_mkLevelIMax_x27(v___x_2150_, v_fst_2129_);
v___x_2152_ = l_Lean_Level_normalize(v___x_2151_);
lean_dec(v___x_2151_);
lean_inc(v___x_2152_);
v___x_2153_ = lean_array_push(v_snd_2134_, v___x_2152_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v___x_2153_);
lean_ctor_set(v___x_2136_, 0, v___x_2148_);
v___x_2155_ = v___x_2136_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v___x_2155_);
lean_ctor_set(v___x_2131_, 0, v___x_2152_);
v___x_2157_ = v___x_2131_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
v_b_2126_ = v___x_2157_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2163_, v_b_2164_);
lean_dec_ref(v_argUnivs_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2169_, lean_object* v_argUnivs_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
if (lean_obj_tag(v_type_2169_) == 7)
{
lean_object* v_binderType_2178_; lean_object* v_body_2179_; lean_object* v___x_2180_; 
v_binderType_2178_ = lean_ctor_get(v_type_2169_, 1);
lean_inc_ref(v_binderType_2178_);
v_body_2179_ = lean_ctor_get(v_type_2169_, 2);
lean_inc_ref(v_body_2179_);
lean_dec_ref(v_type_2169_);
lean_inc(v_a_2176_);
lean_inc_ref(v_a_2175_);
lean_inc(v_a_2174_);
lean_inc_ref(v_a_2173_);
v___x_2180_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2178_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = lean_array_push(v_argUnivs_2170_, v_a_2181_);
v_type_2169_ = v_body_2179_;
v_argUnivs_2170_ = v___x_2182_;
goto _start;
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_body_2179_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec_ref(v_argUnivs_2170_);
v_a_2184_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2180_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2180_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2169_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
v___x_2194_ = lean_array_get_size(v_argUnivs_2170_);
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2193_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2170_, v___x_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2217_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2217_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2217_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_snd_2203_; lean_object* v_snd_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2215_; 
v_snd_2203_ = lean_ctor_get(v_a_2199_, 1);
lean_inc(v_snd_2203_);
lean_dec(v_a_2199_);
v_snd_2204_ = lean_ctor_get(v_snd_2203_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_snd_2203_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v_snd_2203_, 0);
lean_dec(v_unused_2216_);
v___x_2206_ = v_snd_2203_;
v_isShared_2207_ = v_isSharedCheck_2215_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_snd_2204_);
lean_dec(v_snd_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2215_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = l_Array_reverse___redArg(v_snd_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 1, v___x_2208_);
lean_ctor_set(v___x_2206_, 0, v_argUnivs_2170_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_argUnivs_2170_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2210_);
v___x_2212_ = v___x_2201_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
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
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_argUnivs_2170_);
v_a_2218_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2198_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2198_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_argUnivs_2170_);
v_a_2226_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2192_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2192_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2234_, lean_object* v_argUnivs_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2234_, v_argUnivs_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2244_, v_b_2245_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2254_, lean_object* v_b_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2254_, v_b_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_argUnivs_2254_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2273_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2264_, v___x_2272_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2283_, lean_object* v_argUnivs_2284_, lean_object* v_declName_2285_, lean_object* v_fType_2286_, lean_object* v_i_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v_00_u03b1_2290_; lean_object* v_00_u03b2_2291_; lean_object* v_u_2292_; lean_object* v_v_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2289_ = lean_box(0);
v_00_u03b1_2290_ = l_Lean_Expr_bindingDomain_x21(v_fType_2286_);
v_00_u03b2_2291_ = l_Lean_Expr_bindingBody_x21(v_fType_2286_);
v_u_2292_ = lean_array_get_borrowed(v___x_2289_, v_argUnivs_2284_, v_i_2287_);
v_v_2293_ = lean_array_get_borrowed(v___x_2289_, v_fnUnivs_2283_, v_i_2287_);
v___x_2294_ = lean_box(0);
lean_inc(v_v_2293_);
v___x_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_v_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
lean_inc(v_u_2292_);
v___x_2296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2296_, 0, v_u_2292_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Lean_mkConst(v_declName_2285_, v___x_2296_);
v___x_2298_ = l_Lean_mkAppB(v___x_2297_, v_00_u03b1_2290_, v_00_u03b2_2291_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2300_, lean_object* v_argUnivs_2301_, lean_object* v_declName_2302_, lean_object* v_fType_2303_, lean_object* v_i_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2300_, v_argUnivs_2301_, v_declName_2302_, v_fType_2303_, v_i_2304_);
lean_dec(v_i_2304_);
lean_dec_ref(v_fType_2303_);
lean_dec_ref(v_argUnivs_2301_);
lean_dec_ref(v_fnUnivs_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2307_, lean_object* v_argUnivs_2308_, lean_object* v_declName_2309_, lean_object* v_fType_2310_, lean_object* v_i_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2307_, v_argUnivs_2308_, v_declName_2309_, v_fType_2310_, v_i_2311_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2320_, lean_object* v_argUnivs_2321_, lean_object* v_declName_2322_, lean_object* v_fType_2323_, lean_object* v_i_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2320_, v_argUnivs_2321_, v_declName_2322_, v_fType_2323_, v_i_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_i_2324_);
lean_dec_ref(v_fType_2323_);
lean_dec_ref(v_argUnivs_2321_);
lean_dec_ref(v_fnUnivs_2320_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2333_, lean_object* v_a_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___y_2343_; lean_object* v___x_2346_; uint8_t v_debug_2347_; 
v___x_2346_ = lean_st_ref_get(v___y_2336_);
v_debug_2347_ = lean_ctor_get_uint8(v___x_2346_, sizeof(void*)*7);
lean_dec(v___x_2346_);
if (v_debug_2347_ == 0)
{
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v___y_2335_);
v___y_2343_ = v___y_2336_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2348_; 
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc(v___y_2336_);
lean_inc_ref(v___y_2335_);
lean_inc_ref(v_f_2333_);
v___x_2348_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2333_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2349_; 
lean_dec_ref(v___x_2348_);
lean_inc(v___y_2336_);
lean_inc_ref(v_a_2334_);
v___x_2349_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_dec_ref(v___x_2349_);
v___y_2343_ = v___y_2336_;
goto v___jp_2342_;
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v___y_2336_);
lean_dec_ref(v_a_2334_);
lean_dec_ref(v_f_2333_);
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec_ref(v_a_2334_);
lean_dec_ref(v_f_2333_);
v_a_2358_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2348_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2348_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
v___jp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = l_Lean_Expr_app___override(v_f_2333_, v_a_2334_);
v___x_2345_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2344_, v___y_2343_);
lean_dec(v___y_2343_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2366_, lean_object* v_a_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2366_, v_a_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2376_, lean_object* v_a_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2376_, v_a_2377_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2389_, lean_object* v_a_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2389_, v_a_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
return v_res_2401_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_14459__overap_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_14459__overap_2415_ = lean_panic_fn(v___x_2414_, v_msg_2403_);
v___x_2416_ = lean_apply_10(v___x_14459__overap_2415_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v_res_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__8(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_2442_ = lean_unsigned_to_nat(11u);
v___x_2443_ = lean_unsigned_to_nat(345u);
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7));
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_2446_ = l_mkPanicMessageWithDecl(v___x_2445_, v___x_2444_, v___x_2443_, v___x_2442_, v___x_2441_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2447_, lean_object* v_fnUnivs_2448_, lean_object* v_argUnivs_2449_, lean_object* v_simpBody_2450_, lean_object* v_e_2451_, lean_object* v_i_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
switch(lean_obj_tag(v_e_2451_))
{
case 5:
{
lean_object* v_fn_2463_; lean_object* v_arg_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_fn_2463_ = lean_ctor_get(v_e_2451_, 0);
lean_inc_ref(v_fn_2463_);
v_arg_2464_ = lean_ctor_get(v_e_2451_, 1);
lean_inc_ref(v_arg_2464_);
lean_dec_ref(v_e_2451_);
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_nat_sub(v_i_2452_, v___x_2465_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
lean_inc(v_a_2457_);
lean_inc_ref(v_a_2456_);
lean_inc(v_a_2455_);
lean_inc_ref(v_a_2454_);
lean_inc(v_a_2453_);
lean_inc_ref(v_fn_2463_);
v___x_2467_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2447_, v_fnUnivs_2448_, v_argUnivs_2449_, v_simpBody_2450_, v_fn_2463_, v___x_2466_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v___x_2466_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2573_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2573_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2573_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2572_; 
v_fst_2472_ = lean_ctor_get(v_a_2468_, 0);
v_snd_2473_ = lean_ctor_get(v_a_2468_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_a_2468_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2475_ = v_a_2468_;
v_isShared_2476_ = v_isSharedCheck_2572_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_snd_2473_);
lean_inc(v_fst_2472_);
lean_dec(v_a_2468_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2572_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_r_2478_; lean_object* v___x_2486_; 
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
lean_inc(v_a_2457_);
lean_inc_ref(v_a_2456_);
lean_inc_ref(v_arg_2464_);
v___x_2486_ = lean_sym_simp(v_arg_2464_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2486_) == 0)
{
if (lean_obj_tag(v_fst_2472_) == 0)
{
lean_object* v_a_2487_; 
lean_dec_ref(v_fst_2472_);
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2486_);
if (lean_obj_tag(v_a_2487_) == 0)
{
lean_object* v___x_2488_; 
lean_dec_ref(v_a_2487_);
lean_dec_ref(v_arg_2464_);
lean_dec_ref(v_fn_2463_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0));
v_r_2478_ = v___x_2488_;
goto v___jp_2477_;
}
else
{
lean_object* v_e_x27_2489_; lean_object* v_proof_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2512_; 
v_e_x27_2489_ = lean_ctor_get(v_a_2487_, 0);
v_proof_2490_ = lean_ctor_get(v_a_2487_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2487_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2492_ = v_a_2487_;
v_isShared_2493_ = v_isSharedCheck_2512_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_proof_2490_);
lean_inc(v_e_x27_2489_);
lean_dec(v_a_2487_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2512_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; 
lean_inc_ref(v_e_x27_2489_);
lean_inc_ref(v_fn_2463_);
v___x_2494_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2463_, v_e_x27_2489_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2));
v___x_2497_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2448_, v_argUnivs_2449_, v___x_2496_, v_snd_2473_, v_i_2452_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = l_Lean_mkApp4(v_a_2498_, v_arg_2464_, v_e_x27_2489_, v_fn_2463_, v_proof_2490_);
v___x_2500_ = 0;
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2499_);
lean_ctor_set(v___x_2492_, 0, v_a_2495_);
v___x_2502_ = v___x_2492_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2495_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2499_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*2, v___x_2500_);
v_r_2478_ = v___x_2502_;
goto v___jp_2477_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_del_object(v___x_2492_);
lean_dec_ref(v_proof_2490_);
lean_dec_ref(v_e_x27_2489_);
lean_del_object(v___x_2475_);
lean_dec(v_snd_2473_);
lean_del_object(v___x_2470_);
lean_dec_ref(v_arg_2464_);
lean_dec_ref(v_fn_2463_);
v_a_2504_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2494_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2494_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
else
{
lean_object* v_a_2513_; 
v_a_2513_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2486_);
if (lean_obj_tag(v_a_2513_) == 0)
{
lean_object* v_e_x27_2514_; lean_object* v_proof_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v_a_2513_);
v_e_x27_2514_ = lean_ctor_get(v_fst_2472_, 0);
v_proof_2515_ = lean_ctor_get(v_fst_2472_, 1);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_fst_2472_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2517_ = v_fst_2472_;
v_isShared_2518_ = v_isSharedCheck_2537_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_proof_2515_);
lean_inc(v_e_x27_2514_);
lean_dec(v_fst_2472_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2537_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; 
lean_inc_ref(v_arg_2464_);
lean_inc_ref(v_e_x27_2514_);
v___x_2519_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2514_, v_arg_2464_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_a_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; lean_object* v___x_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref(v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4));
v___x_2522_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2448_, v_argUnivs_2449_, v___x_2521_, v_snd_2473_, v_i_2452_);
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = l_Lean_mkApp4(v_a_2523_, v_fn_2463_, v_e_x27_2514_, v_proof_2515_, v_arg_2464_);
v___x_2525_ = 0;
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v___x_2524_);
lean_ctor_set(v___x_2517_, 0, v_a_2520_);
v___x_2527_ = v___x_2517_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2520_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2524_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2, v___x_2525_);
v_r_2478_ = v___x_2527_;
goto v___jp_2477_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_del_object(v___x_2517_);
lean_dec_ref(v_proof_2515_);
lean_dec_ref(v_e_x27_2514_);
lean_del_object(v___x_2475_);
lean_dec(v_snd_2473_);
lean_del_object(v___x_2470_);
lean_dec_ref(v_arg_2464_);
lean_dec_ref(v_fn_2463_);
v_a_2529_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2519_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2519_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2538_; lean_object* v_proof_2539_; lean_object* v_e_x27_2540_; lean_object* v_proof_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2563_; 
v_e_x27_2538_ = lean_ctor_get(v_fst_2472_, 0);
lean_inc_ref(v_e_x27_2538_);
v_proof_2539_ = lean_ctor_get(v_fst_2472_, 1);
lean_inc_ref(v_proof_2539_);
lean_dec_ref(v_fst_2472_);
v_e_x27_2540_ = lean_ctor_get(v_a_2513_, 0);
v_proof_2541_ = lean_ctor_get(v_a_2513_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_a_2513_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2543_ = v_a_2513_;
v_isShared_2544_ = v_isSharedCheck_2563_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_proof_2541_);
lean_inc(v_e_x27_2540_);
lean_dec(v_a_2513_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2563_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; 
lean_inc_ref(v_e_x27_2540_);
lean_inc_ref(v_e_x27_2538_);
v___x_2545_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2538_, v_e_x27_2540_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_a_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2553_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2548_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2448_, v_argUnivs_2449_, v___x_2547_, v_snd_2473_, v_i_2452_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = l_Lean_mkApp6(v_a_2549_, v_fn_2463_, v_e_x27_2538_, v_arg_2464_, v_e_x27_2540_, v_proof_2539_, v_proof_2541_);
v___x_2551_ = 0;
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v___x_2550_);
lean_ctor_set(v___x_2543_, 0, v_a_2546_);
v___x_2553_ = v___x_2543_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2546_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2550_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*2, v___x_2551_);
v_r_2478_ = v___x_2553_;
goto v___jp_2477_;
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_proof_2541_);
lean_dec_ref(v_e_x27_2540_);
lean_dec_ref(v_proof_2539_);
lean_dec_ref(v_e_x27_2538_);
lean_del_object(v___x_2475_);
lean_dec(v_snd_2473_);
lean_del_object(v___x_2470_);
lean_dec_ref(v_arg_2464_);
lean_dec_ref(v_fn_2463_);
v_a_2555_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2545_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2545_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_del_object(v___x_2475_);
lean_dec(v_snd_2473_);
lean_dec(v_fst_2472_);
lean_del_object(v___x_2470_);
lean_dec_ref(v_arg_2464_);
lean_dec_ref(v_fn_2463_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
v_a_2564_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2486_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2486_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
v___jp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = l_Lean_Expr_bindingBody_x21(v_snd_2473_);
lean_dec(v_snd_2473_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v___x_2479_);
lean_ctor_set(v___x_2475_, 0, v_r_2478_);
v___x_2481_ = v___x_2475_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_r_2478_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2483_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2481_);
v___x_2483_ = v___x_2470_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2464_);
lean_dec_ref(v_fn_2463_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
return v___x_2467_;
}
}
case 6:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_apply_11(v_simpBody_2450_, v_e_2451_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, lean_box(0));
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2583_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_a_2575_);
lean_ctor_set(v___x_2579_, 1, v_fType_2447_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2579_);
v___x_2581_ = v___x_2577_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v_fType_2447_);
v_a_2584_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2574_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2574_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
default: 
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v_e_2451_);
lean_dec_ref(v_simpBody_2450_);
lean_dec_ref(v_fType_2447_);
v___x_2592_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__8, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__8);
v___x_2593_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2592_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2594_, lean_object* v_fnUnivs_2595_, lean_object* v_argUnivs_2596_, lean_object* v_simpBody_2597_, lean_object* v_e_2598_, lean_object* v_i_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2594_, v_fnUnivs_2595_, v_argUnivs_2596_, v_simpBody_2597_, v_e_2598_, v_i_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_i_2599_);
lean_dec_ref(v_argUnivs_2596_);
lean_dec_ref(v_fnUnivs_2595_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2611_, lean_object* v_fType_2612_, lean_object* v_fnUnivs_2613_, lean_object* v_argUnivs_2614_, lean_object* v_simpBody_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_numArgs_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_numArgs_2626_ = lean_array_get_size(v_argUnivs_2614_);
v___x_2627_ = lean_unsigned_to_nat(1u);
v___x_2628_ = lean_nat_sub(v_numArgs_2626_, v___x_2627_);
v___x_2629_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2612_, v_fnUnivs_2613_, v_argUnivs_2614_, v_simpBody_2615_, v_e_2611_, v___x_2628_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v___x_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2638_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v_fst_2634_; lean_object* v___x_2636_; 
v_fst_2634_ = lean_ctor_get(v_a_2630_, 0);
lean_inc(v_fst_2634_);
lean_dec(v_a_2630_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v_fst_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_fst_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2629_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2629_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2647_, lean_object* v_fType_2648_, lean_object* v_fnUnivs_2649_, lean_object* v_argUnivs_2650_, lean_object* v_simpBody_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2647_, v_fType_2648_, v_fnUnivs_2649_, v_argUnivs_2650_, v_simpBody_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec_ref(v_argUnivs_2650_);
lean_dec_ref(v_fnUnivs_2649_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2667_, lean_object* v_simpBody_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; 
lean_inc(v_a_2677_);
lean_inc_ref(v_a_2676_);
lean_inc(v_a_2675_);
lean_inc_ref(v_a_2674_);
lean_inc(v_a_2673_);
lean_inc_ref(v_a_2672_);
lean_inc_ref(v_e_2667_);
v___x_2679_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2667_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_00_u03b1_2681_; lean_object* v_u_2682_; lean_object* v_e_2683_; lean_object* v_h_2684_; lean_object* v_varDeps_2685_; lean_object* v_fType_2686_; lean_object* v___x_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
v_00_u03b1_2681_ = lean_ctor_get(v_a_2680_, 0);
lean_inc_ref(v_00_u03b1_2681_);
v_u_2682_ = lean_ctor_get(v_a_2680_, 1);
lean_inc(v_u_2682_);
v_e_2683_ = lean_ctor_get(v_a_2680_, 2);
lean_inc_ref(v_e_2683_);
v_h_2684_ = lean_ctor_get(v_a_2680_, 3);
lean_inc_ref(v_h_2684_);
v_varDeps_2685_ = lean_ctor_get(v_a_2680_, 4);
lean_inc_ref(v_varDeps_2685_);
v_fType_2686_ = lean_ctor_get(v_a_2680_, 5);
lean_inc_ref(v_fType_2686_);
lean_dec(v_a_2680_);
lean_inc(v_a_2677_);
lean_inc_ref(v_a_2676_);
lean_inc(v_a_2675_);
lean_inc_ref(v_a_2674_);
lean_inc_ref(v_fType_2686_);
v___x_2687_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2686_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v_argUnivs_2689_; lean_object* v_fnUnivs_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2756_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref(v___x_2687_);
v_argUnivs_2689_ = lean_ctor_get(v_a_2688_, 0);
v_fnUnivs_2690_ = lean_ctor_get(v_a_2688_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2692_ = v_a_2688_;
v_isShared_2693_ = v_isSharedCheck_2756_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_fnUnivs_2690_);
lean_inc(v_argUnivs_2689_);
lean_dec(v_a_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2756_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; 
lean_inc(v_a_2677_);
lean_inc_ref(v_a_2676_);
lean_inc(v_a_2675_);
lean_inc_ref(v_a_2674_);
lean_inc(v_a_2673_);
lean_inc_ref(v_a_2672_);
lean_inc_ref(v_e_2683_);
v___x_2694_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2683_, v_fType_2686_, v_fnUnivs_2690_, v_argUnivs_2689_, v_simpBody_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec_ref(v_argUnivs_2689_);
lean_dec_ref(v_fnUnivs_2690_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2747_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2747_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2747_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
if (lean_obj_tag(v_a_2695_) == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec_ref(v_a_2695_);
lean_del_object(v___x_2692_);
lean_dec_ref(v_varDeps_2685_);
lean_dec_ref(v_h_2684_);
lean_dec_ref(v_e_2683_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec_ref(v_e_2667_);
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0));
v___x_2700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v_00_u03b1_2681_);
lean_ctor_set(v___x_2700_, 2, v_u_2682_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2700_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
else
{
lean_object* v_e_x27_2704_; lean_object* v_proof_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2746_; 
lean_del_object(v___x_2697_);
v_e_x27_2704_ = lean_ctor_get(v_a_2695_, 0);
v_proof_2705_ = lean_ctor_get(v_a_2695_, 1);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_a_2695_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2707_ = v_a_2695_;
v_isShared_2708_ = v_isSharedCheck_2746_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_proof_2705_);
lean_inc(v_e_x27_2704_);
lean_dec(v_a_2695_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2746_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2710_ = lean_box(0);
lean_inc(v_u_2682_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 1);
lean_ctor_set(v___x_2692_, 1, v___x_2710_);
lean_ctor_set(v___x_2692_, 0, v_u_2682_);
v___x_2712_ = v___x_2692_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_u_2682_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_inc_ref(v___x_2712_);
v___x_2713_ = l_Lean_mkConst(v___x_2709_, v___x_2712_);
lean_inc_ref(v_e_x27_2704_);
lean_inc_ref(v_e_2667_);
lean_inc_ref(v_00_u03b1_2681_);
lean_inc_ref(v___x_2713_);
v___x_2714_ = l_Lean_mkApp6(v___x_2713_, v_00_u03b1_2681_, v_e_2667_, v_e_2683_, v_e_x27_2704_, v_h_2684_, v_proof_2705_);
lean_inc_ref(v_e_x27_2704_);
v___x_2715_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2704_, v_varDeps_2685_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2736_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2736_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2736_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2730_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2712_);
v___x_2721_ = l_Lean_mkConst(v___x_2720_, v___x_2712_);
lean_inc(v_a_2716_);
lean_inc_ref(v_e_x27_2704_);
lean_inc_ref(v_00_u03b1_2681_);
v___x_2722_ = l_Lean_mkApp3(v___x_2721_, v_00_u03b1_2681_, v_e_x27_2704_, v_a_2716_);
v___x_2723_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2724_ = l_Lean_mkConst(v___x_2723_, v___x_2712_);
lean_inc_ref(v_e_x27_2704_);
lean_inc_ref(v_00_u03b1_2681_);
v___x_2725_ = l_Lean_mkAppB(v___x_2724_, v_00_u03b1_2681_, v_e_x27_2704_);
v___x_2726_ = l_Lean_Meta_mkExpectedPropHint(v___x_2725_, v___x_2722_);
lean_inc(v_a_2716_);
lean_inc_ref(v_00_u03b1_2681_);
v___x_2727_ = l_Lean_mkApp6(v___x_2713_, v_00_u03b1_2681_, v_e_2667_, v_e_x27_2704_, v_a_2716_, v___x_2714_, v___x_2726_);
v___x_2728_ = 0;
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___x_2727_);
lean_ctor_set(v___x_2707_, 0, v_a_2716_);
v___x_2730_ = v___x_2707_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2716_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2727_);
v___x_2730_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*2, v___x_2728_);
v___x_2731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
lean_ctor_set(v___x_2731_, 1, v_00_u03b1_2681_);
lean_ctor_set(v___x_2731_, 2, v_u_2682_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2731_);
v___x_2733_ = v___x_2718_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___x_2714_);
lean_dec_ref(v___x_2713_);
lean_dec_ref(v___x_2712_);
lean_del_object(v___x_2707_);
lean_dec_ref(v_e_x27_2704_);
lean_dec(v_u_2682_);
lean_dec_ref(v_00_u03b1_2681_);
lean_dec_ref(v_e_2667_);
v_a_2737_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2715_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2715_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
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
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_del_object(v___x_2692_);
lean_dec_ref(v_varDeps_2685_);
lean_dec_ref(v_h_2684_);
lean_dec_ref(v_e_2683_);
lean_dec(v_u_2682_);
lean_dec_ref(v_00_u03b1_2681_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec_ref(v_e_2667_);
v_a_2748_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2694_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2694_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_fType_2686_);
lean_dec_ref(v_varDeps_2685_);
lean_dec_ref(v_h_2684_);
lean_dec_ref(v_e_2683_);
lean_dec(v_u_2682_);
lean_dec_ref(v_00_u03b1_2681_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_simpBody_2668_);
lean_dec_ref(v_e_2667_);
v_a_2757_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2687_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2687_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_simpBody_2668_);
lean_dec_ref(v_e_2667_);
v_a_2765_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2679_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2679_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2773_, lean_object* v_simpBody_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2773_, v_simpBody_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2786_, lean_object* v_simpBody_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2786_, v_simpBody_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2807_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_result_2803_; lean_object* v___x_2805_; 
v_result_2803_ = lean_ctor_get(v_a_2799_, 0);
lean_inc_ref(v_result_2803_);
lean_dec(v_a_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_result_2803_);
v___x_2805_ = v___x_2801_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_result_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2798_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2798_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2816_, lean_object* v_simpBody_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2816_, v_simpBody_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2829_, lean_object* v_simpBody_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2841_; 
lean_inc(v_a_2839_);
lean_inc_ref(v_a_2838_);
lean_inc(v_a_2837_);
lean_inc_ref(v_a_2836_);
lean_inc_ref(v_e_u2081_2829_);
v___x_2841_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2829_, v_simpBody_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v_result_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v_result_2843_ = lean_ctor_get(v_a_2842_, 0);
lean_inc_ref(v_result_2843_);
if (lean_obj_tag(v_result_2843_) == 0)
{
lean_object* v_00_u03b1_2844_; lean_object* v_u_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v_result_2843_);
v_00_u03b1_2844_ = lean_ctor_get(v_a_2842_, 1);
lean_inc_ref(v_00_u03b1_2844_);
v_u_2845_ = lean_ctor_get(v_a_2842_, 2);
lean_inc(v_u_2845_);
lean_dec(v_a_2842_);
lean_inc_ref(v_e_u2081_2829_);
v___x_2846_ = l_Lean_Meta_zetaUnused(v_e_u2081_2829_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2865_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2865_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2865_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint8_t v___x_2851_; 
v___x_2851_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_u2081_2829_, v_a_2847_);
lean_dec_ref(v_e_u2081_2829_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2852_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_u_2845_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_mkConst(v___x_2852_, v___x_2854_);
lean_inc(v_a_2847_);
v___x_2856_ = l_Lean_mkAppB(v___x_2855_, v_00_u03b1_2844_, v_a_2847_);
v___x_2857_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2857_, 0, v_a_2847_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*2, v___x_2851_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2857_);
v___x_2859_ = v___x_2849_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_dec(v_a_2847_);
lean_dec(v_u_2845_);
lean_dec_ref(v_00_u03b1_2844_);
v___x_2861_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0));
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2861_);
v___x_2863_ = v___x_2849_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_u_2845_);
lean_dec_ref(v_00_u03b1_2844_);
lean_dec_ref(v_e_u2081_2829_);
v_a_2866_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2846_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2846_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_00_u03b1_2874_; lean_object* v_u_2875_; lean_object* v_e_x27_2876_; lean_object* v_proof_2877_; lean_object* v___x_2878_; 
v_00_u03b1_2874_ = lean_ctor_get(v_a_2842_, 1);
lean_inc_ref(v_00_u03b1_2874_);
v_u_2875_ = lean_ctor_get(v_a_2842_, 2);
lean_inc(v_u_2875_);
lean_dec(v_a_2842_);
v_e_x27_2876_ = lean_ctor_get(v_result_2843_, 0);
v_proof_2877_ = lean_ctor_get(v_result_2843_, 1);
lean_inc_ref(v_e_x27_2876_);
v___x_2878_ = l_Lean_Meta_zetaUnused(v_e_x27_2876_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2907_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2907_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2907_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___x_2883_; 
v___x_2883_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_2876_, v_a_2879_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2901_; 
lean_inc_ref(v_proof_2877_);
lean_inc_ref(v_e_x27_2876_);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_result_2843_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; lean_object* v_unused_2903_; 
v_unused_2902_ = lean_ctor_get(v_result_2843_, 1);
lean_dec(v_unused_2902_);
v_unused_2903_ = lean_ctor_get(v_result_2843_, 0);
lean_dec(v_unused_2903_);
v___x_2885_ = v_result_2843_;
v_isShared_2886_ = v_isSharedCheck_2901_;
goto v_resetjp_2884_;
}
else
{
lean_dec(v_result_2843_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2901_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_u_2875_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
lean_inc_ref(v___x_2889_);
v___x_2890_ = l_Lean_mkConst(v___x_2887_, v___x_2889_);
v___x_2891_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2892_ = l_Lean_mkConst(v___x_2891_, v___x_2889_);
lean_inc(v_a_2879_);
lean_inc_ref(v_00_u03b1_2874_);
v___x_2893_ = l_Lean_mkAppB(v___x_2892_, v_00_u03b1_2874_, v_a_2879_);
lean_inc(v_a_2879_);
v___x_2894_ = l_Lean_mkApp6(v___x_2890_, v_00_u03b1_2874_, v_e_u2081_2829_, v_e_x27_2876_, v_a_2879_, v_proof_2877_, v___x_2893_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2894_);
lean_ctor_set(v___x_2885_, 0, v_a_2879_);
v___x_2896_ = v___x_2885_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2879_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*2, v___x_2883_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2896_);
v___x_2898_ = v___x_2881_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v___x_2905_; 
lean_dec(v_a_2879_);
lean_dec(v_u_2875_);
lean_dec_ref(v_00_u03b1_2874_);
lean_dec_ref(v_e_u2081_2829_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v_result_2843_);
v___x_2905_ = v___x_2881_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_result_2843_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_u_2875_);
lean_dec_ref(v_00_u03b1_2874_);
lean_dec_ref(v_result_2843_);
lean_dec_ref(v_e_u2081_2829_);
v_a_2908_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2878_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2878_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec_ref(v_e_u2081_2829_);
v_a_2916_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2841_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2841_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_2924_, lean_object* v_simpBody_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_2924_, v_simpBody_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_2937_, lean_object* v_e_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
uint8_t v___x_2949_; 
v___x_2949_ = l_Lean_Expr_letNondep_x21(v_e_2938_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_e_2938_);
lean_dec_ref(v_simpBody_2937_);
v___x_2950_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2950_, 0, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_2938_, v_simpBody_2937_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_2953_, lean_object* v_e_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_2953_, v_e_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_2979_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_2978_, v_e_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
return v_res_2991_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HaveTelescope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HaveTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default = _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default);
l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult = _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_HaveTelescope(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HaveTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Have(builtin);
}
#ifdef __cplusplus
}
#endif
