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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
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
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1;
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0;
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congrFun'"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 239, 156, 219, 118, 185, 235, 192)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.simpBetaApp.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7;
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
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object* v_msg_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_panic_fn_borrowed(v___x_52_, v_msg_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_57_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2));
v___x_58_ = lean_unsigned_to_nat(13u);
v___x_59_ = lean_unsigned_to_nat(227u);
v___x_60_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1));
v___x_61_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0));
v___x_62_ = l_mkPanicMessageWithDecl(v___x_61_, v___x_60_, v___x_59_, v___x_58_, v___x_57_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object* v_t_63_, lean_object* v_k_64_){
_start:
{
if (lean_obj_tag(v_t_63_) == 0)
{
lean_object* v_k_65_; lean_object* v_v_66_; lean_object* v_l_67_; lean_object* v_r_68_; uint8_t v___x_69_; 
v_k_65_ = lean_ctor_get(v_t_63_, 1);
v_v_66_ = lean_ctor_get(v_t_63_, 2);
v_l_67_ = lean_ctor_get(v_t_63_, 3);
v_r_68_ = lean_ctor_get(v_t_63_, 4);
v___x_69_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_64_, v_k_65_);
switch(v___x_69_)
{
case 0:
{
v_t_63_ = v_l_67_;
goto _start;
}
case 1:
{
lean_inc(v_v_66_);
return v_v_66_;
}
default: 
{
v_t_63_ = v_r_68_;
goto _start;
}
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3);
v___x_73_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object* v_t_74_, lean_object* v_k_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_t_74_, v_k_75_);
lean_dec(v_k_75_);
lean_dec(v_t_74_);
return v_res_76_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object* v_fvarIdToPos_77_, lean_object* v_fvarId_u2081_78_, lean_object* v_fvarId_u2082_79_){
_start:
{
lean_object* v_pos_u2081_80_; lean_object* v_pos_u2082_81_; uint8_t v___x_82_; 
v_pos_u2081_80_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_77_, v_fvarId_u2081_78_);
v_pos_u2082_81_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_77_, v_fvarId_u2082_79_);
v___x_82_ = lean_nat_dec_lt(v_pos_u2081_80_, v_pos_u2082_81_);
lean_dec(v_pos_u2082_81_);
lean_dec(v_pos_u2081_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object* v_fvarIdToPos_83_, lean_object* v_fvarId_u2081_84_, lean_object* v_fvarId_u2082_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_83_, v_fvarId_u2081_84_, v_fvarId_u2082_85_);
lean_dec(v_fvarId_u2082_85_);
lean_dec(v_fvarId_u2081_84_);
lean_dec(v_fvarIdToPos_83_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(lean_object* v_fvarIdToPos_88_, lean_object* v_hi_89_, lean_object* v_pivot_90_, lean_object* v_as_91_, lean_object* v_i_92_, lean_object* v_k_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_lt(v_k_93_, v_hi_89_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_k_93_);
v___x_95_ = lean_array_fswap(v_as_91_, v_i_92_, v_hi_89_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_i_92_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v_pos_u2081_98_; lean_object* v_pos_u2082_99_; uint8_t v___x_100_; 
v___x_97_ = lean_array_fget_borrowed(v_as_91_, v_k_93_);
v_pos_u2081_98_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_88_, v___x_97_);
v_pos_u2082_99_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_88_, v_pivot_90_);
v___x_100_ = lean_nat_dec_lt(v_pos_u2081_98_, v_pos_u2082_99_);
lean_dec(v_pos_u2082_99_);
lean_dec(v_pos_u2081_98_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_k_93_, v___x_101_);
lean_dec(v_k_93_);
v_k_93_ = v___x_102_;
goto _start;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_array_fswap(v_as_91_, v_i_92_, v_k_93_);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_i_92_, v___x_105_);
lean_dec(v_i_92_);
v___x_107_ = lean_nat_add(v_k_93_, v___x_105_);
lean_dec(v_k_93_);
v_as_91_ = v___x_104_;
v_i_92_ = v___x_106_;
v_k_93_ = v___x_107_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg___boxed(lean_object* v_fvarIdToPos_109_, lean_object* v_hi_110_, lean_object* v_pivot_111_, lean_object* v_as_112_, lean_object* v_i_113_, lean_object* v_k_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_109_, v_hi_110_, v_pivot_111_, v_as_112_, v_i_113_, v_k_114_);
lean_dec(v_pivot_111_);
lean_dec(v_hi_110_);
lean_dec(v_fvarIdToPos_109_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object* v_fvarIdToPos_116_, lean_object* v_n_117_, lean_object* v_as_118_, lean_object* v_lo_119_, lean_object* v_hi_120_){
_start:
{
lean_object* v___y_122_; uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_lt(v_lo_119_, v_hi_120_);
if (v___x_132_ == 0)
{
lean_dec(v_lo_119_);
return v_as_118_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_mid_135_; lean_object* v___y_137_; lean_object* v___y_143_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_133_ = lean_nat_add(v_lo_119_, v_hi_120_);
v___x_134_ = lean_unsigned_to_nat(1u);
v_mid_135_ = lean_nat_shiftr(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_148_ = lean_array_fget_borrowed(v_as_118_, v_mid_135_);
v___x_149_ = lean_array_fget_borrowed(v_as_118_, v_lo_119_);
v___x_150_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_116_, v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
v___y_143_ = v_as_118_;
goto v___jp_142_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_array_fswap(v_as_118_, v_lo_119_, v_mid_135_);
v___y_143_ = v___x_151_;
goto v___jp_142_;
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_138_ = lean_array_fget_borrowed(v___y_137_, v_mid_135_);
v___x_139_ = lean_array_fget_borrowed(v___y_137_, v_hi_120_);
v___x_140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_116_, v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec(v_mid_135_);
v___y_122_ = v___y_137_;
goto v___jp_121_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_array_fswap(v___y_137_, v_mid_135_, v_hi_120_);
lean_dec(v_mid_135_);
v___y_122_ = v___x_141_;
goto v___jp_121_;
}
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_144_ = lean_array_fget_borrowed(v___y_143_, v_hi_120_);
v___x_145_ = lean_array_fget_borrowed(v___y_143_, v_lo_119_);
v___x_146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_116_, v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
v___y_137_ = v___y_143_;
goto v___jp_136_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_array_fswap(v___y_143_, v_lo_119_, v_hi_120_);
v___y_137_ = v___x_147_;
goto v___jp_136_;
}
}
}
v___jp_121_:
{
lean_object* v_pivot_123_; lean_object* v___x_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; uint8_t v___x_127_; 
v_pivot_123_ = lean_array_fget(v___y_122_, v_hi_120_);
lean_inc_n(v_lo_119_, 2);
v___x_124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_116_, v_hi_120_, v_pivot_123_, v___y_122_, v_lo_119_, v_lo_119_);
lean_dec(v_pivot_123_);
v_fst_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_fst_125_);
v_snd_126_ = lean_ctor_get(v___x_124_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v___x_124_);
v___x_127_ = lean_nat_dec_le(v_hi_120_, v_fst_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_116_, v_n_117_, v_snd_126_, v_lo_119_, v_fst_125_);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_fst_125_, v___x_129_);
lean_dec(v_fst_125_);
v_as_118_ = v___x_128_;
v_lo_119_ = v___x_130_;
goto _start;
}
else
{
lean_dec(v_fst_125_);
lean_dec(v_lo_119_);
return v_snd_126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object* v_fvarIdToPos_152_, lean_object* v_n_153_, lean_object* v_as_154_, lean_object* v_lo_155_, lean_object* v_hi_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_152_, v_n_153_, v_as_154_, v_lo_155_, v_hi_156_);
lean_dec(v_hi_156_);
lean_dec(v_n_153_);
lean_dec(v_fvarIdToPos_152_);
return v_res_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_unsigned_to_nat(16u);
v___x_160_ = lean_mk_array(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v___x_169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_166_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_170_, lean_object* v_fvarIdToPos_171_){
_start:
{
lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___x_180_; lean_object* v___y_182_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_s_190_; lean_object* v_fvarIds_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3);
v_s_190_ = l_Lean_collectFVars(v___x_189_, v_e_170_);
v_fvarIds_191_ = lean_ctor_get(v_s_190_, 2);
lean_inc_ref(v_fvarIds_191_);
lean_dec_ref(v_s_190_);
v___x_192_ = lean_array_get_size(v_fvarIds_191_);
v___x_193_ = lean_nat_dec_lt(v___x_180_, v___x_192_);
if (v___x_193_ == 0)
{
lean_dec_ref(v_fvarIds_191_);
v___y_182_ = v___x_188_;
goto v___jp_181_;
}
else
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_le(v___x_192_, v___x_192_);
if (v___x_194_ == 0)
{
if (v___x_193_ == 0)
{
lean_dec_ref(v_fvarIds_191_);
v___y_182_ = v___x_188_;
goto v___jp_181_;
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((size_t)0ULL);
v___x_196_ = lean_usize_of_nat(v___x_192_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_171_, v_fvarIds_191_, v___x_195_, v___x_196_, v___x_188_);
lean_dec_ref(v_fvarIds_191_);
v___y_182_ = v___x_197_;
goto v___jp_181_;
}
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_192_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_171_, v_fvarIds_191_, v___x_198_, v___x_199_, v___x_188_);
lean_dec_ref(v_fvarIds_191_);
v___y_182_ = v___x_200_;
goto v___jp_181_;
}
}
v___jp_172_:
{
uint8_t v___x_177_; 
v___x_177_ = lean_nat_dec_le(v___y_176_, v___y_175_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v___y_175_);
lean_inc(v___y_176_);
v___x_178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_171_, v___y_174_, v___y_173_, v___y_176_, v___y_176_);
lean_dec(v___y_176_);
lean_dec(v___y_174_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_171_, v___y_174_, v___y_173_, v___y_176_, v___y_175_);
lean_dec(v___y_175_);
lean_dec(v___y_174_);
return v___x_179_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_array_get_size(v___y_182_);
v___x_184_ = lean_nat_dec_eq(v___x_183_, v___x_180_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_sub(v___x_183_, v___x_185_);
v___x_187_ = lean_nat_dec_le(v___x_180_, v___x_186_);
if (v___x_187_ == 0)
{
lean_inc(v___x_186_);
v___y_173_ = v___y_182_;
v___y_174_ = v___x_183_;
v___y_175_ = v___x_186_;
v___y_176_ = v___x_186_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___y_182_;
v___y_174_ = v___x_183_;
v___y_175_ = v___x_186_;
v___y_176_ = v___x_180_;
goto v___jp_172_;
}
}
else
{
return v___y_182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(lean_object* v_e_201_, lean_object* v_fvarIdToPos_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_e_201_, v_fvarIdToPos_202_);
lean_dec(v_fvarIdToPos_202_);
return v_res_203_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_204_, lean_object* v_k_205_, lean_object* v_t_206_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_205_, v_t_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_208_, lean_object* v_k_209_, lean_object* v_t_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_208_, v_k_209_, v_t_210_);
lean_dec(v_t_210_);
lean_dec(v_k_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_213_, lean_object* v_n_214_, lean_object* v_as_215_, lean_object* v_lo_216_, lean_object* v_hi_217_, lean_object* v_w_218_, lean_object* v_hlo_219_, lean_object* v_hhi_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_213_, v_n_214_, v_as_215_, v_lo_216_, v_hi_217_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_222_, lean_object* v_n_223_, lean_object* v_as_224_, lean_object* v_lo_225_, lean_object* v_hi_226_, lean_object* v_w_227_, lean_object* v_hlo_228_, lean_object* v_hhi_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_222_, v_n_223_, v_as_224_, v_lo_225_, v_hi_226_, v_w_227_, v_hlo_228_, v_hhi_229_);
lean_dec(v_hi_226_);
lean_dec(v_n_223_);
lean_dec(v_fvarIdToPos_222_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(lean_object* v_fvarIdToPos_231_, lean_object* v_n_232_, lean_object* v_lo_233_, lean_object* v_hi_234_, lean_object* v_hhi_235_, lean_object* v_pivot_236_, lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_k_239_, lean_object* v_ilo_240_, lean_object* v_ik_241_, lean_object* v_w_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_231_, v_hi_234_, v_pivot_236_, v_as_237_, v_i_238_, v_k_239_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(lean_object* v_fvarIdToPos_244_, lean_object* v_n_245_, lean_object* v_lo_246_, lean_object* v_hi_247_, lean_object* v_hhi_248_, lean_object* v_pivot_249_, lean_object* v_as_250_, lean_object* v_i_251_, lean_object* v_k_252_, lean_object* v_ilo_253_, lean_object* v_ik_254_, lean_object* v_w_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(v_fvarIdToPos_244_, v_n_245_, v_lo_246_, v_hi_247_, v_hhi_248_, v_pivot_249_, v_as_250_, v_i_251_, v_k_252_, v_ilo_253_, v_ik_254_, v_w_255_);
lean_dec(v_pivot_249_);
lean_dec(v_hi_247_);
lean_dec(v_lo_246_);
lean_dec(v_n_245_);
lean_dec(v_fvarIdToPos_244_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_257_, uint8_t v_bi_258_, lean_object* v_t_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___y_269_; lean_object* v___x_272_; uint8_t v_debug_273_; 
v___x_272_ = lean_st_ref_get(v___y_262_);
v_debug_273_ = lean_ctor_get_uint8(v___x_272_, sizeof(void*)*10);
lean_dec(v___x_272_);
if (v_debug_273_ == 0)
{
v___y_269_ = v___y_262_;
goto v___jp_268_;
}
else
{
lean_object* v___x_274_; 
lean_inc_ref(v_t_259_);
v___x_274_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; 
lean_dec_ref(v___x_274_);
lean_inc_ref(v_b_260_);
v___x_275_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref(v___x_275_);
v___y_269_ = v___y_262_;
goto v___jp_268_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_b_260_);
lean_dec_ref(v_t_259_);
lean_dec(v_x_257_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_b_260_);
lean_dec_ref(v_t_259_);
lean_dec(v_x_257_);
v_a_284_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_274_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
v___jp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = l_Lean_Expr_forallE___override(v_x_257_, v_t_259_, v_b_260_, v_bi_258_);
v___x_271_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_270_, v___y_269_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_292_, lean_object* v_bi_293_, lean_object* v_t_294_, lean_object* v_b_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v_bi_boxed_303_; lean_object* v_res_304_; 
v_bi_boxed_303_ = lean_unbox(v_bi_293_);
v_res_304_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_292_, v_bi_boxed_303_, v_t_294_, v_b_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_308_, lean_object* v_i_309_, lean_object* v_00_u03b2_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_zero_318_; uint8_t v_isZero_319_; 
v_zero_318_ = lean_unsigned_to_nat(0u);
v_isZero_319_ = lean_nat_dec_eq(v_i_309_, v_zero_318_);
if (v_isZero_319_ == 1)
{
lean_object* v___x_320_; 
lean_dec(v_i_309_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_00_u03b2_310_);
return v___x_320_;
}
else
{
lean_object* v_one_321_; lean_object* v_n_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_one_321_ = lean_unsigned_to_nat(1u);
v_n_322_ = lean_nat_sub(v_i_309_, v_one_321_);
lean_dec(v_i_309_);
v___x_323_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_324_ = 0;
v___x_325_ = lean_array_fget_borrowed(v_00_u03b1s_308_, v_n_322_);
lean_inc(v___x_325_);
v___x_326_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_323_, v___x_324_, v___x_325_, v_00_u03b2_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v___x_326_);
v_i_309_ = v_n_322_;
v_00_u03b2_310_ = v_a_327_;
goto _start;
}
else
{
lean_dec(v_n_322_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_329_, lean_object* v_i_330_, lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_329_, v_i_330_, v_00_u03b2_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_00_u03b1s_329_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_340_, lean_object* v_i_341_, lean_object* v_00_u03b2_342_, lean_object* v_h_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_340_, v_i_341_, v_00_u03b2_342_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_352_, lean_object* v_i_353_, lean_object* v_00_u03b2_354_, lean_object* v_h_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_352_, v_i_353_, v_00_u03b2_354_, v_h_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec_ref(v_00_u03b1s_352_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_364_, lean_object* v_00_u03b2_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_array_get_size(v_00_u03b1s_364_);
v___x_374_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_364_, v___x_373_, v_00_u03b2_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_375_, lean_object* v_00_u03b2_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_375_, v_00_u03b2_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec_ref(v_00_u03b1s_375_);
return v_res_384_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_6003__overap_395_; lean_object* v___x_396_; 
v___x_394_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0);
v___x_6003__overap_395_ = lean_panic_fn_borrowed(v___x_394_, v_msg_386_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
v___x_396_ = lean_apply_7(v___x_6003__overap_395_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, lean_box(0));
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object* v_msg_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v_msg_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_406_, lean_object* v_subst_407_, size_t v_sz_408_, size_t v_i_409_, lean_object* v_bs_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_lt(v_i_409_, v_sz_408_);
if (v___x_411_ == 0)
{
return v_bs_410_;
}
else
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_bs_x27_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
v_v_412_ = lean_array_uget(v_bs_410_, v_i_409_);
v___x_413_ = lean_unsigned_to_nat(0u);
v_bs_x27_414_ = lean_array_uset(v_bs_410_, v_i_409_, v___x_413_);
v___x_415_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_406_, v_v_412_);
lean_dec(v_v_412_);
v___x_416_ = l_Lean_instInhabitedExpr;
v___x_417_ = lean_array_get_borrowed(v___x_416_, v_subst_407_, v___x_415_);
lean_dec(v___x_415_);
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_add(v_i_409_, v___x_418_);
lean_inc(v___x_417_);
v___x_420_ = lean_array_uset(v_bs_x27_414_, v_i_409_, v___x_417_);
v_i_409_ = v___x_419_;
v_bs_410_ = v___x_420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_422_, lean_object* v_subst_423_, lean_object* v_sz_424_, lean_object* v_i_425_, lean_object* v_bs_426_){
_start:
{
size_t v_sz_boxed_427_; size_t v_i_boxed_428_; lean_object* v_res_429_; 
v_sz_boxed_427_ = lean_unbox_usize(v_sz_424_);
lean_dec(v_sz_424_);
v_i_boxed_428_ = lean_unbox_usize(v_i_425_);
lean_dec(v_i_425_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_422_, v_subst_423_, v_sz_boxed_427_, v_i_boxed_428_, v_bs_426_);
lean_dec_ref(v_subst_423_);
lean_dec(v_fvarIdToPos_422_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_430_, size_t v_i_431_, lean_object* v_bs_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
if (v___x_433_ == 0)
{
return v_bs_432_;
}
else
{
lean_object* v_v_434_; lean_object* v___x_435_; lean_object* v_bs_x27_436_; lean_object* v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v_v_434_ = lean_array_uget(v_bs_432_, v_i_431_);
v___x_435_ = lean_unsigned_to_nat(0u);
v_bs_x27_436_ = lean_array_uset(v_bs_432_, v_i_431_, v___x_435_);
v___x_437_ = l_Lean_mkFVar(v_v_434_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_431_, v___x_438_);
v___x_440_ = lean_array_uset(v_bs_x27_436_, v_i_431_, v___x_437_);
v_i_431_ = v___x_439_;
v_bs_432_ = v___x_440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_442_, lean_object* v_i_443_, lean_object* v_bs_444_){
_start:
{
size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v_sz_boxed_445_ = lean_unbox_usize(v_sz_442_);
lean_dec(v_sz_442_);
v_i_boxed_446_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_445_, v_i_boxed_446_, v_bs_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v_b_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; 
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
v___x_457_ = lean_apply_8(v_k_448_, v_b_451_, v___y_449_, v___y_450_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, lean_box(0));
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_458_, v___y_459_, v___y_460_, v_b_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_468_, uint8_t v_bi_469_, lean_object* v_type_470_, lean_object* v_k_471_, uint8_t v_kind_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; 
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_480_, 0, v_k_471_);
lean_closure_set(v___f_480_, 1, v___y_473_);
lean_closure_set(v___f_480_, 2, v___y_474_);
v___x_481_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_468_, v_bi_469_, v_type_470_, v___f_480_, v_kind_472_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_481_) == 0)
{
return v___x_481_;
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_490_, lean_object* v_bi_491_, lean_object* v_type_492_, lean_object* v_k_493_, lean_object* v_kind_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v_bi_boxed_502_; uint8_t v_kind_boxed_503_; lean_object* v_res_504_; 
v_bi_boxed_502_ = lean_unbox(v_bi_491_);
v_kind_boxed_503_ = lean_unbox(v_kind_494_);
v_res_504_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_490_, v_bi_boxed_502_, v_type_492_, v_k_493_, v_kind_boxed_503_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_505_, lean_object* v_type_506_, lean_object* v_k_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = 0;
v___x_516_ = 0;
v___x_517_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_505_, v___x_515_, v_type_506_, v_k_507_, v___x_516_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_518_, lean_object* v_type_519_, lean_object* v_k_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_518_, v_type_519_, v_k_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_529_, lean_object* v_k_530_, lean_object* v_fallback_531_){
_start:
{
if (lean_obj_tag(v_t_529_) == 0)
{
lean_object* v_k_532_; lean_object* v_v_533_; lean_object* v_l_534_; lean_object* v_r_535_; uint8_t v___x_536_; 
v_k_532_ = lean_ctor_get(v_t_529_, 1);
v_v_533_ = lean_ctor_get(v_t_529_, 2);
v_l_534_ = lean_ctor_get(v_t_529_, 3);
v_r_535_ = lean_ctor_get(v_t_529_, 4);
v___x_536_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_530_, v_k_532_);
switch(v___x_536_)
{
case 0:
{
v_t_529_ = v_l_534_;
goto _start;
}
case 1:
{
lean_inc(v_v_533_);
return v_v_533_;
}
default: 
{
v_t_529_ = v_r_535_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_531_);
return v_fallback_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_539_, lean_object* v_k_540_, lean_object* v_fallback_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_539_, v_k_540_, v_fallback_541_);
lean_dec(v_fallback_541_);
lean_dec(v_k_540_);
lean_dec(v_t_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_543_, size_t v_sz_544_, size_t v_i_545_, lean_object* v_bs_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_547_ == 0)
{
return v_bs_546_;
}
else
{
lean_object* v_v_548_; lean_object* v___x_549_; lean_object* v_bs_x27_550_; lean_object* v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v_v_548_ = lean_array_uget(v_bs_546_, v_i_545_);
v___x_549_ = lean_unsigned_to_nat(0u);
v_bs_x27_550_ = lean_array_uset(v_bs_546_, v_i_545_, v___x_549_);
v___x_551_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_543_, v_v_548_, v___x_549_);
lean_dec(v_v_548_);
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_add(v_i_545_, v___x_552_);
v___x_554_ = lean_array_uset(v_bs_x27_550_, v_i_545_, v___x_551_);
v_i_545_ = v___x_553_;
v_bs_546_ = v___x_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_bs_559_){
_start:
{
size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v_sz_boxed_560_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_561_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_556_, v_sz_boxed_560_, v_i_boxed_561_, v_bs_559_);
lean_dec(v_fvarIdToPos_556_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_572_ = _args[0];
lean_object* v_subst_573_ = _args[1];
lean_object* v_sz_574_ = _args[2];
lean_object* v___x_575_ = _args[3];
lean_object* v_fvarIds_576_ = _args[4];
lean_object* v_x_577_ = _args[5];
lean_object* v_xs_578_ = _args[6];
lean_object* v_xs_x27_579_ = _args[7];
lean_object* v_args_580_ = _args[8];
lean_object* v_a_581_ = _args[9];
lean_object* v_types_582_ = _args[10];
lean_object* v_a_583_ = _args[11];
lean_object* v_varDeps_584_ = _args[12];
lean_object* v_varPos_585_ = _args[13];
lean_object* v_haveExpr_586_ = _args[14];
lean_object* v_body_587_ = _args[15];
lean_object* v_x_x27_588_ = _args[16];
lean_object* v___y_589_ = _args[17];
lean_object* v___y_590_ = _args[18];
lean_object* v___y_591_ = _args[19];
lean_object* v___y_592_ = _args[20];
lean_object* v___y_593_ = _args[21];
lean_object* v___y_594_ = _args[22];
lean_object* v___y_595_ = _args[23];
_start:
{
size_t v_sz_boxed_596_; size_t v___x_7250__boxed_597_; lean_object* v_res_598_; 
v_sz_boxed_596_ = lean_unbox_usize(v_sz_574_);
lean_dec(v_sz_574_);
v___x_7250__boxed_597_ = lean_unbox_usize(v___x_575_);
lean_dec(v___x_575_);
v_res_598_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_572_, v_subst_573_, v_sz_boxed_596_, v___x_7250__boxed_597_, v_fvarIds_576_, v_x_577_, v_xs_578_, v_xs_x27_579_, v_args_580_, v_a_581_, v_types_582_, v_a_583_, v_varDeps_584_, v_varPos_585_, v_haveExpr_586_, v_body_587_, v_x_x27_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_value_599_, lean_object* v_xs_600_, lean_object* v_fvarIdToPos_601_, uint8_t v___x_602_, uint8_t v_nondep_603_, lean_object* v_type_604_, lean_object* v_subst_605_, lean_object* v_xs_x27_606_, lean_object* v_args_607_, lean_object* v_types_608_, lean_object* v_varDeps_609_, lean_object* v_haveExpr_610_, lean_object* v_body_611_, lean_object* v_declName_612_, lean_object* v_x_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_v_621_; lean_object* v_fvarIds_622_; size_t v_sz_623_; size_t v___x_624_; lean_object* v_varPos_625_; lean_object* v_ys_626_; uint8_t v___x_627_; lean_object* v___x_628_; 
v_v_621_ = lean_expr_instantiate_rev(v_value_599_, v_xs_600_);
lean_inc_ref(v_v_621_);
v_fvarIds_622_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_621_, v_fvarIdToPos_601_);
v_sz_623_ = lean_array_size(v_fvarIds_622_);
v___x_624_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_622_, 2);
v_varPos_625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_601_, v_sz_623_, v___x_624_, v_fvarIds_622_);
v_ys_626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_623_, v___x_624_, v_fvarIds_622_);
v___x_627_ = 1;
v___x_628_ = l_Lean_Meta_mkLambdaFVars(v_ys_626_, v_v_621_, v___x_602_, v_nondep_603_, v___x_602_, v_nondep_603_, v___x_627_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___x_628_);
v___x_630_ = l_Lean_Meta_mkForallFVars(v_ys_626_, v_type_604_, v___x_602_, v_nondep_603_, v_nondep_603_, v___x_627_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec_ref(v_ys_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_631_, v___y_615_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc_n(v_a_633_, 2);
lean_dec_ref(v___x_632_);
v___x_634_ = lean_box_usize(v_sz_623_);
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_636_, 0, v_fvarIdToPos_601_);
lean_closure_set(v___f_636_, 1, v_subst_605_);
lean_closure_set(v___f_636_, 2, v___x_634_);
lean_closure_set(v___f_636_, 3, v___x_635_);
lean_closure_set(v___f_636_, 4, v_fvarIds_622_);
lean_closure_set(v___f_636_, 5, v_x_613_);
lean_closure_set(v___f_636_, 6, v_xs_600_);
lean_closure_set(v___f_636_, 7, v_xs_x27_606_);
lean_closure_set(v___f_636_, 8, v_args_607_);
lean_closure_set(v___f_636_, 9, v_a_629_);
lean_closure_set(v___f_636_, 10, v_types_608_);
lean_closure_set(v___f_636_, 11, v_a_633_);
lean_closure_set(v___f_636_, 12, v_varDeps_609_);
lean_closure_set(v___f_636_, 13, v_varPos_625_);
lean_closure_set(v___f_636_, 14, v_haveExpr_610_);
lean_closure_set(v___f_636_, 15, v_body_611_);
v___x_637_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_612_, v_a_633_, v___f_636_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
return v___x_637_;
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_a_629_);
lean_dec_ref(v_varPos_625_);
lean_dec_ref(v_fvarIds_622_);
lean_dec_ref(v_x_613_);
lean_dec(v_declName_612_);
lean_dec_ref(v_body_611_);
lean_dec_ref(v_haveExpr_610_);
lean_dec_ref(v_varDeps_609_);
lean_dec_ref(v_types_608_);
lean_dec_ref(v_args_607_);
lean_dec_ref(v_xs_x27_606_);
lean_dec_ref(v_subst_605_);
lean_dec(v_fvarIdToPos_601_);
lean_dec_ref(v_xs_600_);
v_a_638_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_632_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_629_);
lean_dec_ref(v_varPos_625_);
lean_dec_ref(v_fvarIds_622_);
lean_dec_ref(v_x_613_);
lean_dec(v_declName_612_);
lean_dec_ref(v_body_611_);
lean_dec_ref(v_haveExpr_610_);
lean_dec_ref(v_varDeps_609_);
lean_dec_ref(v_types_608_);
lean_dec_ref(v_args_607_);
lean_dec_ref(v_xs_x27_606_);
lean_dec_ref(v_subst_605_);
lean_dec(v_fvarIdToPos_601_);
lean_dec_ref(v_xs_600_);
v_a_646_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_630_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_630_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_ys_626_);
lean_dec_ref(v_varPos_625_);
lean_dec_ref(v_fvarIds_622_);
lean_dec_ref(v_x_613_);
lean_dec(v_declName_612_);
lean_dec_ref(v_body_611_);
lean_dec_ref(v_haveExpr_610_);
lean_dec_ref(v_varDeps_609_);
lean_dec_ref(v_types_608_);
lean_dec_ref(v_args_607_);
lean_dec_ref(v_xs_x27_606_);
lean_dec_ref(v_subst_605_);
lean_dec_ref(v_type_604_);
lean_dec(v_fvarIdToPos_601_);
lean_dec_ref(v_xs_600_);
v_a_654_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_628_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_628_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_value_662_ = _args[0];
lean_object* v_xs_663_ = _args[1];
lean_object* v_fvarIdToPos_664_ = _args[2];
lean_object* v___x_665_ = _args[3];
lean_object* v_nondep_666_ = _args[4];
lean_object* v_type_667_ = _args[5];
lean_object* v_subst_668_ = _args[6];
lean_object* v_xs_x27_669_ = _args[7];
lean_object* v_args_670_ = _args[8];
lean_object* v_types_671_ = _args[9];
lean_object* v_varDeps_672_ = _args[10];
lean_object* v_haveExpr_673_ = _args[11];
lean_object* v_body_674_ = _args[12];
lean_object* v_declName_675_ = _args[13];
lean_object* v_x_676_ = _args[14];
lean_object* v___y_677_ = _args[15];
lean_object* v___y_678_ = _args[16];
lean_object* v___y_679_ = _args[17];
lean_object* v___y_680_ = _args[18];
lean_object* v___y_681_ = _args[19];
lean_object* v___y_682_ = _args[20];
lean_object* v___y_683_ = _args[21];
_start:
{
uint8_t v___x_7278__boxed_684_; uint8_t v_nondep_7279__boxed_685_; lean_object* v_res_686_; 
v___x_7278__boxed_684_ = lean_unbox(v___x_665_);
v_nondep_7279__boxed_685_ = lean_unbox(v_nondep_666_);
v_res_686_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_value_662_, v_xs_663_, v_fvarIdToPos_664_, v___x_7278__boxed_684_, v_nondep_7279__boxed_685_, v_type_667_, v_subst_668_, v_xs_x27_669_, v_args_670_, v_types_671_, v_varDeps_672_, v_haveExpr_673_, v_body_674_, v_declName_675_, v_x_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v_value_662_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6));
v___x_691_ = lean_unsigned_to_nat(6u);
v___x_692_ = lean_unsigned_to_nat(168u);
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5));
v___x_694_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_695_ = l_mkPanicMessageWithDecl(v___x_694_, v___x_693_, v___x_692_, v___x_691_, v___x_690_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_696_, lean_object* v_e_697_, lean_object* v_xs_698_, lean_object* v_xs_x27_699_, lean_object* v_args_700_, lean_object* v_subst_701_, lean_object* v_types_702_, lean_object* v_varDeps_703_, lean_object* v_fvarIdToPos_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; 
if (lean_obj_tag(v_e_697_) == 8)
{
uint8_t v_nondep_799_; 
v_nondep_799_ = lean_ctor_get_uint8(v_e_697_, sizeof(void*)*4 + 8);
if (v_nondep_799_ == 1)
{
lean_object* v_declName_800_; lean_object* v_type_801_; lean_object* v_value_802_; lean_object* v_body_803_; uint8_t v___x_804_; 
v_declName_800_ = lean_ctor_get(v_e_697_, 0);
lean_inc(v_declName_800_);
v_type_801_ = lean_ctor_get(v_e_697_, 1);
lean_inc_ref(v_type_801_);
v_value_802_ = lean_ctor_get(v_e_697_, 2);
lean_inc_ref(v_value_802_);
v_body_803_ = lean_ctor_get(v_e_697_, 3);
lean_inc_ref(v_body_803_);
lean_dec_ref(v_e_697_);
v___x_804_ = l_Lean_Expr_hasLooseBVars(v_type_801_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; 
v___x_805_ = lean_box(v___x_804_);
v___x_806_ = lean_box(v_nondep_799_);
lean_inc(v_declName_800_);
lean_inc_ref(v_type_801_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 22, 14);
lean_closure_set(v___f_807_, 0, v_value_802_);
lean_closure_set(v___f_807_, 1, v_xs_698_);
lean_closure_set(v___f_807_, 2, v_fvarIdToPos_704_);
lean_closure_set(v___f_807_, 3, v___x_805_);
lean_closure_set(v___f_807_, 4, v___x_806_);
lean_closure_set(v___f_807_, 5, v_type_801_);
lean_closure_set(v___f_807_, 6, v_subst_701_);
lean_closure_set(v___f_807_, 7, v_xs_x27_699_);
lean_closure_set(v___f_807_, 8, v_args_700_);
lean_closure_set(v___f_807_, 9, v_types_702_);
lean_closure_set(v___f_807_, 10, v_varDeps_703_);
lean_closure_set(v___f_807_, 11, v_haveExpr_696_);
lean_closure_set(v___f_807_, 12, v_body_803_);
lean_closure_set(v___f_807_, 13, v_declName_800_);
v___x_808_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_800_, v_type_801_, v___f_807_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_body_803_);
lean_dec_ref(v_value_802_);
lean_dec_ref(v_type_801_);
lean_dec(v_declName_800_);
lean_dec(v_fvarIdToPos_704_);
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_types_702_);
lean_dec_ref(v_subst_701_);
lean_dec_ref(v_args_700_);
lean_dec_ref(v_xs_x27_699_);
lean_dec_ref(v_xs_698_);
lean_dec_ref(v_haveExpr_696_);
v___x_809_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7);
v___x_810_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v___x_809_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_810_;
}
}
else
{
lean_dec(v_fvarIdToPos_704_);
lean_dec_ref(v_xs_698_);
v___y_713_ = v_a_705_;
v___y_714_ = v_a_706_;
v___y_715_ = v_a_707_;
v___y_716_ = v_a_708_;
v___y_717_ = v_a_709_;
v___y_718_ = v_a_710_;
goto v___jp_712_;
}
}
else
{
lean_dec(v_fvarIdToPos_704_);
lean_dec_ref(v_xs_698_);
v___y_713_ = v_a_705_;
v___y_714_ = v_a_706_;
v___y_715_ = v_a_707_;
v___y_716_ = v_a_708_;
v___y_717_ = v_a_709_;
v___y_718_ = v_a_710_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_subst_701_);
v___x_721_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_697_, v___x_719_, v___x_720_, v_subst_701_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v_subst_701_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_n(v_a_722_, 2);
lean_dec_ref(v___x_721_);
v___x_723_ = l_Lean_Meta_Sym_inferType___redArg(v_a_722_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc_n(v_a_724_, 2);
lean_dec_ref(v___x_723_);
v___x_725_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_724_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
lean_inc(v_a_724_);
v___x_727_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_702_, v_a_724_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v_types_702_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_699_, v_a_722_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v_xs_x27_699_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = l_Lean_mkAppN(v_a_730_, v_args_700_);
lean_dec_ref(v_args_700_);
v___x_732_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_731_, v___y_714_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_750_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_750_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_750_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_738_ = lean_box(0);
lean_inc(v_a_726_);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_726_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_inc_ref(v___x_739_);
v___x_740_ = l_Lean_mkConst(v___x_737_, v___x_739_);
lean_inc(v_a_733_);
lean_inc_ref(v_haveExpr_696_);
lean_inc_n(v_a_724_, 2);
v___x_741_ = l_Lean_mkApp3(v___x_740_, v_a_724_, v_haveExpr_696_, v_a_733_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_743_ = l_Lean_mkConst(v___x_742_, v___x_739_);
v___x_744_ = l_Lean_mkAppB(v___x_743_, v_a_724_, v_haveExpr_696_);
v___x_745_ = l_Lean_Meta_mkExpectedPropHint(v___x_744_, v___x_741_);
v___x_746_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_746_, 0, v_a_724_);
lean_ctor_set(v___x_746_, 1, v_a_726_);
lean_ctor_set(v___x_746_, 2, v_a_733_);
lean_ctor_set(v___x_746_, 3, v___x_745_);
lean_ctor_set(v___x_746_, 4, v_varDeps_703_);
lean_ctor_set(v___x_746_, 5, v_a_728_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_746_);
v___x_748_ = v___x_735_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_a_728_);
lean_dec(v_a_726_);
lean_dec(v_a_724_);
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_haveExpr_696_);
v_a_751_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_732_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_732_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_728_);
lean_dec(v_a_726_);
lean_dec(v_a_724_);
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_args_700_);
lean_dec_ref(v_haveExpr_696_);
v_a_759_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_729_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_729_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_a_726_);
lean_dec(v_a_724_);
lean_dec(v_a_722_);
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_args_700_);
lean_dec_ref(v_xs_x27_699_);
lean_dec_ref(v_haveExpr_696_);
v_a_767_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_727_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_727_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_724_);
lean_dec(v_a_722_);
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_types_702_);
lean_dec_ref(v_args_700_);
lean_dec_ref(v_xs_x27_699_);
lean_dec_ref(v_haveExpr_696_);
v_a_775_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_725_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_725_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_722_);
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_types_702_);
lean_dec_ref(v_args_700_);
lean_dec_ref(v_xs_x27_699_);
lean_dec_ref(v_haveExpr_696_);
v_a_783_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_723_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_723_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_varDeps_703_);
lean_dec_ref(v_types_702_);
lean_dec_ref(v_args_700_);
lean_dec_ref(v_xs_x27_699_);
lean_dec_ref(v_haveExpr_696_);
v_a_791_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_721_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_721_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_811_, lean_object* v_subst_812_, size_t v_sz_813_, size_t v___x_814_, lean_object* v_fvarIds_815_, lean_object* v_x_816_, lean_object* v_xs_817_, lean_object* v_xs_x27_818_, lean_object* v_args_819_, lean_object* v_a_820_, lean_object* v_types_821_, lean_object* v_a_822_, lean_object* v_varDeps_823_, lean_object* v_varPos_824_, lean_object* v_haveExpr_825_, lean_object* v_body_826_, lean_object* v_x_x27_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_811_, v_subst_812_, v_sz_813_, v___x_814_, v_fvarIds_815_);
lean_inc_ref(v_x_x27_827_);
v___x_836_ = l_Lean_mkAppN(v_x_x27_827_, v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_836_, v___y_829_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_Expr_fvarId_x21(v_x_816_);
v___x_840_ = lean_array_get_size(v_xs_817_);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_839_, v___x_840_, v_fvarIdToPos_811_);
v___x_842_ = lean_array_push(v_xs_817_, v_x_816_);
v___x_843_ = lean_array_push(v_xs_x27_818_, v_x_x27_827_);
v___x_844_ = lean_array_push(v_args_819_, v_a_820_);
v___x_845_ = lean_array_push(v_subst_812_, v_a_838_);
v___x_846_ = lean_array_push(v_types_821_, v_a_822_);
v___x_847_ = lean_array_push(v_varDeps_823_, v_varPos_824_);
v___x_848_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_825_, v_body_826_, v___x_842_, v___x_843_, v___x_844_, v___x_845_, v___x_846_, v___x_847_, v___x_841_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_848_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_x_x27_827_);
lean_dec_ref(v_body_826_);
lean_dec_ref(v_haveExpr_825_);
lean_dec_ref(v_varPos_824_);
lean_dec_ref(v_varDeps_823_);
lean_dec_ref(v_a_822_);
lean_dec_ref(v_types_821_);
lean_dec_ref(v_a_820_);
lean_dec_ref(v_args_819_);
lean_dec_ref(v_xs_x27_818_);
lean_dec_ref(v_xs_817_);
lean_dec_ref(v_x_816_);
lean_dec_ref(v_subst_812_);
lean_dec(v_fvarIdToPos_811_);
v_a_849_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_837_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_857_, lean_object* v_e_858_, lean_object* v_xs_859_, lean_object* v_xs_x27_860_, lean_object* v_args_861_, lean_object* v_subst_862_, lean_object* v_types_863_, lean_object* v_varDeps_864_, lean_object* v_fvarIdToPos_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_857_, v_e_858_, v_xs_859_, v_xs_x27_860_, v_args_861_, v_subst_862_, v_types_863_, v_varDeps_864_, v_fvarIdToPos_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_874_, lean_object* v_t_875_, lean_object* v_k_876_, lean_object* v_fallback_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_875_, v_k_876_, v_fallback_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_879_, lean_object* v_t_880_, lean_object* v_k_881_, lean_object* v_fallback_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_879_, v_t_880_, v_k_881_, v_fallback_882_);
lean_dec(v_fallback_882_);
lean_dec(v_k_881_);
lean_dec(v_t_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_884_, lean_object* v_name_885_, uint8_t v_bi_886_, lean_object* v_type_887_, lean_object* v_k_888_, uint8_t v_kind_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_885_, v_bi_886_, v_type_887_, v_k_888_, v_kind_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_898_, lean_object* v_name_899_, lean_object* v_bi_900_, lean_object* v_type_901_, lean_object* v_k_902_, lean_object* v_kind_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_bi_boxed_911_; uint8_t v_kind_boxed_912_; lean_object* v_res_913_; 
v_bi_boxed_911_ = lean_unbox(v_bi_900_);
v_kind_boxed_912_ = lean_unbox(v_kind_903_);
v_res_913_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_898_, v_name_899_, v_bi_boxed_911_, v_type_901_, v_k_902_, v_kind_boxed_912_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_914_, lean_object* v_name_915_, lean_object* v_type_916_, lean_object* v_k_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_915_, v_type_916_, v_k_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_926_, lean_object* v_name_927_, lean_object* v_type_928_, lean_object* v_k_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_926_, v_name_927_, v_type_928_, v_k_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_949_ = lean_box(1);
lean_inc_ref(v_haveExpr_940_);
v___x_950_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_940_, v_haveExpr_940_, v___x_948_, v___x_948_, v___x_948_, v___x_948_, v___x_948_, v___x_948_, v___x_949_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_960_, lean_object* v_n_961_){
_start:
{
lean_object* v_zero_962_; uint8_t v_isZero_963_; 
v_zero_962_ = lean_unsigned_to_nat(0u);
v_isZero_963_ = lean_nat_dec_eq(v_n_961_, v_zero_962_);
if (v_isZero_963_ == 1)
{
lean_dec(v_n_961_);
return v_type_960_;
}
else
{
lean_object* v_one_964_; lean_object* v_n_965_; lean_object* v___x_966_; 
v_one_964_ = lean_unsigned_to_nat(1u);
v_n_965_ = lean_nat_sub(v_n_961_, v_one_964_);
lean_dec(v_n_961_);
v___x_966_ = l_Lean_Expr_bindingBody_x21(v_type_960_);
lean_dec_ref(v_type_960_);
v_type_960_ = v___x_966_;
v_n_961_ = v_n_965_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0(void){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_968_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_00_u03b2_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object* v_idx_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Lean_Expr_bvar___override(v_idx_973_);
v___x_976_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_975_, v___y_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_idx_977_, uint8_t v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v_idx_977_, v___y_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_idx_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v___y_21807__boxed_984_; lean_object* v_res_985_; 
v___y_21807__boxed_984_ = lean_unbox(v___y_982_);
v_res_985_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_idx_981_, v___y_21807__boxed_984_, v___y_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_msg_993_, uint8_t v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___f_1018_; lean_object* v___x_1737__overap_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___f_996_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_997_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_998_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_999_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1000_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1001_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1002_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___f_996_);
lean_ctor_set(v___x_1003_, 1, v___f_997_);
v___x_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___f_998_);
lean_ctor_set(v___x_1004_, 2, v___f_999_);
lean_ctor_set(v___x_1004_, 3, v___f_1000_);
lean_ctor_set(v___x_1004_, 4, v___f_1001_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___f_1002_);
lean_inc_ref_n(v___x_1005_, 6);
v___f_1006_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1006_, 0, v___x_1005_);
v___f_1007_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1007_, 0, v___x_1005_);
v___f_1008_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1008_, 0, v___x_1005_);
v___f_1009_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1009_, 0, v___x_1005_);
v___x_1010_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1010_, 0, lean_box(0));
lean_closure_set(v___x_1010_, 1, lean_box(0));
lean_closure_set(v___x_1010_, 2, v___x_1005_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___f_1006_);
v___x_1012_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1012_, 0, lean_box(0));
lean_closure_set(v___x_1012_, 1, lean_box(0));
lean_closure_set(v___x_1012_, 2, v___x_1005_);
v___x_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_ctor_set(v___x_1013_, 2, v___f_1007_);
lean_ctor_set(v___x_1013_, 3, v___f_1008_);
lean_ctor_set(v___x_1013_, 4, v___f_1009_);
v___x_1014_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1014_, 0, lean_box(0));
lean_closure_set(v___x_1014_, 1, lean_box(0));
lean_closure_set(v___x_1014_, 2, v___x_1005_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_box(0);
v___x_1017_ = l_instInhabitedOfMonad___redArg(v___x_1015_, v___x_1016_);
v___f_1018_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1018_, 0, v___x_1017_);
v___x_1737__overap_1019_ = lean_panic_fn_borrowed(v___f_1018_, v_msg_993_);
lean_dec_ref(v___f_1018_);
v___x_1020_ = lean_box(v___y_994_);
v___x_1021_ = lean_apply_2(v___x_1737__overap_1019_, v___x_1020_, v___y_995_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v___y_21829__boxed_1025_; lean_object* v_res_1026_; 
v___y_21829__boxed_1025_ = lean_unbox(v___y_1023_);
v_res_1026_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_msg_1022_, v___y_21829__boxed_1025_, v___y_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object* v_structName_1027_, lean_object* v_idx_1028_, lean_object* v_struct_1029_, lean_object* v___y_1030_, uint8_t v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___y_1034_; lean_object* v___y_1035_; 
if (v___y_1031_ == 0)
{
v___y_1034_ = v___y_1030_;
v___y_1035_ = v___y_1032_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1048_; lean_object* v_snd_1049_; 
lean_inc_ref(v_struct_1029_);
v___x_1048_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1029_, v___y_1031_, v___y_1032_);
v_snd_1049_ = lean_ctor_get(v___x_1048_, 1);
lean_inc(v_snd_1049_);
lean_dec_ref(v___x_1048_);
v___y_1034_ = v___y_1030_;
v___y_1035_ = v_snd_1049_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_fst_1038_; lean_object* v_snd_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1047_; 
v___x_1036_ = l_Lean_Expr_proj___override(v_structName_1027_, v_idx_1028_, v_struct_1029_);
v___x_1037_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1036_, v___y_1035_);
v_fst_1038_ = lean_ctor_get(v___x_1037_, 0);
v_snd_1039_ = lean_ctor_get(v___x_1037_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1041_ = v___x_1037_;
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_snd_1039_);
lean_inc(v_fst_1038_);
lean_dec(v___x_1037_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___y_1034_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_fst_1038_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___y_1034_);
v___x_1044_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_snd_1039_);
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object* v_structName_1050_, lean_object* v_idx_1051_, lean_object* v_struct_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v___y_21893__boxed_1056_; lean_object* v_res_1057_; 
v___y_21893__boxed_1056_ = lean_unbox(v___y_1054_);
v_res_1057_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_structName_1050_, v_idx_1051_, v_struct_1052_, v___y_1053_, v___y_21893__boxed_1056_, v___y_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object* v_x_1058_, uint8_t v_bi_1059_, lean_object* v_t_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, uint8_t v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___y_1066_; lean_object* v___y_1067_; 
if (v___y_1063_ == 0)
{
v___y_1066_ = v___y_1062_;
v___y_1067_ = v___y_1064_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1080_; lean_object* v_snd_1081_; lean_object* v___x_1082_; lean_object* v_snd_1083_; 
lean_inc_ref(v_t_1060_);
v___x_1080_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1060_, v___y_1063_, v___y_1064_);
v_snd_1081_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_snd_1081_);
lean_dec_ref(v___x_1080_);
lean_inc_ref(v_b_1061_);
v___x_1082_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1061_, v___y_1063_, v_snd_1081_);
v_snd_1083_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_snd_1083_);
lean_dec_ref(v___x_1082_);
v___y_1066_ = v___y_1062_;
v___y_1067_ = v_snd_1083_;
goto v___jp_1065_;
}
v___jp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1079_; 
v___x_1068_ = l_Lean_Expr_lam___override(v_x_1058_, v_t_1060_, v_b_1061_, v_bi_1059_);
v___x_1069_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1068_, v___y_1067_);
v_fst_1070_ = lean_ctor_get(v___x_1069_, 0);
v_snd_1071_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1073_ = v___x_1069_;
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_snd_1071_);
lean_inc(v_fst_1070_);
lean_dec(v___x_1069_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___y_1066_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fst_1070_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___y_1066_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_snd_1071_);
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object* v_x_1084_, lean_object* v_bi_1085_, lean_object* v_t_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v_bi_boxed_1091_; uint8_t v___y_21937__boxed_1092_; lean_object* v_res_1093_; 
v_bi_boxed_1091_ = lean_unbox(v_bi_1085_);
v___y_21937__boxed_1092_ = lean_unbox(v___y_1089_);
v_res_1093_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_x_1084_, v_bi_boxed_1091_, v_t_1086_, v_b_1087_, v___y_1088_, v___y_21937__boxed_1092_, v___y_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object* v_msg_1094_, lean_object* v___y_1095_, uint8_t v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___f_1098_; lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_21471__overap_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___f_1098_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_1099_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_1100_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_1101_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1102_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1103_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1104_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___f_1098_);
lean_ctor_set(v___x_1105_, 1, v___f_1099_);
v___x_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___f_1100_);
lean_ctor_set(v___x_1106_, 2, v___f_1101_);
lean_ctor_set(v___x_1106_, 3, v___f_1102_);
lean_ctor_set(v___x_1106_, 4, v___f_1103_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___f_1104_);
lean_inc_ref_n(v___x_1107_, 6);
v___f_1108_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1108_, 0, v___x_1107_);
v___f_1109_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1109_, 0, v___x_1107_);
v___f_1110_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1110_, 0, v___x_1107_);
v___f_1111_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1111_, 0, v___x_1107_);
v___x_1112_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1112_, 0, lean_box(0));
lean_closure_set(v___x_1112_, 1, lean_box(0));
lean_closure_set(v___x_1112_, 2, v___x_1107_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___f_1108_);
v___x_1114_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1114_, 0, lean_box(0));
lean_closure_set(v___x_1114_, 1, lean_box(0));
lean_closure_set(v___x_1114_, 2, v___x_1107_);
v___x_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
lean_ctor_set(v___x_1115_, 2, v___f_1109_);
lean_ctor_set(v___x_1115_, 3, v___f_1110_);
lean_ctor_set(v___x_1115_, 4, v___f_1111_);
v___x_1116_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1116_, 0, lean_box(0));
lean_closure_set(v___x_1116_, 1, lean_box(0));
lean_closure_set(v___x_1116_, 2, v___x_1107_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_ReaderT_instMonad___redArg(v___x_1117_);
lean_inc_ref_n(v___x_1118_, 6);
v___f_1119_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1119_, 0, v___x_1118_);
v___f_1120_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1120_, 0, v___x_1118_);
v___f_1121_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1121_, 0, v___x_1118_);
v___f_1122_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1122_, 0, v___x_1118_);
v___x_1123_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1123_, 0, lean_box(0));
lean_closure_set(v___x_1123_, 1, lean_box(0));
lean_closure_set(v___x_1123_, 2, v___x_1118_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v___f_1119_);
v___x_1125_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1125_, 0, lean_box(0));
lean_closure_set(v___x_1125_, 1, lean_box(0));
lean_closure_set(v___x_1125_, 2, v___x_1118_);
v___x_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_ctor_set(v___x_1126_, 2, v___f_1120_);
lean_ctor_set(v___x_1126_, 3, v___f_1121_);
lean_ctor_set(v___x_1126_, 4, v___f_1122_);
v___x_1127_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1127_, 0, lean_box(0));
lean_closure_set(v___x_1127_, 1, lean_box(0));
lean_closure_set(v___x_1127_, 2, v___x_1118_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_instInhabitedExpr;
v___x_1130_ = l_instInhabitedOfMonad___redArg(v___x_1128_, v___x_1129_);
v___x_21471__overap_1131_ = lean_panic_fn_borrowed(v___x_1130_, v_msg_1094_);
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(v___y_1096_);
v___x_1133_ = lean_apply_3(v___x_21471__overap_1131_, v___y_1095_, v___x_1132_, v___y_1097_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object* v_msg_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v___y_21993__boxed_1138_; lean_object* v_res_1139_; 
v___y_21993__boxed_1138_ = lean_unbox(v___y_1136_);
v_res_1139_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v_msg_1134_, v___y_1135_, v___y_21993__boxed_1138_, v___y_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object* v_f_1140_, lean_object* v_a_1141_, lean_object* v___y_1142_, uint8_t v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___y_1146_; lean_object* v___y_1147_; 
if (v___y_1143_ == 0)
{
v___y_1146_ = v___y_1142_;
v___y_1147_ = v___y_1144_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1160_; lean_object* v_snd_1161_; lean_object* v___x_1162_; lean_object* v_snd_1163_; 
lean_inc_ref(v_f_1140_);
v___x_1160_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1140_, v___y_1143_, v___y_1144_);
v_snd_1161_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_snd_1161_);
lean_dec_ref(v___x_1160_);
lean_inc_ref(v_a_1141_);
v___x_1162_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1141_, v___y_1143_, v_snd_1161_);
v_snd_1163_ = lean_ctor_get(v___x_1162_, 1);
lean_inc(v_snd_1163_);
lean_dec_ref(v___x_1162_);
v___y_1146_ = v___y_1142_;
v___y_1147_ = v_snd_1163_;
goto v___jp_1145_;
}
v___jp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v___x_1148_ = l_Lean_Expr_app___override(v_f_1140_, v_a_1141_);
v___x_1149_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1148_, v___y_1147_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
v_snd_1151_ = lean_ctor_get(v___x_1149_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v___x_1149_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v___x_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___y_1146_);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_fst_1150_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___y_1146_);
v___x_1156_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_snd_1151_);
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object* v_f_1164_, lean_object* v_a_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
uint8_t v___y_22072__boxed_1169_; lean_object* v_res_1170_; 
v___y_22072__boxed_1169_ = lean_unbox(v___y_1167_);
v_res_1170_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_f_1164_, v_a_1165_, v___y_1166_, v___y_22072__boxed_1169_, v___y_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object* v_x_1171_, uint8_t v_bi_1172_, lean_object* v_t_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, uint8_t v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___y_1179_; lean_object* v___y_1180_; 
if (v___y_1176_ == 0)
{
v___y_1179_ = v___y_1175_;
v___y_1180_ = v___y_1177_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1193_; lean_object* v_snd_1194_; lean_object* v___x_1195_; lean_object* v_snd_1196_; 
lean_inc_ref(v_t_1173_);
v___x_1193_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1173_, v___y_1176_, v___y_1177_);
v_snd_1194_ = lean_ctor_get(v___x_1193_, 1);
lean_inc(v_snd_1194_);
lean_dec_ref(v___x_1193_);
lean_inc_ref(v_b_1174_);
v___x_1195_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1174_, v___y_1176_, v_snd_1194_);
v_snd_1196_ = lean_ctor_get(v___x_1195_, 1);
lean_inc(v_snd_1196_);
lean_dec_ref(v___x_1195_);
v___y_1179_ = v___y_1175_;
v___y_1180_ = v_snd_1196_;
goto v___jp_1178_;
}
v___jp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1192_; 
v___x_1181_ = l_Lean_Expr_forallE___override(v_x_1171_, v_t_1173_, v_b_1174_, v_bi_1172_);
v___x_1182_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1181_, v___y_1180_);
v_fst_1183_ = lean_ctor_get(v___x_1182_, 0);
v_snd_1184_ = lean_ctor_get(v___x_1182_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1186_ = v___x_1182_;
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_snd_1184_);
lean_inc(v_fst_1183_);
lean_dec(v___x_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___y_1179_);
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1183_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___y_1179_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v_snd_1184_);
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object* v_x_1197_, lean_object* v_bi_1198_, lean_object* v_t_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v_bi_boxed_1204_; uint8_t v___y_22121__boxed_1205_; lean_object* v_res_1206_; 
v_bi_boxed_1204_ = lean_unbox(v_bi_1198_);
v___y_22121__boxed_1205_ = lean_unbox(v___y_1202_);
v_res_1206_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_x_1197_, v_bi_boxed_1204_, v_t_1199_, v_b_1200_, v___y_1201_, v___y_22121__boxed_1205_, v___y_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object* v_x_1207_, lean_object* v_t_1208_, lean_object* v_v_1209_, lean_object* v_b_1210_, uint8_t v_nondep_1211_, lean_object* v___y_1212_, uint8_t v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___y_1216_; lean_object* v___y_1217_; 
if (v___y_1213_ == 0)
{
v___y_1216_ = v___y_1212_;
v___y_1217_ = v___y_1214_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1230_; lean_object* v_snd_1231_; lean_object* v___x_1232_; lean_object* v_snd_1233_; lean_object* v___x_1234_; lean_object* v_snd_1235_; 
lean_inc_ref(v_t_1208_);
v___x_1230_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1208_, v___y_1213_, v___y_1214_);
v_snd_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_snd_1231_);
lean_dec_ref(v___x_1230_);
lean_inc_ref(v_v_1209_);
v___x_1232_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1209_, v___y_1213_, v_snd_1231_);
v_snd_1233_ = lean_ctor_get(v___x_1232_, 1);
lean_inc(v_snd_1233_);
lean_dec_ref(v___x_1232_);
lean_inc_ref(v_b_1210_);
v___x_1234_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1210_, v___y_1213_, v_snd_1233_);
v_snd_1235_ = lean_ctor_get(v___x_1234_, 1);
lean_inc(v_snd_1235_);
lean_dec_ref(v___x_1234_);
v___y_1216_ = v___y_1212_;
v___y_1217_ = v_snd_1235_;
goto v___jp_1215_;
}
v___jp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
v___x_1218_ = l_Lean_Expr_letE___override(v_x_1207_, v_t_1208_, v_v_1209_, v_b_1210_, v_nondep_1211_);
v___x_1219_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1218_, v___y_1217_);
v_fst_1220_ = lean_ctor_get(v___x_1219_, 0);
v_snd_1221_ = lean_ctor_get(v___x_1219_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1219_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snd_1221_);
lean_inc(v_fst_1220_);
lean_dec(v___x_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___y_1216_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_fst_1220_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___y_1216_);
v___x_1226_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_snd_1221_);
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object* v_x_1236_, lean_object* v_t_1237_, lean_object* v_v_1238_, lean_object* v_b_1239_, lean_object* v_nondep_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_nondep_boxed_1244_; uint8_t v___y_22170__boxed_1245_; lean_object* v_res_1246_; 
v_nondep_boxed_1244_ = lean_unbox(v_nondep_1240_);
v___y_22170__boxed_1245_ = lean_unbox(v___y_1242_);
v_res_1246_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_x_1236_, v_t_1237_, v_v_1238_, v_b_1239_, v_nondep_boxed_1244_, v___y_1241_, v___y_22170__boxed_1245_, v___y_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_a_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_box(0);
return v___x_1249_;
}
else
{
lean_object* v_key_1250_; lean_object* v_value_1251_; lean_object* v_tail_1252_; uint8_t v___y_1254_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; lean_object* v_fst_1259_; lean_object* v_snd_1260_; uint8_t v___x_1261_; 
v_key_1250_ = lean_ctor_get(v_x_1248_, 0);
v_value_1251_ = lean_ctor_get(v_x_1248_, 1);
v_tail_1252_ = lean_ctor_get(v_x_1248_, 2);
v_fst_1257_ = lean_ctor_get(v_key_1250_, 0);
v_snd_1258_ = lean_ctor_get(v_key_1250_, 1);
v_fst_1259_ = lean_ctor_get(v_a_1247_, 0);
v_snd_1260_ = lean_ctor_get(v_a_1247_, 1);
v___x_1261_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1257_, v_fst_1259_);
if (v___x_1261_ == 0)
{
v___y_1254_ = v___x_1261_;
goto v___jp_1253_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_snd_1258_, v_snd_1260_);
v___y_1254_ = v___x_1262_;
goto v___jp_1253_;
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
v_x_1248_ = v_tail_1252_;
goto _start;
}
else
{
lean_object* v___x_1256_; 
lean_inc(v_value_1251_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_value_1251_);
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object* v_a_1263_, lean_object* v_x_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1263_, v_x_1264_);
lean_dec(v_x_1264_);
lean_dec_ref(v_a_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object* v_m_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_buckets_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; uint64_t v___x_1276_; uint64_t v_fold_1277_; uint64_t v___x_1278_; uint64_t v___x_1279_; uint64_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_buckets_1268_ = lean_ctor_get(v_m_1266_, 1);
v_fst_1269_ = lean_ctor_get(v_a_1267_, 0);
v_snd_1270_ = lean_ctor_get(v_a_1267_, 1);
v___x_1271_ = lean_array_get_size(v_buckets_1268_);
v___x_1272_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1269_);
v___x_1273_ = lean_uint64_of_nat(v_snd_1270_);
v___x_1274_ = lean_uint64_mix_hash(v___x_1272_, v___x_1273_);
v___x_1275_ = 32ULL;
v___x_1276_ = lean_uint64_shift_right(v___x_1274_, v___x_1275_);
v_fold_1277_ = lean_uint64_xor(v___x_1274_, v___x_1276_);
v___x_1278_ = 16ULL;
v___x_1279_ = lean_uint64_shift_right(v_fold_1277_, v___x_1278_);
v___x_1280_ = lean_uint64_xor(v_fold_1277_, v___x_1279_);
v___x_1281_ = lean_uint64_to_usize(v___x_1280_);
v___x_1282_ = lean_usize_of_nat(v___x_1271_);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_sub(v___x_1282_, v___x_1283_);
v___x_1285_ = lean_usize_land(v___x_1281_, v___x_1284_);
v___x_1286_ = lean_array_uget_borrowed(v_buckets_1268_, v___x_1285_);
v___x_1287_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1267_, v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1288_, v_a_1289_);
lean_dec_ref(v_a_1289_);
lean_dec_ref(v_m_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object* v_d_1291_, lean_object* v_e_1292_, lean_object* v___y_1293_, uint8_t v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___y_1297_; lean_object* v___y_1298_; 
if (v___y_1294_ == 0)
{
v___y_1297_ = v___y_1293_;
v___y_1298_ = v___y_1295_;
goto v___jp_1296_;
}
else
{
lean_object* v___x_1311_; lean_object* v_snd_1312_; 
lean_inc_ref(v_e_1292_);
v___x_1311_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1292_, v___y_1294_, v___y_1295_);
v_snd_1312_ = lean_ctor_get(v___x_1311_, 1);
lean_inc(v_snd_1312_);
lean_dec_ref(v___x_1311_);
v___y_1297_ = v___y_1293_;
v___y_1298_ = v_snd_1312_;
goto v___jp_1296_;
}
v___jp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1310_; 
v___x_1299_ = l_Lean_Expr_mdata___override(v_d_1291_, v_e_1292_);
v___x_1300_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1299_, v___y_1298_);
v_fst_1301_ = lean_ctor_get(v___x_1300_, 0);
v_snd_1302_ = lean_ctor_get(v___x_1300_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1304_ = v___x_1300_;
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_snd_1302_);
lean_inc(v_fst_1301_);
lean_dec(v___x_1300_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___y_1297_);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_fst_1301_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___y_1297_);
v___x_1307_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_snd_1302_);
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object* v_d_1313_, lean_object* v_e_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___y_22293__boxed_1318_; lean_object* v_res_1319_; 
v___y_22293__boxed_1318_ = lean_unbox(v___y_1316_);
v_res_1319_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_d_1313_, v_e_1314_, v___y_1315_, v___y_22293__boxed_1318_, v___y_1317_);
return v_res_1319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Array_instInhabited(lean_box(0));
return v___x_1320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2));
v___x_1324_ = lean_unsigned_to_nat(12u);
v___x_1325_ = lean_unsigned_to_nat(234u);
v___x_1326_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1));
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1328_ = l_mkPanicMessageWithDecl(v___x_1327_, v___x_1326_, v___x_1325_, v___x_1324_, v___x_1323_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1333_ = lean_unsigned_to_nat(67u);
v___x_1334_ = lean_unsigned_to_nat(35u);
v___x_1335_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1));
v___x_1336_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0));
v___x_1337_ = l_mkPanicMessageWithDecl(v___x_1336_, v___x_1335_, v___x_1334_, v___x_1333_, v___x_1332_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_n_1338_, lean_object* v_varDeps_1339_, lean_object* v_xs_1340_, lean_object* v_e_1341_, lean_object* v_offset_1342_, lean_object* v_a_1343_, uint8_t v_a_1344_, lean_object* v_a_1345_){
_start:
{
switch(lean_obj_tag(v_e_1341_))
{
case 5:
{
lean_object* v_fn_1346_; lean_object* v_arg_1347_; lean_object* v___x_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v_fst_1351_; lean_object* v_snd_1352_; lean_object* v___x_1353_; lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1376_; 
v_fn_1346_ = lean_ctor_get(v_e_1341_, 0);
v_arg_1347_ = lean_ctor_get(v_e_1341_, 1);
lean_inc(v_offset_1342_);
lean_inc_ref(v_fn_1346_);
v___x_1348_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_fn_1346_, v_offset_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
v_fst_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_fst_1349_);
v_snd_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_snd_1350_);
lean_dec_ref(v___x_1348_);
v_fst_1351_ = lean_ctor_get(v_fst_1349_, 0);
lean_inc(v_fst_1351_);
v_snd_1352_ = lean_ctor_get(v_fst_1349_, 1);
lean_inc(v_snd_1352_);
lean_dec(v_fst_1349_);
lean_inc_ref(v_arg_1347_);
v___x_1353_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_arg_1347_, v_offset_1342_, v_snd_1352_, v_a_1344_, v_snd_1350_);
v_fst_1354_ = lean_ctor_get(v___x_1353_, 0);
v_snd_1355_ = lean_ctor_get(v___x_1353_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1357_ = v___x_1353_;
v_isShared_1358_ = v_isSharedCheck_1376_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v___x_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1376_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_fst_1359_; lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1375_; 
v_fst_1359_ = lean_ctor_get(v_fst_1354_, 0);
v_snd_1360_ = lean_ctor_get(v_fst_1354_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_fst_1354_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1362_ = v_fst_1354_;
v_isShared_1363_ = v_isSharedCheck_1375_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_inc(v_fst_1359_);
lean_dec(v_fst_1354_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1375_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
uint8_t v___y_1365_; uint8_t v___x_1373_; 
v___x_1373_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1346_, v_fst_1351_);
if (v___x_1373_ == 0)
{
v___y_1365_ = v___x_1373_;
goto v___jp_1364_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1347_, v_fst_1359_);
v___y_1365_ = v___x_1374_;
goto v___jp_1364_;
}
v___jp_1364_:
{
if (v___y_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_del_object(v___x_1362_);
lean_del_object(v___x_1357_);
lean_dec_ref(v_e_1341_);
v___x_1366_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_fst_1351_, v_fst_1359_, v_snd_1360_, v_a_1344_, v_snd_1355_);
return v___x_1366_;
}
else
{
lean_object* v___x_1368_; 
lean_dec(v_fst_1359_);
lean_dec(v_fst_1351_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_e_1341_);
v___x_1368_ = v___x_1362_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_e_1341_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1360_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1368_);
v___x_1370_ = v___x_1357_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_snd_1355_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_1377_; lean_object* v_binderType_1378_; lean_object* v_body_1379_; uint8_t v_binderInfo_1380_; lean_object* v___x_1381_; lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_fst_1389_; lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1411_; 
v_binderName_1377_ = lean_ctor_get(v_e_1341_, 0);
v_binderType_1378_ = lean_ctor_get(v_e_1341_, 1);
v_body_1379_ = lean_ctor_get(v_e_1341_, 2);
v_binderInfo_1380_ = lean_ctor_get_uint8(v_e_1341_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1342_);
lean_inc_ref(v_binderType_1378_);
v___x_1381_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_binderType_1378_, v_offset_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
v_fst_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_fst_1382_);
v_snd_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_snd_1383_);
lean_dec_ref(v___x_1381_);
v_fst_1384_ = lean_ctor_get(v_fst_1382_, 0);
lean_inc(v_fst_1384_);
v_snd_1385_ = lean_ctor_get(v_fst_1382_, 1);
lean_inc(v_snd_1385_);
lean_dec(v_fst_1382_);
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v_offset_1342_, v___x_1386_);
lean_dec(v_offset_1342_);
lean_inc_ref(v_body_1379_);
v___x_1388_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_body_1379_, v___x_1387_, v_snd_1385_, v_a_1344_, v_snd_1383_);
v_fst_1389_ = lean_ctor_get(v___x_1388_, 0);
v_snd_1390_ = lean_ctor_get(v___x_1388_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1392_ = v___x_1388_;
v_isShared_1393_ = v_isSharedCheck_1411_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_inc(v_fst_1389_);
lean_dec(v___x_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1411_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1410_; 
v_fst_1394_ = lean_ctor_get(v_fst_1389_, 0);
v_snd_1395_ = lean_ctor_get(v_fst_1389_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_fst_1389_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1397_ = v_fst_1389_;
v_isShared_1398_ = v_isSharedCheck_1410_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_inc(v_fst_1394_);
lean_dec(v_fst_1389_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1410_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___y_1400_; uint8_t v___x_1408_; 
v___x_1408_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1378_, v_fst_1384_);
if (v___x_1408_ == 0)
{
v___y_1400_ = v___x_1408_;
goto v___jp_1399_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1379_, v_fst_1394_);
v___y_1400_ = v___x_1409_;
goto v___jp_1399_;
}
v___jp_1399_:
{
if (v___y_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_inc(v_binderName_1377_);
lean_del_object(v___x_1397_);
lean_del_object(v___x_1392_);
lean_dec_ref(v_e_1341_);
v___x_1401_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_binderName_1377_, v_binderInfo_1380_, v_fst_1384_, v_fst_1394_, v_snd_1395_, v_a_1344_, v_snd_1390_);
return v___x_1401_;
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_fst_1394_);
lean_dec(v_fst_1384_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_e_1341_);
v___x_1403_ = v___x_1397_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_e_1341_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_snd_1395_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1403_);
v___x_1405_ = v___x_1392_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1390_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1412_; lean_object* v_binderType_1413_; lean_object* v_body_1414_; uint8_t v_binderInfo_1415_; lean_object* v___x_1416_; lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v_fst_1419_; lean_object* v_snd_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1446_; 
v_binderName_1412_ = lean_ctor_get(v_e_1341_, 0);
v_binderType_1413_ = lean_ctor_get(v_e_1341_, 1);
v_body_1414_ = lean_ctor_get(v_e_1341_, 2);
v_binderInfo_1415_ = lean_ctor_get_uint8(v_e_1341_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1342_);
lean_inc_ref(v_binderType_1413_);
v___x_1416_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_binderType_1413_, v_offset_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
v_fst_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_fst_1417_);
v_snd_1418_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_snd_1418_);
lean_dec_ref(v___x_1416_);
v_fst_1419_ = lean_ctor_get(v_fst_1417_, 0);
lean_inc(v_fst_1419_);
v_snd_1420_ = lean_ctor_get(v_fst_1417_, 1);
lean_inc(v_snd_1420_);
lean_dec(v_fst_1417_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_offset_1342_, v___x_1421_);
lean_dec(v_offset_1342_);
lean_inc_ref(v_body_1414_);
v___x_1423_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_body_1414_, v___x_1422_, v_snd_1420_, v_a_1344_, v_snd_1418_);
v_fst_1424_ = lean_ctor_get(v___x_1423_, 0);
v_snd_1425_ = lean_ctor_get(v___x_1423_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1427_ = v___x_1423_;
v_isShared_1428_ = v_isSharedCheck_1446_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snd_1425_);
lean_inc(v_fst_1424_);
lean_dec(v___x_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1446_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1445_; 
v_fst_1429_ = lean_ctor_get(v_fst_1424_, 0);
v_snd_1430_ = lean_ctor_get(v_fst_1424_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_fst_1424_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1432_ = v_fst_1424_;
v_isShared_1433_ = v_isSharedCheck_1445_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_inc(v_fst_1429_);
lean_dec(v_fst_1424_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1445_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v___y_1435_; uint8_t v___x_1443_; 
v___x_1443_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1413_, v_fst_1419_);
if (v___x_1443_ == 0)
{
v___y_1435_ = v___x_1443_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1414_, v_fst_1429_);
v___y_1435_ = v___x_1444_;
goto v___jp_1434_;
}
v___jp_1434_:
{
if (v___y_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_inc(v_binderName_1412_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
lean_dec_ref(v_e_1341_);
v___x_1436_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_binderName_1412_, v_binderInfo_1415_, v_fst_1419_, v_fst_1429_, v_snd_1430_, v_a_1344_, v_snd_1425_);
return v___x_1436_;
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_fst_1429_);
lean_dec(v_fst_1419_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_e_1341_);
v___x_1438_ = v___x_1432_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_e_1341_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1430_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1438_);
v___x_1440_ = v___x_1427_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_snd_1425_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1447_; lean_object* v_type_1448_; lean_object* v_value_1449_; lean_object* v_body_1450_; uint8_t v_nondep_1451_; lean_object* v___x_1452_; lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v_fst_1455_; lean_object* v_snd_1456_; lean_object* v___x_1457_; lean_object* v_fst_1458_; lean_object* v_snd_1459_; lean_object* v_fst_1460_; lean_object* v_snd_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1489_; 
v_declName_1447_ = lean_ctor_get(v_e_1341_, 0);
v_type_1448_ = lean_ctor_get(v_e_1341_, 1);
v_value_1449_ = lean_ctor_get(v_e_1341_, 2);
v_body_1450_ = lean_ctor_get(v_e_1341_, 3);
v_nondep_1451_ = lean_ctor_get_uint8(v_e_1341_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_1342_, 2);
lean_inc_ref(v_type_1448_);
v___x_1452_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_type_1448_, v_offset_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
v_fst_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_fst_1453_);
v_snd_1454_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_snd_1454_);
lean_dec_ref(v___x_1452_);
v_fst_1455_ = lean_ctor_get(v_fst_1453_, 0);
lean_inc(v_fst_1455_);
v_snd_1456_ = lean_ctor_get(v_fst_1453_, 1);
lean_inc(v_snd_1456_);
lean_dec(v_fst_1453_);
lean_inc_ref(v_value_1449_);
v___x_1457_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_value_1449_, v_offset_1342_, v_snd_1456_, v_a_1344_, v_snd_1454_);
v_fst_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_fst_1458_);
v_snd_1459_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_snd_1459_);
lean_dec_ref(v___x_1457_);
v_fst_1460_ = lean_ctor_get(v_fst_1458_, 0);
lean_inc(v_fst_1460_);
v_snd_1461_ = lean_ctor_get(v_fst_1458_, 1);
lean_inc(v_snd_1461_);
lean_dec(v_fst_1458_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_offset_1342_, v___x_1462_);
lean_dec(v_offset_1342_);
lean_inc_ref(v_body_1450_);
v___x_1464_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_body_1450_, v___x_1463_, v_snd_1461_, v_a_1344_, v_snd_1459_);
v_fst_1465_ = lean_ctor_get(v___x_1464_, 0);
v_snd_1466_ = lean_ctor_get(v___x_1464_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1489_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_snd_1466_);
lean_inc(v_fst_1465_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1489_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_fst_1470_; lean_object* v_snd_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1488_; 
v_fst_1470_ = lean_ctor_get(v_fst_1465_, 0);
v_snd_1471_ = lean_ctor_get(v_fst_1465_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_fst_1465_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1473_ = v_fst_1465_;
v_isShared_1474_ = v_isSharedCheck_1488_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snd_1471_);
lean_inc(v_fst_1470_);
lean_dec(v_fst_1465_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1488_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
uint8_t v___y_1476_; uint8_t v___x_1486_; 
v___x_1486_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1448_, v_fst_1455_);
if (v___x_1486_ == 0)
{
v___y_1476_ = v___x_1486_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1449_, v_fst_1460_);
v___y_1476_ = v___x_1487_;
goto v___jp_1475_;
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_inc(v_declName_1447_);
lean_del_object(v___x_1473_);
lean_del_object(v___x_1468_);
lean_dec_ref(v_e_1341_);
v___x_1477_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1447_, v_fst_1455_, v_fst_1460_, v_fst_1470_, v_nondep_1451_, v_snd_1471_, v_a_1344_, v_snd_1466_);
return v___x_1477_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1450_, v_fst_1470_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_inc(v_declName_1447_);
lean_del_object(v___x_1473_);
lean_del_object(v___x_1468_);
lean_dec_ref(v_e_1341_);
v___x_1479_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1447_, v_fst_1455_, v_fst_1460_, v_fst_1470_, v_nondep_1451_, v_snd_1471_, v_a_1344_, v_snd_1466_);
return v___x_1479_;
}
else
{
lean_object* v___x_1481_; 
lean_dec(v_fst_1470_);
lean_dec(v_fst_1460_);
lean_dec(v_fst_1455_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v_e_1341_);
v___x_1481_ = v___x_1473_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_e_1341_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_snd_1471_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1481_);
v___x_1483_ = v___x_1468_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_snd_1466_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
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
lean_object* v_data_1490_; lean_object* v_expr_1491_; lean_object* v___x_1492_; lean_object* v_fst_1493_; lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1512_; 
v_data_1490_ = lean_ctor_get(v_e_1341_, 0);
v_expr_1491_ = lean_ctor_get(v_e_1341_, 1);
lean_inc_ref(v_expr_1491_);
v___x_1492_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_expr_1491_, v_offset_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
v_fst_1493_ = lean_ctor_get(v___x_1492_, 0);
v_snd_1494_ = lean_ctor_get(v___x_1492_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1496_ = v___x_1492_;
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_inc(v_fst_1493_);
lean_dec(v___x_1492_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_fst_1498_; lean_object* v_snd_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1511_; 
v_fst_1498_ = lean_ctor_get(v_fst_1493_, 0);
v_snd_1499_ = lean_ctor_get(v_fst_1493_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_fst_1493_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1501_ = v_fst_1493_;
v_isShared_1502_ = v_isSharedCheck_1511_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snd_1499_);
lean_inc(v_fst_1498_);
lean_dec(v_fst_1493_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1511_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
uint8_t v___x_1503_; 
v___x_1503_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1491_, v_fst_1498_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_inc(v_data_1490_);
lean_del_object(v___x_1501_);
lean_del_object(v___x_1496_);
lean_dec_ref(v_e_1341_);
v___x_1504_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_data_1490_, v_fst_1498_, v_snd_1499_, v_a_1344_, v_snd_1494_);
return v___x_1504_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_fst_1498_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v_e_1341_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_e_1341_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_snd_1499_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1506_);
v___x_1508_ = v___x_1496_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_snd_1494_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1513_; lean_object* v_idx_1514_; lean_object* v_struct_1515_; lean_object* v___x_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1536_; 
v_typeName_1513_ = lean_ctor_get(v_e_1341_, 0);
v_idx_1514_ = lean_ctor_get(v_e_1341_, 1);
v_struct_1515_ = lean_ctor_get(v_e_1341_, 2);
lean_inc_ref(v_struct_1515_);
v___x_1516_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1338_, v_varDeps_1339_, v_xs_1340_, v_struct_1515_, v_offset_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
v_fst_1517_ = lean_ctor_get(v___x_1516_, 0);
v_snd_1518_ = lean_ctor_get(v___x_1516_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1520_ = v___x_1516_;
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_snd_1518_);
lean_inc(v_fst_1517_);
lean_dec(v___x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1535_; 
v_fst_1522_ = lean_ctor_get(v_fst_1517_, 0);
v_snd_1523_ = lean_ctor_get(v_fst_1517_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_fst_1517_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1525_ = v_fst_1517_;
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snd_1523_);
lean_inc(v_fst_1522_);
lean_dec(v_fst_1517_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
uint8_t v___x_1527_; 
v___x_1527_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1515_, v_fst_1522_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_inc(v_idx_1514_);
lean_inc(v_typeName_1513_);
lean_del_object(v___x_1525_);
lean_del_object(v___x_1520_);
lean_dec_ref(v_e_1341_);
v___x_1528_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_typeName_1513_, v_idx_1514_, v_fst_1522_, v_snd_1523_, v_a_1344_, v_snd_1518_);
return v___x_1528_;
}
else
{
lean_object* v___x_1530_; 
lean_dec(v_fst_1522_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_e_1341_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_e_1341_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_snd_1523_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1530_);
v___x_1532_ = v___x_1520_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_snd_1518_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_offset_1342_);
lean_dec_ref(v_e_1341_);
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3);
v___x_1538_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v___x_1537_, v_a_1343_, v_a_1344_, v_a_1345_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object* v_n_1539_, lean_object* v_varDeps_1540_, lean_object* v_xs_1541_, lean_object* v_e_1542_, lean_object* v_offset_1543_, lean_object* v_a_1544_, uint8_t v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_key_1547_; lean_object* v_snd_1549_; lean_object* v___x_1562_; 
lean_inc(v_offset_1543_);
lean_inc_ref(v_e_1542_);
v_key_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1547_, 0, v_e_1542_);
lean_ctor_set(v_key_1547_, 1, v_offset_1543_);
v___x_1562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_a_1544_, v_key_1547_);
if (lean_obj_tag(v___x_1562_) == 1)
{
lean_object* v_val_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v_key_1547_);
lean_dec(v_offset_1543_);
lean_dec_ref(v_e_1542_);
v_val_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_val_1563_);
lean_ctor_set(v___x_1564_, 1, v_a_1544_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v_a_1546_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
lean_dec(v___x_1562_);
v___x_1566_ = l_Lean_Expr_looseBVarRange(v_e_1542_);
v___x_1567_ = lean_nat_dec_le(v___x_1566_, v_offset_1543_);
lean_dec(v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Expr_getAppFn(v_e_1542_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_deBruijnIndex_1569_; uint8_t v___x_1570_; 
v_deBruijnIndex_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_deBruijnIndex_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = lean_nat_dec_le(v_offset_1543_, v_deBruijnIndex_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v_deBruijnIndex_1569_);
lean_dec(v_offset_1543_);
v___x_1571_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_nat_add(v_offset_1543_, v_n_1539_);
v___x_1573_ = lean_nat_dec_lt(v_deBruijnIndex_1569_, v___x_1572_);
lean_dec(v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1578_; 
lean_dec(v_offset_1543_);
lean_dec_ref(v_e_1542_);
v___x_1574_ = lean_nat_sub(v_deBruijnIndex_1569_, v_n_1539_);
lean_dec(v_deBruijnIndex_1569_);
v___x_1575_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1574_, v_a_1546_);
v_fst_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_fst_1576_);
v_snd_1577_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_snd_1577_);
lean_dec_ref(v___x_1575_);
v___x_1578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_fst_1576_, v_a_1544_, v_a_1545_, v_snd_1577_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_i_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_expectedNumArgs_1585_; lean_object* v_numArgs_1586_; uint8_t v___x_1587_; 
v___x_1579_ = lean_nat_sub(v_deBruijnIndex_1569_, v_offset_1543_);
lean_dec(v_deBruijnIndex_1569_);
v___x_1580_ = lean_nat_sub(v_n_1539_, v___x_1579_);
lean_dec(v___x_1579_);
v___x_1581_ = lean_unsigned_to_nat(1u);
v_i_1582_ = lean_nat_sub(v___x_1580_, v___x_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1584_ = lean_array_get_borrowed(v___x_1583_, v_varDeps_1540_, v_i_1582_);
v_expectedNumArgs_1585_ = lean_array_get_size(v___x_1584_);
v_numArgs_1586_ = l_Lean_Expr_getAppNumArgs(v_e_1542_);
v___x_1587_ = lean_nat_dec_lt(v_expectedNumArgs_1585_, v_numArgs_1586_);
if (v___x_1587_ == 0)
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_nat_dec_eq(v_numArgs_1586_, v_expectedNumArgs_1585_);
lean_dec(v_numArgs_1586_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_fst_1591_; 
lean_dec(v_i_1582_);
v___x_1589_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1590_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1589_, v_a_1545_, v_a_1546_);
v_fst_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_fst_1591_);
if (lean_obj_tag(v_fst_1591_) == 1)
{
lean_object* v_snd_1592_; lean_object* v_val_1593_; lean_object* v___x_1594_; 
lean_dec(v_offset_1543_);
lean_dec_ref(v_e_1542_);
v_snd_1592_ = lean_ctor_get(v___x_1590_, 1);
lean_inc(v_snd_1592_);
lean_dec_ref(v___x_1590_);
v_val_1593_ = lean_ctor_get(v_fst_1591_, 0);
lean_inc(v_val_1593_);
lean_dec_ref(v_fst_1591_);
v___x_1594_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_val_1593_, v_a_1544_, v_a_1545_, v_snd_1592_);
return v___x_1594_;
}
else
{
lean_object* v_snd_1595_; 
lean_dec(v_fst_1591_);
v_snd_1595_ = lean_ctor_get(v___x_1590_, 1);
lean_inc(v_snd_1595_);
lean_dec_ref(v___x_1590_);
v_snd_1549_ = v_snd_1595_;
goto v___jp_1548_;
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_offset_1543_);
lean_dec_ref(v_e_1542_);
v___x_1596_ = lean_array_fget_borrowed(v_xs_1541_, v_i_1582_);
lean_dec(v_i_1582_);
lean_inc(v___x_1596_);
v___x_1597_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v___x_1596_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1597_;
}
}
else
{
lean_dec(v_numArgs_1586_);
lean_dec(v_i_1582_);
v_snd_1549_ = v_a_1546_;
goto v___jp_1548_;
}
}
}
}
else
{
lean_dec_ref(v___x_1568_);
v_snd_1549_ = v_a_1546_;
goto v___jp_1548_;
}
}
else
{
lean_object* v___x_1598_; 
lean_dec(v_offset_1543_);
v___x_1598_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1598_;
}
}
v___jp_1548_:
{
switch(lean_obj_tag(v_e_1542_))
{
case 9:
{
lean_object* v___x_1550_; 
lean_dec(v_offset_1543_);
v___x_1550_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_snd_1549_);
return v___x_1550_;
}
case 2:
{
lean_object* v___x_1551_; 
lean_dec(v_offset_1543_);
v___x_1551_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_snd_1549_);
return v___x_1551_;
}
case 0:
{
lean_object* v___x_1552_; 
lean_dec(v_offset_1543_);
v___x_1552_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_snd_1549_);
return v___x_1552_;
}
case 1:
{
lean_object* v___x_1553_; 
lean_dec(v_offset_1543_);
v___x_1553_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_snd_1549_);
return v___x_1553_;
}
case 4:
{
lean_object* v___x_1554_; 
lean_dec(v_offset_1543_);
v___x_1554_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_snd_1549_);
return v___x_1554_;
}
case 3:
{
lean_object* v___x_1555_; 
lean_dec(v_offset_1543_);
v___x_1555_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_e_1542_, v_a_1544_, v_a_1545_, v_snd_1549_);
return v___x_1555_;
}
default: 
{
lean_object* v___x_1556_; lean_object* v_fst_1557_; lean_object* v_snd_1558_; lean_object* v_fst_1559_; lean_object* v_snd_1560_; lean_object* v___x_1561_; 
v___x_1556_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1539_, v_varDeps_1540_, v_xs_1541_, v_e_1542_, v_offset_1543_, v_a_1544_, v_a_1545_, v_snd_1549_);
v_fst_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_fst_1557_);
v_snd_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_snd_1558_);
lean_dec_ref(v___x_1556_);
v_fst_1559_ = lean_ctor_get(v_fst_1557_, 0);
lean_inc(v_fst_1559_);
v_snd_1560_ = lean_ctor_get(v_fst_1557_, 1);
lean_inc(v_snd_1560_);
lean_dec(v_fst_1557_);
v___x_1561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1547_, v_fst_1559_, v_snd_1560_, v_a_1545_, v_snd_1558_);
return v___x_1561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object* v_n_1599_, lean_object* v_varDeps_1600_, lean_object* v_xs_1601_, lean_object* v_e_1602_, lean_object* v_offset_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
uint8_t v_a_boxed_1607_; lean_object* v_res_1608_; 
v_a_boxed_1607_ = lean_unbox(v_a_1605_);
v_res_1608_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1599_, v_varDeps_1600_, v_xs_1601_, v_e_1602_, v_offset_1603_, v_a_1604_, v_a_boxed_1607_, v_a_1606_);
lean_dec_ref(v_xs_1601_);
lean_dec_ref(v_varDeps_1600_);
lean_dec(v_n_1599_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_n_1609_, lean_object* v_varDeps_1610_, lean_object* v_xs_1611_, lean_object* v_e_1612_, lean_object* v_offset_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
uint8_t v_a_boxed_1617_; lean_object* v_res_1618_; 
v_a_boxed_1617_ = lean_unbox(v_a_1615_);
v_res_1618_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1609_, v_varDeps_1610_, v_xs_1611_, v_e_1612_, v_offset_1613_, v_a_1614_, v_a_boxed_1617_, v_a_1616_);
lean_dec_ref(v_xs_1611_);
lean_dec_ref(v_varDeps_1610_);
lean_dec(v_n_1609_);
return v_res_1618_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0(void){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_box(0));
return v___x_1619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_unsigned_to_nat(16u);
v___x_1622_ = lean_mk_array(v___x_1621_, v___x_1620_);
return v___x_1622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v___x_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object* v_e_1626_, lean_object* v_xs_1627_, lean_object* v_varDeps_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v_share_1632_; lean_object* v_maxFVar_1633_; lean_object* v_proofInstInfo_1634_; lean_object* v_inferType_1635_; lean_object* v_getLevel_1636_; lean_object* v_congrInfo_1637_; lean_object* v_defEqI_1638_; lean_object* v_extensions_1639_; lean_object* v_issues_1640_; lean_object* v_canon_1641_; uint8_t v_debug_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1712_; 
v___x_1631_ = lean_st_ref_take(v_a_1629_);
v_share_1632_ = lean_ctor_get(v___x_1631_, 0);
v_maxFVar_1633_ = lean_ctor_get(v___x_1631_, 1);
v_proofInstInfo_1634_ = lean_ctor_get(v___x_1631_, 2);
v_inferType_1635_ = lean_ctor_get(v___x_1631_, 3);
v_getLevel_1636_ = lean_ctor_get(v___x_1631_, 4);
v_congrInfo_1637_ = lean_ctor_get(v___x_1631_, 5);
v_defEqI_1638_ = lean_ctor_get(v___x_1631_, 6);
v_extensions_1639_ = lean_ctor_get(v___x_1631_, 7);
v_issues_1640_ = lean_ctor_get(v___x_1631_, 8);
v_canon_1641_ = lean_ctor_get(v___x_1631_, 9);
v_debug_1642_ = lean_ctor_get_uint8(v___x_1631_, sizeof(void*)*10);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1644_ = v___x_1631_;
v_isShared_1645_ = v_isSharedCheck_1712_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_canon_1641_);
lean_inc(v_issues_1640_);
lean_inc(v_extensions_1639_);
lean_inc(v_defEqI_1638_);
lean_inc(v_congrInfo_1637_);
lean_inc(v_getLevel_1636_);
lean_inc(v_inferType_1635_);
lean_inc(v_proofInstInfo_1634_);
lean_inc(v_maxFVar_1633_);
lean_inc(v_share_1632_);
lean_dec(v___x_1631_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1712_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_maxFVar_1633_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v_proofInstInfo_1634_);
lean_ctor_set(v_reuseFailAlloc_1711_, 3, v_inferType_1635_);
lean_ctor_set(v_reuseFailAlloc_1711_, 4, v_getLevel_1636_);
lean_ctor_set(v_reuseFailAlloc_1711_, 5, v_congrInfo_1637_);
lean_ctor_set(v_reuseFailAlloc_1711_, 6, v_defEqI_1638_);
lean_ctor_set(v_reuseFailAlloc_1711_, 7, v_extensions_1639_);
lean_ctor_set(v_reuseFailAlloc_1711_, 8, v_issues_1640_);
lean_ctor_set(v_reuseFailAlloc_1711_, 9, v_canon_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1711_, sizeof(void*)*10, v_debug_1642_);
v___x_1648_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_fst_1652_; lean_object* v_snd_1653_; uint8_t v_debug_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1649_ = lean_st_ref_set(v_a_1629_, v___x_1648_);
v___x_1650_ = lean_st_ref_get(v_a_1629_);
v_debug_1675_ = lean_ctor_get_uint8(v___x_1650_, sizeof(void*)*10);
lean_dec(v___x_1650_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = l_Lean_Expr_looseBVarRange(v_e_1626_);
v___x_1678_ = lean_nat_dec_le(v___x_1677_, v___x_1676_);
lean_dec(v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v_n_1679_; lean_object* v_snd_1681_; lean_object* v___x_1687_; 
v_n_1679_ = lean_array_get_size(v_xs_1627_);
v___x_1687_ = l_Lean_Expr_getAppFn(v_e_1626_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_deBruijnIndex_1688_; uint8_t v___x_1689_; 
v_deBruijnIndex_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_deBruijnIndex_1688_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = lean_nat_dec_le(v___x_1676_, v_deBruijnIndex_1688_);
if (v___x_1689_ == 0)
{
lean_dec(v_deBruijnIndex_1688_);
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_share_1632_;
goto v___jp_1651_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_lt(v_deBruijnIndex_1688_, v_n_1679_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_fst_1693_; lean_object* v_snd_1694_; 
lean_dec_ref(v_e_1626_);
v___x_1691_ = lean_nat_sub(v_deBruijnIndex_1688_, v_n_1679_);
lean_dec(v_deBruijnIndex_1688_);
v___x_1692_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1691_, v_share_1632_);
v_fst_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_fst_1693_);
v_snd_1694_ = lean_ctor_get(v___x_1692_, 1);
lean_inc(v_snd_1694_);
lean_dec_ref(v___x_1692_);
v_fst_1652_ = v_fst_1693_;
v_snd_1653_ = v_snd_1694_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_i_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_expectedNumArgs_1700_; lean_object* v_numArgs_1701_; uint8_t v___x_1702_; 
v___x_1695_ = lean_nat_sub(v_n_1679_, v_deBruijnIndex_1688_);
lean_dec(v_deBruijnIndex_1688_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v_i_1697_ = lean_nat_sub(v___x_1695_, v___x_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1699_ = lean_array_get_borrowed(v___x_1698_, v_varDeps_1628_, v_i_1697_);
v_expectedNumArgs_1700_ = lean_array_get_size(v___x_1699_);
v_numArgs_1701_ = l_Lean_Expr_getAppNumArgs(v_e_1626_);
v___x_1702_ = lean_nat_dec_lt(v_expectedNumArgs_1700_, v_numArgs_1701_);
if (v___x_1702_ == 0)
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_nat_dec_eq(v_numArgs_1701_, v_expectedNumArgs_1700_);
lean_dec(v_numArgs_1701_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_fst_1706_; 
lean_dec(v_i_1697_);
v___x_1704_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1705_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1704_, v_debug_1675_, v_share_1632_);
v_fst_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_fst_1706_);
if (lean_obj_tag(v_fst_1706_) == 1)
{
lean_object* v_snd_1707_; lean_object* v_val_1708_; 
lean_dec_ref(v_e_1626_);
v_snd_1707_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_snd_1707_);
lean_dec_ref(v___x_1705_);
v_val_1708_ = lean_ctor_get(v_fst_1706_, 0);
lean_inc(v_val_1708_);
lean_dec_ref(v_fst_1706_);
v_fst_1652_ = v_val_1708_;
v_snd_1653_ = v_snd_1707_;
goto v___jp_1651_;
}
else
{
lean_object* v_snd_1709_; 
lean_dec(v_fst_1706_);
v_snd_1709_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_snd_1709_);
lean_dec_ref(v___x_1705_);
v_snd_1681_ = v_snd_1709_;
goto v___jp_1680_;
}
}
else
{
lean_object* v___x_1710_; 
lean_dec_ref(v_e_1626_);
v___x_1710_ = lean_array_fget_borrowed(v_xs_1627_, v_i_1697_);
lean_dec(v_i_1697_);
lean_inc(v___x_1710_);
v_fst_1652_ = v___x_1710_;
v_snd_1653_ = v_share_1632_;
goto v___jp_1651_;
}
}
else
{
lean_dec(v_numArgs_1701_);
lean_dec(v_i_1697_);
v_snd_1681_ = v_share_1632_;
goto v___jp_1680_;
}
}
}
}
else
{
lean_dec_ref(v___x_1687_);
v_snd_1681_ = v_share_1632_;
goto v___jp_1680_;
}
v___jp_1680_:
{
switch(lean_obj_tag(v_e_1626_))
{
case 9:
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_snd_1681_;
goto v___jp_1651_;
}
case 2:
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_snd_1681_;
goto v___jp_1651_;
}
case 0:
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_snd_1681_;
goto v___jp_1651_;
}
case 1:
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_snd_1681_;
goto v___jp_1651_;
}
case 4:
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_snd_1681_;
goto v___jp_1651_;
}
case 3:
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_snd_1681_;
goto v___jp_1651_;
}
default: 
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v_fst_1686_; 
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2);
v___x_1683_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1679_, v_varDeps_1628_, v_xs_1627_, v_e_1626_, v___x_1676_, v___x_1682_, v_debug_1675_, v_snd_1681_);
v_fst_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_fst_1684_);
v_snd_1685_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_snd_1685_);
lean_dec_ref(v___x_1683_);
v_fst_1686_ = lean_ctor_get(v_fst_1684_, 0);
lean_inc(v_fst_1686_);
lean_dec(v_fst_1684_);
v_fst_1652_ = v_fst_1686_;
v_snd_1653_ = v_snd_1685_;
goto v___jp_1651_;
}
}
}
}
else
{
v_fst_1652_ = v_e_1626_;
v_snd_1653_ = v_share_1632_;
goto v___jp_1651_;
}
v___jp_1651_:
{
lean_object* v___x_1654_; lean_object* v_maxFVar_1655_; lean_object* v_proofInstInfo_1656_; lean_object* v_inferType_1657_; lean_object* v_getLevel_1658_; lean_object* v_congrInfo_1659_; lean_object* v_defEqI_1660_; lean_object* v_extensions_1661_; lean_object* v_issues_1662_; lean_object* v_canon_1663_; uint8_t v_debug_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v___x_1654_ = lean_st_ref_take(v_a_1629_);
v_maxFVar_1655_ = lean_ctor_get(v___x_1654_, 1);
v_proofInstInfo_1656_ = lean_ctor_get(v___x_1654_, 2);
v_inferType_1657_ = lean_ctor_get(v___x_1654_, 3);
v_getLevel_1658_ = lean_ctor_get(v___x_1654_, 4);
v_congrInfo_1659_ = lean_ctor_get(v___x_1654_, 5);
v_defEqI_1660_ = lean_ctor_get(v___x_1654_, 6);
v_extensions_1661_ = lean_ctor_get(v___x_1654_, 7);
v_issues_1662_ = lean_ctor_get(v___x_1654_, 8);
v_canon_1663_ = lean_ctor_get(v___x_1654_, 9);
v_debug_1664_ = lean_ctor_get_uint8(v___x_1654_, sizeof(void*)*10);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1674_);
v___x_1666_ = v___x_1654_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_canon_1663_);
lean_inc(v_issues_1662_);
lean_inc(v_extensions_1661_);
lean_inc(v_defEqI_1660_);
lean_inc(v_congrInfo_1659_);
lean_inc(v_getLevel_1658_);
lean_inc(v_inferType_1657_);
lean_inc(v_proofInstInfo_1656_);
lean_inc(v_maxFVar_1655_);
lean_dec(v___x_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v_snd_1653_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_snd_1653_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_maxFVar_1655_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_proofInstInfo_1656_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_inferType_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v_getLevel_1658_);
lean_ctor_set(v_reuseFailAlloc_1672_, 5, v_congrInfo_1659_);
lean_ctor_set(v_reuseFailAlloc_1672_, 6, v_defEqI_1660_);
lean_ctor_set(v_reuseFailAlloc_1672_, 7, v_extensions_1661_);
lean_ctor_set(v_reuseFailAlloc_1672_, 8, v_issues_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 9, v_canon_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1672_, sizeof(void*)*10, v_debug_1664_);
v___x_1669_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_st_ref_set(v_a_1629_, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_fst_1652_);
return v___x_1671_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object* v_e_1713_, lean_object* v_xs_1714_, lean_object* v_varDeps_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1713_, v_xs_1714_, v_varDeps_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_varDeps_1715_);
lean_dec_ref(v_xs_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1719_, lean_object* v_xs_1720_, lean_object* v_varDeps_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1719_, v_xs_1720_, v_varDeps_1721_, v_a_1723_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1730_, lean_object* v_xs_1731_, lean_object* v_varDeps_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1730_, v_xs_1731_, v_varDeps_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec_ref(v_varDeps_1732_);
lean_dec_ref(v_xs_1731_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1741_, lean_object* v_m_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1742_, v_a_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1745_, lean_object* v_m_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(v_00_u03b2_1745_, v_m_1746_, v_a_1747_);
lean_dec_ref(v_a_1747_);
lean_dec_ref(v_m_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_1749_, lean_object* v_a_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1750_, v_x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1753_, lean_object* v_a_1754_, lean_object* v_x_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(v_00_u03b2_1753_, v_a_1754_, v_x_1755_);
lean_dec(v_x_1755_);
lean_dec_ref(v_a_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1757_, lean_object* v_type_1758_, lean_object* v_val_1759_, lean_object* v_k_1760_, uint8_t v_nondep_1761_, uint8_t v_kind_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___f_1770_; lean_object* v___x_1771_; 
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1770_, 0, v_k_1760_);
lean_closure_set(v___f_1770_, 1, v___y_1763_);
lean_closure_set(v___f_1770_, 2, v___y_1764_);
v___x_1771_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1757_, v_type_1758_, v_val_1759_, v___f_1770_, v_nondep_1761_, v_kind_1762_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1771_) == 0)
{
return v___x_1771_;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1780_, lean_object* v_type_1781_, lean_object* v_val_1782_, lean_object* v_k_1783_, lean_object* v_nondep_1784_, lean_object* v_kind_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v_nondep_boxed_1793_; uint8_t v_kind_boxed_1794_; lean_object* v_res_1795_; 
v_nondep_boxed_1793_ = lean_unbox(v_nondep_1784_);
v_kind_boxed_1794_ = lean_unbox(v_kind_1785_);
v_res_1795_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1780_, v_type_1781_, v_val_1782_, v_k_1783_, v_nondep_boxed_1793_, v_kind_boxed_1794_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1796_, lean_object* v_name_1797_, lean_object* v_type_1798_, lean_object* v_val_1799_, lean_object* v_k_1800_, uint8_t v_nondep_1801_, uint8_t v_kind_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1797_, v_type_1798_, v_val_1799_, v_k_1800_, v_nondep_1801_, v_kind_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_name_1812_, lean_object* v_type_1813_, lean_object* v_val_1814_, lean_object* v_k_1815_, lean_object* v_nondep_1816_, lean_object* v_kind_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_nondep_boxed_1825_; uint8_t v_kind_boxed_1826_; lean_object* v_res_1827_; 
v_nondep_boxed_1825_ = lean_unbox(v_nondep_1816_);
v_kind_boxed_1826_ = lean_unbox(v_kind_1817_);
v_res_1827_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_1811_, v_name_1812_, v_type_1813_, v_val_1814_, v_k_1815_, v_nondep_boxed_1825_, v_kind_boxed_1826_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1827_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object* v_msg_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_2402__overap_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0);
v___x_2402__overap_1838_ = lean_panic_fn_borrowed(v___x_1837_, v_msg_1829_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1839_ = lean_apply_7(v___x_2402__overap_1838_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, lean_box(0));
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v_msg_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_1849_, size_t v_sz_1850_, size_t v_i_1851_, lean_object* v_bs_1852_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_usize_dec_lt(v_i_1851_, v_sz_1850_);
if (v___x_1853_ == 0)
{
return v_bs_1852_;
}
else
{
lean_object* v_v_1854_; lean_object* v___x_1855_; lean_object* v_bs_x27_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v_v_1854_ = lean_array_uget(v_bs_1852_, v_i_1851_);
v___x_1855_ = lean_unsigned_to_nat(0u);
v_bs_x27_1856_ = lean_array_uset(v_bs_1852_, v_i_1851_, v___x_1855_);
v___x_1857_ = l_Lean_instInhabitedExpr;
v___x_1858_ = lean_array_get_borrowed(v___x_1857_, v_xs_1849_, v_v_1854_);
lean_dec(v_v_1854_);
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = lean_usize_add(v_i_1851_, v___x_1859_);
lean_inc(v___x_1858_);
v___x_1861_ = lean_array_uset(v_bs_x27_1856_, v_i_1851_, v___x_1858_);
v_i_1851_ = v___x_1860_;
v_bs_1852_ = v___x_1861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_1863_, lean_object* v_sz_1864_, lean_object* v_i_1865_, lean_object* v_bs_1866_){
_start:
{
size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1864_);
lean_dec(v_sz_1864_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1863_, v_sz_boxed_1867_, v_i_boxed_1868_, v_bs_1866_);
lean_dec_ref(v_xs_1863_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_1870_, lean_object* v_i_1871_, lean_object* v_varDeps_1872_, lean_object* v_args_1873_, lean_object* v_body_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_1870_, v_i_1871_, v_varDeps_1872_, v_args_1873_, v_body_1874_, v_x_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v_i_1871_);
return v_res_1883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1885_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1886_ = lean_unsigned_to_nat(30u);
v___x_1887_ = lean_unsigned_to_nat(254u);
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_1889_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1890_ = l_mkPanicMessageWithDecl(v___x_1889_, v___x_1888_, v___x_1887_, v___x_1886_, v___x_1885_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_1891_, lean_object* v_args_1892_, lean_object* v_f_1893_, lean_object* v_xs_1894_, lean_object* v_i_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_array_get_size(v_args_1892_);
v___x_1904_ = lean_nat_dec_lt(v_i_1895_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v_a_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; 
lean_dec(v_i_1895_);
lean_dec_ref(v_args_1892_);
v___x_1905_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_f_1893_, v_xs_1894_, v_varDeps_1891_, v_a_1897_);
lean_dec_ref(v_varDeps_1891_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = 1;
v___x_1908_ = l_Lean_Meta_mkLetFVars(v_xs_1894_, v_a_1906_, v___x_1904_, v___x_1904_, v___x_1907_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec_ref(v_xs_1894_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_1909_, v_a_1897_);
return v___x_1910_;
}
else
{
return v___x_1908_;
}
}
else
{
if (lean_obj_tag(v_f_1893_) == 6)
{
lean_object* v_binderName_1911_; lean_object* v_binderType_1912_; lean_object* v_body_1913_; lean_object* v_varPos_1914_; size_t v_sz_1915_; size_t v___x_1916_; lean_object* v_ys_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_binderName_1911_ = lean_ctor_get(v_f_1893_, 0);
lean_inc(v_binderName_1911_);
v_binderType_1912_ = lean_ctor_get(v_f_1893_, 1);
lean_inc_ref(v_binderType_1912_);
v_body_1913_ = lean_ctor_get(v_f_1893_, 2);
lean_inc_ref(v_body_1913_);
lean_dec_ref(v_f_1893_);
v_varPos_1914_ = lean_array_fget(v_varDeps_1891_, v_i_1895_);
v_sz_1915_ = lean_array_size(v_varPos_1914_);
v___x_1916_ = ((size_t)0ULL);
lean_inc(v_varPos_1914_);
v_ys_1917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1894_, v_sz_1915_, v___x_1916_, v_varPos_1914_);
v___x_1918_ = lean_array_fget_borrowed(v_args_1892_, v_i_1895_);
v___x_1919_ = 0;
lean_inc(v___x_1918_);
v___x_1920_ = l_Lean_Expr_betaRev(v___x_1918_, v_ys_1917_, v___x_1919_, v___x_1919_);
lean_dec_ref(v_ys_1917_);
v___x_1921_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1920_, v_a_1897_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; lean_object* v_type_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
v___f_1923_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1923_, 0, v_xs_1894_);
lean_closure_set(v___f_1923_, 1, v_i_1895_);
lean_closure_set(v___f_1923_, 2, v_varDeps_1891_);
lean_closure_set(v___f_1923_, 3, v_args_1892_);
lean_closure_set(v___f_1923_, 4, v_body_1913_);
v___x_1924_ = lean_array_get_size(v_varPos_1914_);
lean_dec(v_varPos_1914_);
v_type_1925_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_1912_, v___x_1924_);
v___x_1926_ = 0;
v___x_1927_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_1911_, v_type_1925_, v_a_1922_, v___f_1923_, v___x_1904_, v___x_1926_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_1927_;
}
else
{
lean_dec(v_varPos_1914_);
lean_dec_ref(v_body_1913_);
lean_dec_ref(v_binderType_1912_);
lean_dec(v_binderName_1911_);
lean_dec(v_i_1895_);
lean_dec_ref(v_xs_1894_);
lean_dec_ref(v_args_1892_);
lean_dec_ref(v_varDeps_1891_);
return v___x_1921_;
}
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_i_1895_);
lean_dec_ref(v_xs_1894_);
lean_dec_ref(v_f_1893_);
lean_dec_ref(v_args_1892_);
lean_dec_ref(v_varDeps_1891_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_1929_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1928_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_1930_, lean_object* v_i_1931_, lean_object* v_varDeps_1932_, lean_object* v_args_1933_, lean_object* v_body_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_x_1935_, v___y_1937_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = lean_array_push(v_xs_1930_, v_a_1944_);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = lean_nat_add(v_i_1931_, v___x_1946_);
v___x_1948_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1932_, v_args_1933_, v_body_1934_, v___x_1945_, v___x_1947_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1948_;
}
else
{
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_args_1933_);
lean_dec_ref(v_varDeps_1932_);
lean_dec_ref(v_xs_1930_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_1949_, lean_object* v_args_1950_, lean_object* v_f_1951_, lean_object* v_xs_1952_, lean_object* v_i_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1949_, v_args_1950_, v_f_1951_, v_xs_1952_, v_i_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_1962_, lean_object* v_args_1963_, lean_object* v___h_1964_, lean_object* v_f_1965_, lean_object* v_xs_1966_, lean_object* v_i_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1962_, v_args_1963_, v_f_1965_, v_xs_1966_, v_i_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_1976_, lean_object* v_args_1977_, lean_object* v___h_1978_, lean_object* v_f_1979_, lean_object* v_xs_1980_, lean_object* v_i_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_1976_, v_args_1977_, v___h_1978_, v_f_1979_, v_xs_1980_, v_i_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
return v_res_1989_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1992_ = lean_unsigned_to_nat(40u);
v___x_1993_ = lean_unsigned_to_nat(251u);
v___x_1994_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1996_ = l_mkPanicMessageWithDecl(v___x_1995_, v___x_1994_, v___x_1993_, v___x_1992_, v___x_1991_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
if (lean_obj_tag(v_x_1998_) == 5)
{
lean_object* v_fn_2008_; lean_object* v_arg_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_fn_2008_ = lean_ctor_get(v_x_1998_, 0);
lean_inc_ref(v_fn_2008_);
v_arg_2009_ = lean_ctor_get(v_x_1998_, 1);
lean_inc_ref(v_arg_2009_);
lean_dec_ref(v_x_1998_);
v___x_2010_ = lean_array_set(v_x_1999_, v_x_2000_, v_arg_2009_);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_nat_sub(v_x_2000_, v___x_2011_);
lean_dec(v_x_2000_);
v_x_1998_ = v_fn_2008_;
v_x_1999_ = v___x_2010_;
v_x_2000_ = v___x_2012_;
goto _start;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
lean_dec(v_x_2000_);
v___x_2014_ = lean_array_get_size(v_x_1999_);
v___x_2015_ = lean_array_get_size(v_varDeps_1997_);
v___x_2016_ = lean_nat_dec_eq(v___x_2014_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_x_1999_);
lean_dec_ref(v_x_1998_);
lean_dec_ref(v_varDeps_1997_);
v___x_2017_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2018_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_2017_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2021_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1997_, v_x_1999_, v_x_1998_, v___x_2020_, v___x_2019_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2022_, v_x_2023_, v_x_2024_, v_x_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2033_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2034_; lean_object* v_dummy_2035_; 
v___x_2034_ = lean_box(0);
v_dummy_2035_ = l_Lean_Expr_sort___override(v___x_2034_);
return v_dummy_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2036_, lean_object* v_varDeps_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_dummy_2045_; lean_object* v_nargs_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_dummy_2045_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2046_ = l_Lean_Expr_getAppNumArgs(v_e_2036_);
lean_inc(v_nargs_2046_);
v___x_2047_ = lean_mk_array(v_nargs_2046_, v_dummy_2045_);
v___x_2048_ = lean_unsigned_to_nat(1u);
v___x_2049_ = lean_nat_sub(v_nargs_2046_, v___x_2048_);
lean_dec(v_nargs_2046_);
v___x_2050_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2037_, v_e_2036_, v___x_2047_, v___x_2049_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2051_, lean_object* v_varDeps_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2051_, v_varDeps_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2061_, lean_object* v_b_2062_){
_start:
{
lean_object* v_snd_2064_; lean_object* v_fst_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2098_; 
v_snd_2064_ = lean_ctor_get(v_b_2062_, 1);
v_fst_2065_ = lean_ctor_get(v_b_2062_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_b_2062_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2067_ = v_b_2062_;
v_isShared_2068_ = v_isSharedCheck_2098_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snd_2064_);
lean_inc(v_fst_2065_);
lean_dec(v_b_2062_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2098_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2097_; 
v_fst_2069_ = lean_ctor_get(v_snd_2064_, 0);
v_snd_2070_ = lean_ctor_get(v_snd_2064_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_snd_2064_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2072_ = v_snd_2064_;
v_isShared_2073_ = v_isSharedCheck_2097_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snd_2070_);
lean_inc(v_fst_2069_);
lean_dec(v_snd_2064_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2097_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_nat_dec_lt(v___x_2074_, v_fst_2069_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2077_; 
if (v_isShared_2073_ == 0)
{
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_fst_2069_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_snd_2070_);
v___x_2077_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2077_);
v___x_2079_ = v___x_2067_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_fst_2065_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_nat_sub(v_fst_2069_, v___x_2083_);
lean_dec(v_fst_2069_);
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_array_get_borrowed(v___x_2085_, v_argUnivs_2061_, v___x_2084_);
lean_inc(v___x_2086_);
v___x_2087_ = l_Lean_mkLevelIMax_x27(v___x_2086_, v_fst_2065_);
v___x_2088_ = l_Lean_Level_normalize(v___x_2087_);
lean_dec(v___x_2087_);
lean_inc(v___x_2088_);
v___x_2089_ = lean_array_push(v_snd_2070_, v___x_2088_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2089_);
lean_ctor_set(v___x_2072_, 0, v___x_2084_);
v___x_2091_ = v___x_2072_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2091_);
lean_ctor_set(v___x_2067_, 0, v___x_2088_);
v___x_2093_ = v___x_2067_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v_b_2062_ = v___x_2093_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2099_, v_b_2100_);
lean_dec_ref(v_argUnivs_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2105_, lean_object* v_argUnivs_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
if (lean_obj_tag(v_type_2105_) == 7)
{
lean_object* v_binderType_2114_; lean_object* v_body_2115_; lean_object* v___x_2116_; 
v_binderType_2114_ = lean_ctor_get(v_type_2105_, 1);
lean_inc_ref(v_binderType_2114_);
v_body_2115_ = lean_ctor_get(v_type_2105_, 2);
lean_inc_ref(v_body_2115_);
lean_dec_ref(v_type_2105_);
v___x_2116_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2114_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = lean_array_push(v_argUnivs_2106_, v_a_2117_);
v_type_2105_ = v_body_2115_;
v_argUnivs_2106_ = v___x_2118_;
goto _start;
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_body_2115_);
lean_dec_ref(v_argUnivs_2106_);
v_a_2120_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2116_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2116_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2105_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = lean_array_get_size(v_argUnivs_2106_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_a_2129_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2106_, v___x_2133_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2153_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2153_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2153_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_snd_2139_; lean_object* v_snd_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2151_; 
v_snd_2139_ = lean_ctor_get(v_a_2135_, 1);
lean_inc(v_snd_2139_);
lean_dec(v_a_2135_);
v_snd_2140_ = lean_ctor_get(v_snd_2139_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_snd_2139_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_snd_2139_, 0);
lean_dec(v_unused_2152_);
v___x_2142_ = v_snd_2139_;
v_isShared_2143_ = v_isSharedCheck_2151_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_snd_2140_);
lean_dec(v_snd_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2151_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2144_ = l_Array_reverse___redArg(v_snd_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 1, v___x_2144_);
lean_ctor_set(v___x_2142_, 0, v_argUnivs_2106_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_argUnivs_2106_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2146_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_argUnivs_2106_);
v_a_2154_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2134_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2134_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_argUnivs_2106_);
v_a_2162_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2128_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2128_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2170_, lean_object* v_argUnivs_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2170_, v_argUnivs_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2180_, v_b_2181_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2190_, lean_object* v_b_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2190_, v_b_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v_argUnivs_2190_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2209_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2200_, v___x_2208_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2219_, lean_object* v_argUnivs_2220_, lean_object* v_declName_2221_, lean_object* v_fType_2222_, lean_object* v_i_2223_){
_start:
{
lean_object* v___x_2225_; lean_object* v_00_u03b1_2226_; lean_object* v_00_u03b2_2227_; lean_object* v_u_2228_; lean_object* v_v_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2225_ = lean_box(0);
v_00_u03b1_2226_ = l_Lean_Expr_bindingDomain_x21(v_fType_2222_);
v_00_u03b2_2227_ = l_Lean_Expr_bindingBody_x21(v_fType_2222_);
v_u_2228_ = lean_array_get_borrowed(v___x_2225_, v_argUnivs_2220_, v_i_2223_);
v_v_2229_ = lean_array_get_borrowed(v___x_2225_, v_fnUnivs_2219_, v_i_2223_);
v___x_2230_ = lean_box(0);
lean_inc(v_v_2229_);
v___x_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2231_, 0, v_v_2229_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
lean_inc(v_u_2228_);
v___x_2232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2232_, 0, v_u_2228_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_mkConst(v_declName_2221_, v___x_2232_);
v___x_2234_ = l_Lean_mkAppB(v___x_2233_, v_00_u03b1_2226_, v_00_u03b2_2227_);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2236_, lean_object* v_argUnivs_2237_, lean_object* v_declName_2238_, lean_object* v_fType_2239_, lean_object* v_i_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2236_, v_argUnivs_2237_, v_declName_2238_, v_fType_2239_, v_i_2240_);
lean_dec(v_i_2240_);
lean_dec_ref(v_fType_2239_);
lean_dec_ref(v_argUnivs_2237_);
lean_dec_ref(v_fnUnivs_2236_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2243_, lean_object* v_argUnivs_2244_, lean_object* v_declName_2245_, lean_object* v_fType_2246_, lean_object* v_i_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2243_, v_argUnivs_2244_, v_declName_2245_, v_fType_2246_, v_i_2247_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2256_, lean_object* v_argUnivs_2257_, lean_object* v_declName_2258_, lean_object* v_fType_2259_, lean_object* v_i_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2256_, v_argUnivs_2257_, v_declName_2258_, v_fType_2259_, v_i_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_i_2260_);
lean_dec_ref(v_fType_2259_);
lean_dec_ref(v_argUnivs_2257_);
lean_dec_ref(v_fnUnivs_2256_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2269_, lean_object* v_a_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___y_2279_; lean_object* v___x_2282_; uint8_t v_debug_2283_; 
v___x_2282_ = lean_st_ref_get(v___y_2272_);
v_debug_2283_ = lean_ctor_get_uint8(v___x_2282_, sizeof(void*)*10);
lean_dec(v___x_2282_);
if (v_debug_2283_ == 0)
{
v___y_2279_ = v___y_2272_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2284_; 
lean_inc_ref(v_f_2269_);
v___x_2284_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2269_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; 
lean_dec_ref(v___x_2284_);
lean_inc_ref(v_a_2270_);
v___x_2285_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_dec_ref(v___x_2285_);
v___y_2279_ = v___y_2272_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_a_2270_);
lean_dec_ref(v_f_2269_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_a_2270_);
lean_dec_ref(v_f_2269_);
v_a_2294_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2284_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2284_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
v___jp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = l_Lean_Expr_app___override(v_f_2269_, v_a_2270_);
v___x_2281_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2280_, v___y_2279_);
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2302_, lean_object* v_a_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2302_, v_a_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2312_, lean_object* v_a_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2312_, v_a_2313_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2325_, lean_object* v_a_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2325_, v_a_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
return v_res_2337_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_15370__overap_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15370__overap_2351_ = lean_panic_fn_borrowed(v___x_2350_, v_msg_2339_);
lean_inc(v___y_2348_);
lean_inc_ref(v___y_2347_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v___y_2344_);
lean_inc_ref(v___y_2343_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
lean_inc(v___y_2340_);
v___x_2352_ = lean_apply_10(v___x_15370__overap_2351_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, lean_box(0));
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
return v_res_2364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_2376_ = lean_unsigned_to_nat(11u);
v___x_2377_ = lean_unsigned_to_nat(346u);
v___x_2378_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_2380_ = l_mkPanicMessageWithDecl(v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_, v___x_2375_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2381_, lean_object* v_fnUnivs_2382_, lean_object* v_argUnivs_2383_, lean_object* v_simpBody_2384_, lean_object* v_e_2385_, lean_object* v_i_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
switch(lean_obj_tag(v_e_2385_))
{
case 5:
{
lean_object* v_fn_2397_; lean_object* v_arg_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_fn_2397_ = lean_ctor_get(v_e_2385_, 0);
lean_inc_ref_n(v_fn_2397_, 2);
v_arg_2398_ = lean_ctor_get(v_e_2385_, 1);
lean_inc_ref(v_arg_2398_);
lean_dec_ref(v_e_2385_);
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_sub(v_i_2386_, v___x_2399_);
v___x_2401_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2381_, v_fnUnivs_2382_, v_argUnivs_2383_, v_simpBody_2384_, v_fn_2397_, v___x_2400_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
lean_dec(v___x_2400_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2522_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2522_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2522_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v_fst_2406_; lean_object* v_snd_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2521_; 
v_fst_2406_ = lean_ctor_get(v_a_2402_, 0);
v_snd_2407_ = lean_ctor_get(v_a_2402_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2402_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2409_ = v_a_2402_;
v_isShared_2410_ = v_isSharedCheck_2521_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_snd_2407_);
lean_inc(v_fst_2406_);
lean_dec(v_a_2402_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2521_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_r_2412_; lean_object* v___x_2420_; 
lean_inc(v_a_2395_);
lean_inc_ref(v_a_2394_);
lean_inc(v_a_2393_);
lean_inc_ref(v_a_2392_);
lean_inc(v_a_2391_);
lean_inc_ref(v_a_2390_);
lean_inc(v_a_2389_);
lean_inc_ref(v_a_2388_);
lean_inc(v_a_2387_);
lean_inc_ref(v_arg_2398_);
v___x_2420_ = lean_sym_simp(v_arg_2398_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; uint8_t v___y_2423_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
if (lean_obj_tag(v_fst_2406_) == 0)
{
if (lean_obj_tag(v_a_2421_) == 0)
{
uint8_t v_contextDependent_2425_; 
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_fn_2397_);
v_contextDependent_2425_ = lean_ctor_get_uint8(v_fst_2406_, 1);
lean_dec_ref(v_fst_2406_);
if (v_contextDependent_2425_ == 0)
{
uint8_t v_contextDependent_2426_; 
v_contextDependent_2426_ = lean_ctor_get_uint8(v_a_2421_, 1);
lean_dec_ref(v_a_2421_);
v___y_2423_ = v_contextDependent_2426_;
goto v___jp_2422_;
}
else
{
lean_dec_ref(v_a_2421_);
v___y_2423_ = v_contextDependent_2425_;
goto v___jp_2422_;
}
}
else
{
uint8_t v_contextDependent_2427_; lean_object* v_e_x27_2428_; lean_object* v_proof_2429_; uint8_t v_contextDependent_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2454_; 
v_contextDependent_2427_ = lean_ctor_get_uint8(v_fst_2406_, 1);
lean_dec_ref(v_fst_2406_);
v_e_x27_2428_ = lean_ctor_get(v_a_2421_, 0);
v_proof_2429_ = lean_ctor_get(v_a_2421_, 1);
v_contextDependent_2430_ = lean_ctor_get_uint8(v_a_2421_, sizeof(void*)*2 + 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_a_2421_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2432_ = v_a_2421_;
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_proof_2429_);
lean_inc(v_e_x27_2428_);
lean_dec(v_a_2421_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; 
lean_inc_ref(v_e_x27_2428_);
lean_inc_ref(v_fn_2397_);
v___x_2434_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2397_, v_e_x27_2428_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_a_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; uint8_t v___y_2442_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2437_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2382_, v_argUnivs_2383_, v___x_2436_, v_snd_2407_, v_i_2386_);
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = l_Lean_mkApp4(v_a_2438_, v_arg_2398_, v_e_x27_2428_, v_fn_2397_, v_proof_2429_);
v___x_2440_ = 0;
if (v_contextDependent_2427_ == 0)
{
v___y_2442_ = v_contextDependent_2430_;
goto v___jp_2441_;
}
else
{
v___y_2442_ = v_contextDependent_2427_;
goto v___jp_2441_;
}
v___jp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___x_2439_);
lean_ctor_set(v___x_2432_, 0, v_a_2435_);
v___x_2444_ = v___x_2432_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2435_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*2, v___x_2440_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*2 + 1, v___y_2442_);
v_r_2412_ = v___x_2444_;
goto v___jp_2411_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_del_object(v___x_2432_);
lean_dec_ref(v_proof_2429_);
lean_dec_ref(v_e_x27_2428_);
lean_del_object(v___x_2409_);
lean_dec(v_snd_2407_);
lean_del_object(v___x_2404_);
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_fn_2397_);
v_a_2446_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2434_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2434_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2421_) == 0)
{
lean_object* v_e_x27_2455_; lean_object* v_proof_2456_; uint8_t v_contextDependent_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2482_; 
v_e_x27_2455_ = lean_ctor_get(v_fst_2406_, 0);
v_proof_2456_ = lean_ctor_get(v_fst_2406_, 1);
v_contextDependent_2457_ = lean_ctor_get_uint8(v_fst_2406_, sizeof(void*)*2 + 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_fst_2406_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2459_ = v_fst_2406_;
v_isShared_2460_ = v_isSharedCheck_2482_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_proof_2456_);
lean_inc(v_e_x27_2455_);
lean_dec(v_fst_2406_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2482_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v_contextDependent_2461_; lean_object* v___x_2462_; 
v_contextDependent_2461_ = lean_ctor_get_uint8(v_a_2421_, 1);
lean_dec_ref(v_a_2421_);
lean_inc_ref(v_arg_2398_);
lean_inc_ref(v_e_x27_2455_);
v___x_2462_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2455_, v_arg_2398_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v_a_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; uint8_t v___y_2470_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2465_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2382_, v_argUnivs_2383_, v___x_2464_, v_snd_2407_, v_i_2386_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref(v___x_2465_);
v___x_2467_ = l_Lean_mkApp4(v_a_2466_, v_fn_2397_, v_e_x27_2455_, v_proof_2456_, v_arg_2398_);
v___x_2468_ = 0;
if (v_contextDependent_2457_ == 0)
{
v___y_2470_ = v_contextDependent_2461_;
goto v___jp_2469_;
}
else
{
v___y_2470_ = v_contextDependent_2457_;
goto v___jp_2469_;
}
v___jp_2469_:
{
lean_object* v___x_2472_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2467_);
lean_ctor_set(v___x_2459_, 0, v_a_2463_);
v___x_2472_ = v___x_2459_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2463_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*2, v___x_2468_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*2 + 1, v___y_2470_);
v_r_2412_ = v___x_2472_;
goto v___jp_2411_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_del_object(v___x_2459_);
lean_dec_ref(v_proof_2456_);
lean_dec_ref(v_e_x27_2455_);
lean_del_object(v___x_2409_);
lean_dec(v_snd_2407_);
lean_del_object(v___x_2404_);
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_fn_2397_);
v_a_2474_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2462_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2462_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2483_; lean_object* v_proof_2484_; uint8_t v_contextDependent_2485_; lean_object* v_e_x27_2486_; lean_object* v_proof_2487_; uint8_t v_contextDependent_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2512_; 
v_e_x27_2483_ = lean_ctor_get(v_fst_2406_, 0);
lean_inc_ref(v_e_x27_2483_);
v_proof_2484_ = lean_ctor_get(v_fst_2406_, 1);
lean_inc_ref(v_proof_2484_);
v_contextDependent_2485_ = lean_ctor_get_uint8(v_fst_2406_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_2406_);
v_e_x27_2486_ = lean_ctor_get(v_a_2421_, 0);
v_proof_2487_ = lean_ctor_get(v_a_2421_, 1);
v_contextDependent_2488_ = lean_ctor_get_uint8(v_a_2421_, sizeof(void*)*2 + 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2421_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2490_ = v_a_2421_;
v_isShared_2491_ = v_isSharedCheck_2512_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_proof_2487_);
lean_inc(v_e_x27_2486_);
lean_dec(v_a_2421_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2512_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; 
lean_inc_ref(v_e_x27_2486_);
lean_inc_ref(v_e_x27_2483_);
v___x_2492_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2483_, v_e_x27_2486_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; uint8_t v___y_2500_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2495_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2382_, v_argUnivs_2383_, v___x_2494_, v_snd_2407_, v_i_2386_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = l_Lean_mkApp6(v_a_2496_, v_fn_2397_, v_e_x27_2483_, v_arg_2398_, v_e_x27_2486_, v_proof_2484_, v_proof_2487_);
v___x_2498_ = 0;
if (v_contextDependent_2485_ == 0)
{
v___y_2500_ = v_contextDependent_2488_;
goto v___jp_2499_;
}
else
{
v___y_2500_ = v_contextDependent_2485_;
goto v___jp_2499_;
}
v___jp_2499_:
{
lean_object* v___x_2502_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 1, v___x_2497_);
lean_ctor_set(v___x_2490_, 0, v_a_2493_);
v___x_2502_ = v___x_2490_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2493_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*2, v___x_2498_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*2 + 1, v___y_2500_);
v_r_2412_ = v___x_2502_;
goto v___jp_2411_;
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_del_object(v___x_2490_);
lean_dec_ref(v_proof_2487_);
lean_dec_ref(v_e_x27_2486_);
lean_dec_ref(v_proof_2484_);
lean_dec_ref(v_e_x27_2483_);
lean_del_object(v___x_2409_);
lean_dec(v_snd_2407_);
lean_del_object(v___x_2404_);
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_fn_2397_);
v_a_2504_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2492_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2492_);
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
v___jp_2422_:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2423_);
v_r_2412_ = v___x_2424_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_del_object(v___x_2409_);
lean_dec(v_snd_2407_);
lean_dec(v_fst_2406_);
lean_del_object(v___x_2404_);
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_fn_2397_);
v_a_2513_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2420_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2420_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_Expr_bindingBody_x21(v_snd_2407_);
lean_dec(v_snd_2407_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2413_);
lean_ctor_set(v___x_2409_, 0, v_r_2412_);
v___x_2415_ = v___x_2409_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_r_2412_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2415_);
v___x_2417_ = v___x_2404_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_fn_2397_);
return v___x_2401_;
}
}
case 6:
{
lean_object* v___x_2523_; 
lean_inc(v_a_2395_);
lean_inc_ref(v_a_2394_);
lean_inc(v_a_2393_);
lean_inc_ref(v_a_2392_);
lean_inc(v_a_2391_);
lean_inc_ref(v_a_2390_);
lean_inc(v_a_2389_);
lean_inc_ref(v_a_2388_);
lean_inc(v_a_2387_);
v___x_2523_ = lean_apply_11(v_simpBody_2384_, v_e_2385_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, lean_box(0));
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2524_);
lean_ctor_set(v___x_2528_, 1, v_fType_2381_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_fType_2381_);
v_a_2533_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2523_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2523_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
default: 
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v_e_2385_);
lean_dec_ref(v_simpBody_2384_);
lean_dec_ref(v_fType_2381_);
v___x_2541_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2542_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2541_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2543_, lean_object* v_fnUnivs_2544_, lean_object* v_argUnivs_2545_, lean_object* v_simpBody_2546_, lean_object* v_e_2547_, lean_object* v_i_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2543_, v_fnUnivs_2544_, v_argUnivs_2545_, v_simpBody_2546_, v_e_2547_, v_i_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec(v_i_2548_);
lean_dec_ref(v_argUnivs_2545_);
lean_dec_ref(v_fnUnivs_2544_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2560_, lean_object* v_fType_2561_, lean_object* v_fnUnivs_2562_, lean_object* v_argUnivs_2563_, lean_object* v_simpBody_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_numArgs_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_numArgs_2575_ = lean_array_get_size(v_argUnivs_2563_);
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = lean_nat_sub(v_numArgs_2575_, v___x_2576_);
v___x_2578_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2561_, v_fnUnivs_2562_, v_argUnivs_2563_, v_simpBody_2564_, v_e_2560_, v___x_2577_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v___x_2577_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2587_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v_fst_2583_; lean_object* v___x_2585_; 
v_fst_2583_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_fst_2583_);
lean_dec(v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v_fst_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_fst_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2578_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2578_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2596_, lean_object* v_fType_2597_, lean_object* v_fnUnivs_2598_, lean_object* v_argUnivs_2599_, lean_object* v_simpBody_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2596_, v_fType_2597_, v_fnUnivs_2598_, v_argUnivs_2599_, v_simpBody_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_argUnivs_2599_);
lean_dec_ref(v_fnUnivs_2598_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2616_, lean_object* v_simpBody_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; 
lean_inc_ref(v_e_2616_);
v___x_2628_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2616_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v_00_u03b1_2630_; lean_object* v_u_2631_; lean_object* v_e_2632_; lean_object* v_h_2633_; lean_object* v_varDeps_2634_; lean_object* v_fType_2635_; lean_object* v___x_2636_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
v_00_u03b1_2630_ = lean_ctor_get(v_a_2629_, 0);
lean_inc_ref(v_00_u03b1_2630_);
v_u_2631_ = lean_ctor_get(v_a_2629_, 1);
lean_inc(v_u_2631_);
v_e_2632_ = lean_ctor_get(v_a_2629_, 2);
lean_inc_ref(v_e_2632_);
v_h_2633_ = lean_ctor_get(v_a_2629_, 3);
lean_inc_ref(v_h_2633_);
v_varDeps_2634_ = lean_ctor_get(v_a_2629_, 4);
lean_inc_ref(v_varDeps_2634_);
v_fType_2635_ = lean_ctor_get(v_a_2629_, 5);
lean_inc_ref_n(v_fType_2635_, 2);
lean_dec(v_a_2629_);
v___x_2636_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2635_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_argUnivs_2638_; lean_object* v_fnUnivs_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2707_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v_argUnivs_2638_ = lean_ctor_get(v_a_2637_, 0);
v_fnUnivs_2639_ = lean_ctor_get(v_a_2637_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2641_ = v_a_2637_;
v_isShared_2642_ = v_isSharedCheck_2707_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_fnUnivs_2639_);
lean_inc(v_argUnivs_2638_);
lean_dec(v_a_2637_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2707_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; 
lean_inc_ref(v_e_2632_);
v___x_2643_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2632_, v_fType_2635_, v_fnUnivs_2639_, v_argUnivs_2638_, v_simpBody_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
lean_dec_ref(v_argUnivs_2638_);
lean_dec_ref(v_fnUnivs_2639_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2698_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2698_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2698_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
if (lean_obj_tag(v_a_2644_) == 0)
{
uint8_t v_contextDependent_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_del_object(v___x_2641_);
lean_dec_ref(v_varDeps_2634_);
lean_dec_ref(v_h_2633_);
lean_dec_ref(v_e_2632_);
lean_dec_ref(v_e_2616_);
v_contextDependent_2648_ = lean_ctor_get_uint8(v_a_2644_, 1);
lean_dec_ref(v_a_2644_);
v___x_2649_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2648_);
v___x_2650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v_00_u03b1_2630_);
lean_ctor_set(v___x_2650_, 2, v_u_2631_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2650_);
v___x_2652_ = v___x_2646_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v_e_x27_2654_; lean_object* v_proof_2655_; uint8_t v_contextDependent_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2646_);
v_e_x27_2654_ = lean_ctor_get(v_a_2644_, 0);
v_proof_2655_ = lean_ctor_get(v_a_2644_, 1);
v_contextDependent_2656_ = lean_ctor_get_uint8(v_a_2644_, sizeof(void*)*2 + 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_a_2644_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2658_ = v_a_2644_;
v_isShared_2659_ = v_isSharedCheck_2697_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_proof_2655_);
lean_inc(v_e_x27_2654_);
lean_dec(v_a_2644_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2697_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2661_ = lean_box(0);
lean_inc(v_u_2631_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 1, v___x_2661_);
lean_ctor_set(v___x_2641_, 0, v_u_2631_);
v___x_2663_ = v___x_2641_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_u_2631_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_inc_ref(v___x_2663_);
v___x_2664_ = l_Lean_mkConst(v___x_2660_, v___x_2663_);
lean_inc_ref_n(v_e_x27_2654_, 2);
lean_inc_ref(v_e_2616_);
lean_inc_ref(v_00_u03b1_2630_);
lean_inc_ref(v___x_2664_);
v___x_2665_ = l_Lean_mkApp6(v___x_2664_, v_00_u03b1_2630_, v_e_2616_, v_e_2632_, v_e_x27_2654_, v_h_2633_, v_proof_2655_);
v___x_2666_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2654_, v_varDeps_2634_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2687_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2687_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2687_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; lean_object* v___x_2681_; 
v___x_2671_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2663_);
v___x_2672_ = l_Lean_mkConst(v___x_2671_, v___x_2663_);
lean_inc_n(v_a_2667_, 2);
lean_inc_ref_n(v_e_x27_2654_, 2);
lean_inc_ref_n(v_00_u03b1_2630_, 3);
v___x_2673_ = l_Lean_mkApp3(v___x_2672_, v_00_u03b1_2630_, v_e_x27_2654_, v_a_2667_);
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2675_ = l_Lean_mkConst(v___x_2674_, v___x_2663_);
v___x_2676_ = l_Lean_mkAppB(v___x_2675_, v_00_u03b1_2630_, v_e_x27_2654_);
v___x_2677_ = l_Lean_Meta_mkExpectedPropHint(v___x_2676_, v___x_2673_);
v___x_2678_ = l_Lean_mkApp6(v___x_2664_, v_00_u03b1_2630_, v_e_2616_, v_e_x27_2654_, v_a_2667_, v___x_2665_, v___x_2677_);
v___x_2679_ = 0;
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2678_);
lean_ctor_set(v___x_2658_, 0, v_a_2667_);
v___x_2681_ = v___x_2658_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2667_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2678_);
lean_ctor_set_uint8(v_reuseFailAlloc_2686_, sizeof(void*)*2 + 1, v_contextDependent_2656_);
v___x_2681_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*2, v___x_2679_);
v___x_2682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v_00_u03b1_2630_);
lean_ctor_set(v___x_2682_, 2, v_u_2631_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2682_);
v___x_2684_ = v___x_2669_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v___x_2665_);
lean_dec_ref(v___x_2664_);
lean_dec_ref(v___x_2663_);
lean_del_object(v___x_2658_);
lean_dec_ref(v_e_x27_2654_);
lean_dec(v_u_2631_);
lean_dec_ref(v_00_u03b1_2630_);
lean_dec_ref(v_e_2616_);
v_a_2688_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2666_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2666_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
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
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_del_object(v___x_2641_);
lean_dec_ref(v_varDeps_2634_);
lean_dec_ref(v_h_2633_);
lean_dec_ref(v_e_2632_);
lean_dec(v_u_2631_);
lean_dec_ref(v_00_u03b1_2630_);
lean_dec_ref(v_e_2616_);
v_a_2699_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2643_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2643_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_fType_2635_);
lean_dec_ref(v_varDeps_2634_);
lean_dec_ref(v_h_2633_);
lean_dec_ref(v_e_2632_);
lean_dec(v_u_2631_);
lean_dec_ref(v_00_u03b1_2630_);
lean_dec_ref(v_simpBody_2617_);
lean_dec_ref(v_e_2616_);
v_a_2708_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2636_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2636_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v_simpBody_2617_);
lean_dec_ref(v_e_2616_);
v_a_2716_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2628_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2628_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2724_, lean_object* v_simpBody_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2724_, v_simpBody_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2737_, lean_object* v_simpBody_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2737_, v_simpBody_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2758_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2758_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2758_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_result_2754_; lean_object* v___x_2756_; 
v_result_2754_ = lean_ctor_get(v_a_2750_, 0);
lean_inc_ref(v_result_2754_);
lean_dec(v_a_2750_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_result_2754_);
v___x_2756_ = v___x_2752_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_result_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
v_a_2759_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2749_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2749_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2767_, lean_object* v_simpBody_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2767_, v_simpBody_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2780_, lean_object* v_simpBody_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___x_2792_; 
lean_inc_ref(v_e_u2081_2780_);
v___x_2792_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2780_, v_simpBody_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v_result_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref(v___x_2792_);
v_result_2794_ = lean_ctor_get(v_a_2793_, 0);
lean_inc_ref(v_result_2794_);
if (lean_obj_tag(v_result_2794_) == 0)
{
lean_object* v_00_u03b1_2795_; lean_object* v_u_2796_; uint8_t v_contextDependent_2797_; lean_object* v___x_2798_; 
v_00_u03b1_2795_ = lean_ctor_get(v_a_2793_, 1);
lean_inc_ref(v_00_u03b1_2795_);
v_u_2796_ = lean_ctor_get(v_a_2793_, 2);
lean_inc(v_u_2796_);
lean_dec(v_a_2793_);
v_contextDependent_2797_ = lean_ctor_get_uint8(v_result_2794_, 1);
lean_dec_ref(v_result_2794_);
lean_inc_ref(v_e_u2081_2780_);
v___x_2798_ = l_Lean_Meta_zetaUnused(v_e_u2081_2780_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2817_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2817_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2817_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
uint8_t v___x_2803_; 
v___x_2803_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_u2081_2780_, v_a_2799_);
lean_dec_ref(v_e_u2081_2780_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2804_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2805_ = lean_box(0);
v___x_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_u_2796_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = l_Lean_mkConst(v___x_2804_, v___x_2806_);
lean_inc(v_a_2799_);
v___x_2808_ = l_Lean_mkAppB(v___x_2807_, v_00_u03b1_2795_, v_a_2799_);
v___x_2809_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2809_, 0, v_a_2799_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*2, v___x_2803_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*2 + 1, v_contextDependent_2797_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2809_);
v___x_2811_ = v___x_2801_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2815_; 
lean_dec(v_a_2799_);
lean_dec(v_u_2796_);
lean_dec_ref(v_00_u03b1_2795_);
v___x_2813_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2797_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2813_);
v___x_2815_ = v___x_2801_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_u_2796_);
lean_dec_ref(v_00_u03b1_2795_);
lean_dec_ref(v_e_u2081_2780_);
v_a_2818_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2798_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2798_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_00_u03b1_2826_; lean_object* v_u_2827_; lean_object* v_e_x27_2828_; lean_object* v_proof_2829_; uint8_t v_contextDependent_2830_; lean_object* v___x_2831_; 
v_00_u03b1_2826_ = lean_ctor_get(v_a_2793_, 1);
lean_inc_ref(v_00_u03b1_2826_);
v_u_2827_ = lean_ctor_get(v_a_2793_, 2);
lean_inc(v_u_2827_);
lean_dec(v_a_2793_);
v_e_x27_2828_ = lean_ctor_get(v_result_2794_, 0);
v_proof_2829_ = lean_ctor_get(v_result_2794_, 1);
v_contextDependent_2830_ = lean_ctor_get_uint8(v_result_2794_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_2828_);
v___x_2831_ = l_Lean_Meta_zetaUnused(v_e_x27_2828_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2860_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2860_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2860_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
uint8_t v___x_2836_; 
v___x_2836_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_2828_, v_a_2832_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2854_; 
lean_inc_ref(v_proof_2829_);
lean_inc_ref(v_e_x27_2828_);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_result_2794_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; lean_object* v_unused_2856_; 
v_unused_2855_ = lean_ctor_get(v_result_2794_, 1);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_result_2794_, 0);
lean_dec(v_unused_2856_);
v___x_2838_ = v_result_2794_;
v_isShared_2839_ = v_isSharedCheck_2854_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v_result_2794_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2854_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_u_2827_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
lean_inc_ref(v___x_2842_);
v___x_2843_ = l_Lean_mkConst(v___x_2840_, v___x_2842_);
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2845_ = l_Lean_mkConst(v___x_2844_, v___x_2842_);
lean_inc_n(v_a_2832_, 2);
lean_inc_ref(v_00_u03b1_2826_);
v___x_2846_ = l_Lean_mkAppB(v___x_2845_, v_00_u03b1_2826_, v_a_2832_);
v___x_2847_ = l_Lean_mkApp6(v___x_2843_, v_00_u03b1_2826_, v_e_u2081_2780_, v_e_x27_2828_, v_a_2832_, v_proof_2829_, v___x_2846_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2847_);
lean_ctor_set(v___x_2838_, 0, v_a_2832_);
v___x_2849_ = v___x_2838_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2832_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*2 + 1, v_contextDependent_2830_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2851_; 
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*2, v___x_2836_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2849_);
v___x_2851_ = v___x_2834_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v_a_2832_);
lean_dec(v_u_2827_);
lean_dec_ref(v_00_u03b1_2826_);
lean_dec_ref(v_e_u2081_2780_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_result_2794_);
v___x_2858_ = v___x_2834_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_result_2794_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_u_2827_);
lean_dec_ref(v_00_u03b1_2826_);
lean_dec_ref(v_result_2794_);
lean_dec_ref(v_e_u2081_2780_);
v_a_2861_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2831_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2831_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec_ref(v_e_u2081_2780_);
v_a_2869_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2792_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2792_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_2877_, lean_object* v_simpBody_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_2877_, v_simpBody_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_2890_, lean_object* v_e_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = l_Lean_Expr_letNondep_x21(v_e_2891_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec_ref(v_e_2891_);
lean_dec_ref(v_simpBody_2890_);
v___x_2903_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2903_, 0, v___x_2902_);
lean_ctor_set_uint8(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
else
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_2891_, v_simpBody_2890_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
return v___x_2905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_2906_, lean_object* v_e_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_2906_, v_e_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_2932_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_2931_, v_e_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
return v_res_2944_;
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
