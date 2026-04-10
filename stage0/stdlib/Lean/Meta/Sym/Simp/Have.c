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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object* v_fvarIdToPos_88_, lean_object* v_as_89_, lean_object* v_lo_90_, lean_object* v_hi_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_lt(v_lo_90_, v_hi_91_);
if (v___x_92_ == 0)
{
lean_dec(v_lo_90_);
lean_dec(v_fvarIdToPos_88_);
return v_as_89_;
}
else
{
lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; uint8_t v___x_97_; 
lean_inc(v_fvarIdToPos_88_);
v___f_93_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_93_, 0, v_fvarIdToPos_88_);
lean_inc(v_lo_90_);
v___x_94_ = l_Array_qpartition___redArg(v_as_89_, v___f_93_, v_lo_90_, v_hi_91_);
v_fst_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_fst_95_);
v_snd_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_snd_96_);
lean_dec_ref(v___x_94_);
v___x_97_ = lean_nat_dec_le(v_hi_91_, v_fst_95_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
lean_inc(v_fvarIdToPos_88_);
v___x_98_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_88_, v_snd_96_, v_lo_90_, v_fst_95_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_fst_95_, v___x_99_);
lean_dec(v_fst_95_);
v_as_89_ = v___x_98_;
v_lo_90_ = v___x_100_;
goto _start;
}
else
{
lean_dec(v_fst_95_);
lean_dec(v_lo_90_);
lean_dec(v_fvarIdToPos_88_);
return v_snd_96_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object* v_fvarIdToPos_102_, lean_object* v_as_103_, lean_object* v_lo_104_, lean_object* v_hi_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_102_, v_as_103_, v_lo_104_, v_hi_105_);
lean_dec(v_hi_105_);
return v_res_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_unsigned_to_nat(16u);
v___x_109_ = lean_mk_array(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_116_ = lean_box(1);
v___x_117_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_115_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_119_, lean_object* v_fvarIdToPos_120_){
_start:
{
lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___x_129_; lean_object* v___y_131_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_s_139_; lean_object* v_fvarIds_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_138_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3);
v_s_139_ = l_Lean_collectFVars(v___x_138_, v_e_119_);
v_fvarIds_140_ = lean_ctor_get(v_s_139_, 2);
lean_inc_ref(v_fvarIds_140_);
lean_dec_ref(v_s_139_);
v___x_141_ = lean_array_get_size(v_fvarIds_140_);
v___x_142_ = lean_nat_dec_lt(v___x_129_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec_ref(v_fvarIds_140_);
v___y_131_ = v___x_137_;
goto v___jp_130_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_le(v___x_141_, v___x_141_);
if (v___x_143_ == 0)
{
if (v___x_142_ == 0)
{
lean_dec_ref(v_fvarIds_140_);
v___y_131_ = v___x_137_;
goto v___jp_130_;
}
else
{
size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; 
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_141_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_120_, v_fvarIds_140_, v___x_144_, v___x_145_, v___x_137_);
lean_dec_ref(v_fvarIds_140_);
v___y_131_ = v___x_146_;
goto v___jp_130_;
}
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_141_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_120_, v_fvarIds_140_, v___x_147_, v___x_148_, v___x_137_);
lean_dec_ref(v_fvarIds_140_);
v___y_131_ = v___x_149_;
goto v___jp_130_;
}
}
v___jp_121_:
{
uint8_t v___x_126_; 
lean_dec(v___y_123_);
v___x_126_ = lean_nat_dec_le(v___y_125_, v___y_124_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___y_124_);
lean_inc(v___y_125_);
v___x_127_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_120_, v___y_122_, v___y_125_, v___y_125_);
lean_dec(v___y_125_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_120_, v___y_122_, v___y_125_, v___y_124_);
lean_dec(v___y_124_);
return v___x_128_;
}
}
v___jp_130_:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_array_get_size(v___y_131_);
v___x_133_ = lean_nat_dec_eq(v___x_132_, v___x_129_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_sub(v___x_132_, v___x_134_);
v___x_136_ = lean_nat_dec_le(v___x_129_, v___x_135_);
if (v___x_136_ == 0)
{
lean_inc(v___x_135_);
v___y_122_ = v___y_131_;
v___y_123_ = v___x_132_;
v___y_124_ = v___x_135_;
v___y_125_ = v___x_135_;
goto v___jp_121_;
}
else
{
v___y_122_ = v___y_131_;
v___y_123_ = v___x_132_;
v___y_124_ = v___x_135_;
v___y_125_ = v___x_129_;
goto v___jp_121_;
}
}
else
{
lean_dec(v_fvarIdToPos_120_);
return v___y_131_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_150_, lean_object* v_k_151_, lean_object* v_t_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_151_, v_t_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_154_, lean_object* v_k_155_, lean_object* v_t_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_154_, v_k_155_, v_t_156_);
lean_dec(v_t_156_);
lean_dec(v_k_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_159_, lean_object* v_n_160_, lean_object* v_as_161_, lean_object* v_lo_162_, lean_object* v_hi_163_, lean_object* v_w_164_, lean_object* v_hlo_165_, lean_object* v_hhi_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_159_, v_as_161_, v_lo_162_, v_hi_163_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_168_, lean_object* v_n_169_, lean_object* v_as_170_, lean_object* v_lo_171_, lean_object* v_hi_172_, lean_object* v_w_173_, lean_object* v_hlo_174_, lean_object* v_hhi_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_168_, v_n_169_, v_as_170_, v_lo_171_, v_hi_172_, v_w_173_, v_hlo_174_, v_hhi_175_);
lean_dec(v_hi_172_);
lean_dec(v_n_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_177_, uint8_t v_bi_178_, lean_object* v_t_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___y_189_; lean_object* v___x_192_; uint8_t v_debug_193_; 
v___x_192_ = lean_st_ref_get(v___y_182_);
v_debug_193_ = lean_ctor_get_uint8(v___x_192_, sizeof(void*)*10);
lean_dec(v___x_192_);
if (v_debug_193_ == 0)
{
v___y_189_ = v___y_182_;
goto v___jp_188_;
}
else
{
lean_object* v___x_194_; 
lean_inc_ref(v_t_179_);
v___x_194_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_179_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_195_; 
lean_dec_ref(v___x_194_);
lean_inc_ref(v_b_180_);
v___x_195_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_dec_ref(v___x_195_);
v___y_189_ = v___y_182_;
goto v___jp_188_;
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v_b_180_);
lean_dec_ref(v_t_179_);
lean_dec(v_x_177_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_b_180_);
lean_dec_ref(v_t_179_);
lean_dec(v_x_177_);
v_a_204_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_194_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = l_Lean_Expr_forallE___override(v_x_177_, v_t_179_, v_b_180_, v_bi_178_);
v___x_191_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_190_, v___y_189_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_212_, lean_object* v_bi_213_, lean_object* v_t_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_bi_boxed_223_; lean_object* v_res_224_; 
v_bi_boxed_223_ = lean_unbox(v_bi_213_);
v_res_224_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_212_, v_bi_boxed_223_, v_t_214_, v_b_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_228_, lean_object* v_i_229_, lean_object* v_00_u03b2_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_zero_238_; uint8_t v_isZero_239_; 
v_zero_238_ = lean_unsigned_to_nat(0u);
v_isZero_239_ = lean_nat_dec_eq(v_i_229_, v_zero_238_);
if (v_isZero_239_ == 1)
{
lean_object* v___x_240_; 
lean_dec(v_i_229_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v_00_u03b2_230_);
return v___x_240_;
}
else
{
lean_object* v_one_241_; lean_object* v_n_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_one_241_ = lean_unsigned_to_nat(1u);
v_n_242_ = lean_nat_sub(v_i_229_, v_one_241_);
lean_dec(v_i_229_);
v___x_243_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_244_ = 0;
v___x_245_ = lean_array_fget_borrowed(v_00_u03b1s_228_, v_n_242_);
lean_inc(v___x_245_);
v___x_246_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_243_, v___x_244_, v___x_245_, v_00_u03b2_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref(v___x_246_);
v_i_229_ = v_n_242_;
v_00_u03b2_230_ = v_a_247_;
goto _start;
}
else
{
lean_dec(v_n_242_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_249_, lean_object* v_i_250_, lean_object* v_00_u03b2_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_249_, v_i_250_, v_00_u03b2_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_00_u03b1s_249_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_260_, lean_object* v_i_261_, lean_object* v_00_u03b2_262_, lean_object* v_h_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_260_, v_i_261_, v_00_u03b2_262_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_272_, lean_object* v_i_273_, lean_object* v_00_u03b2_274_, lean_object* v_h_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_272_, v_i_273_, v_00_u03b2_274_, v_h_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec_ref(v_00_u03b1s_272_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_284_, lean_object* v_00_u03b2_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_array_get_size(v_00_u03b1s_284_);
v___x_294_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_284_, v___x_293_, v_00_u03b2_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_295_, lean_object* v_00_u03b2_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_295_, v_00_u03b2_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec_ref(v_00_u03b1s_295_);
return v_res_304_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object* v_msg_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_6003__overap_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0);
v___x_6003__overap_315_ = lean_panic_fn_borrowed(v___x_314_, v_msg_306_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
v___x_316_ = lean_apply_7(v___x_6003__overap_315_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_326_, lean_object* v_subst_327_, size_t v_sz_328_, size_t v_i_329_, lean_object* v_bs_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_331_ == 0)
{
return v_bs_330_;
}
else
{
lean_object* v_v_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v_v_332_ = lean_array_uget(v_bs_330_, v_i_329_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_330_, v_i_329_, v___x_333_);
v___x_335_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_326_, v_v_332_);
lean_dec(v_v_332_);
v___x_336_ = l_Lean_instInhabitedExpr;
v___x_337_ = lean_array_get_borrowed(v___x_336_, v_subst_327_, v___x_335_);
lean_dec(v___x_335_);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_add(v_i_329_, v___x_338_);
lean_inc(v___x_337_);
v___x_340_ = lean_array_uset(v_bs_x27_334_, v_i_329_, v___x_337_);
v_i_329_ = v___x_339_;
v_bs_330_ = v___x_340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_342_, lean_object* v_subst_343_, lean_object* v_sz_344_, lean_object* v_i_345_, lean_object* v_bs_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v_i_boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_344_);
lean_dec(v_sz_344_);
v_i_boxed_348_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_342_, v_subst_343_, v_sz_boxed_347_, v_i_boxed_348_, v_bs_346_);
lean_dec_ref(v_subst_343_);
lean_dec(v_fvarIdToPos_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_350_, size_t v_i_351_, lean_object* v_bs_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_lt(v_i_351_, v_sz_350_);
if (v___x_353_ == 0)
{
return v_bs_352_;
}
else
{
lean_object* v_v_354_; lean_object* v___x_355_; lean_object* v_bs_x27_356_; lean_object* v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; 
v_v_354_ = lean_array_uget(v_bs_352_, v_i_351_);
v___x_355_ = lean_unsigned_to_nat(0u);
v_bs_x27_356_ = lean_array_uset(v_bs_352_, v_i_351_, v___x_355_);
v___x_357_ = l_Lean_mkFVar(v_v_354_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_351_, v___x_358_);
v___x_360_ = lean_array_uset(v_bs_x27_356_, v_i_351_, v___x_357_);
v_i_351_ = v___x_359_;
v_bs_352_ = v___x_360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_362_, lean_object* v_i_363_, lean_object* v_bs_364_){
_start:
{
size_t v_sz_boxed_365_; size_t v_i_boxed_366_; lean_object* v_res_367_; 
v_sz_boxed_365_ = lean_unbox_usize(v_sz_362_);
lean_dec(v_sz_362_);
v_i_boxed_366_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_res_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_365_, v_i_boxed_366_, v_bs_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_370_);
lean_inc_ref(v___y_369_);
v___x_377_ = lean_apply_8(v_k_368_, v_b_371_, v___y_369_, v___y_370_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, lean_box(0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_378_, v___y_379_, v___y_380_, v_b_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_388_, uint8_t v_bi_389_, lean_object* v_type_390_, lean_object* v_k_391_, uint8_t v_kind_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___f_400_; lean_object* v___x_401_; 
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
v___f_400_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_400_, 0, v_k_391_);
lean_closure_set(v___f_400_, 1, v___y_393_);
lean_closure_set(v___f_400_, 2, v___y_394_);
v___x_401_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_388_, v_bi_389_, v_type_390_, v___f_400_, v_kind_392_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_401_) == 0)
{
return v___x_401_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_410_, lean_object* v_bi_411_, lean_object* v_type_412_, lean_object* v_k_413_, lean_object* v_kind_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v_bi_boxed_422_; uint8_t v_kind_boxed_423_; lean_object* v_res_424_; 
v_bi_boxed_422_ = lean_unbox(v_bi_411_);
v_kind_boxed_423_ = lean_unbox(v_kind_414_);
v_res_424_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_410_, v_bi_boxed_422_, v_type_412_, v_k_413_, v_kind_boxed_423_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_425_, lean_object* v_type_426_, lean_object* v_k_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = 0;
v___x_436_ = 0;
v___x_437_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_425_, v___x_435_, v_type_426_, v_k_427_, v___x_436_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_438_, lean_object* v_type_439_, lean_object* v_k_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_438_, v_type_439_, v_k_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_449_, lean_object* v_k_450_, lean_object* v_fallback_451_){
_start:
{
if (lean_obj_tag(v_t_449_) == 0)
{
lean_object* v_k_452_; lean_object* v_v_453_; lean_object* v_l_454_; lean_object* v_r_455_; uint8_t v___x_456_; 
v_k_452_ = lean_ctor_get(v_t_449_, 1);
v_v_453_ = lean_ctor_get(v_t_449_, 2);
v_l_454_ = lean_ctor_get(v_t_449_, 3);
v_r_455_ = lean_ctor_get(v_t_449_, 4);
v___x_456_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_450_, v_k_452_);
switch(v___x_456_)
{
case 0:
{
v_t_449_ = v_l_454_;
goto _start;
}
case 1:
{
lean_inc(v_v_453_);
return v_v_453_;
}
default: 
{
v_t_449_ = v_r_455_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_451_);
return v_fallback_451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_459_, lean_object* v_k_460_, lean_object* v_fallback_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_459_, v_k_460_, v_fallback_461_);
lean_dec(v_fallback_461_);
lean_dec(v_k_460_);
lean_dec(v_t_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_463_, size_t v_sz_464_, size_t v_i_465_, lean_object* v_bs_466_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_lt(v_i_465_, v_sz_464_);
if (v___x_467_ == 0)
{
return v_bs_466_;
}
else
{
lean_object* v_v_468_; lean_object* v___x_469_; lean_object* v_bs_x27_470_; lean_object* v___x_471_; size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v_v_468_ = lean_array_uget(v_bs_466_, v_i_465_);
v___x_469_ = lean_unsigned_to_nat(0u);
v_bs_x27_470_ = lean_array_uset(v_bs_466_, v_i_465_, v___x_469_);
v___x_471_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_463_, v_v_468_, v___x_469_);
lean_dec(v_v_468_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_465_, v___x_472_);
v___x_474_ = lean_array_uset(v_bs_x27_470_, v_i_465_, v___x_471_);
v_i_465_ = v___x_473_;
v_bs_466_ = v___x_474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_476_, lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_bs_479_){
_start:
{
size_t v_sz_boxed_480_; size_t v_i_boxed_481_; lean_object* v_res_482_; 
v_sz_boxed_480_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_481_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_476_, v_sz_boxed_480_, v_i_boxed_481_, v_bs_479_);
lean_dec(v_fvarIdToPos_476_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_492_ = _args[0];
lean_object* v_subst_493_ = _args[1];
lean_object* v_sz_494_ = _args[2];
lean_object* v___x_495_ = _args[3];
lean_object* v_fvarIds_496_ = _args[4];
lean_object* v_x_497_ = _args[5];
lean_object* v_xs_498_ = _args[6];
lean_object* v_xs_x27_499_ = _args[7];
lean_object* v_args_500_ = _args[8];
lean_object* v_a_501_ = _args[9];
lean_object* v_types_502_ = _args[10];
lean_object* v_a_503_ = _args[11];
lean_object* v_varDeps_504_ = _args[12];
lean_object* v_varPos_505_ = _args[13];
lean_object* v_haveExpr_506_ = _args[14];
lean_object* v_body_507_ = _args[15];
lean_object* v_x_x27_508_ = _args[16];
lean_object* v___y_509_ = _args[17];
lean_object* v___y_510_ = _args[18];
lean_object* v___y_511_ = _args[19];
lean_object* v___y_512_ = _args[20];
lean_object* v___y_513_ = _args[21];
lean_object* v___y_514_ = _args[22];
lean_object* v___y_515_ = _args[23];
_start:
{
size_t v_sz_boxed_516_; size_t v___x_7250__boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v___x_7250__boxed_517_ = lean_unbox_usize(v___x_495_);
lean_dec(v___x_495_);
v_res_518_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_492_, v_subst_493_, v_sz_boxed_516_, v___x_7250__boxed_517_, v_fvarIds_496_, v_x_497_, v_xs_498_, v_xs_x27_499_, v_args_500_, v_a_501_, v_types_502_, v_a_503_, v_varDeps_504_, v_varPos_505_, v_haveExpr_506_, v_body_507_, v_x_x27_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_value_519_, lean_object* v_xs_520_, lean_object* v_fvarIdToPos_521_, uint8_t v___x_522_, uint8_t v_nondep_523_, lean_object* v_type_524_, lean_object* v_subst_525_, lean_object* v_xs_x27_526_, lean_object* v_args_527_, lean_object* v_types_528_, lean_object* v_varDeps_529_, lean_object* v_haveExpr_530_, lean_object* v_body_531_, lean_object* v_declName_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_v_541_; lean_object* v_fvarIds_542_; size_t v_sz_543_; size_t v___x_544_; lean_object* v_varPos_545_; lean_object* v_ys_546_; uint8_t v___x_547_; lean_object* v___x_548_; 
v_v_541_ = lean_expr_instantiate_rev(v_value_519_, v_xs_520_);
lean_inc(v_fvarIdToPos_521_);
lean_inc_ref(v_v_541_);
v_fvarIds_542_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_541_, v_fvarIdToPos_521_);
v_sz_543_ = lean_array_size(v_fvarIds_542_);
v___x_544_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_542_, 2);
v_varPos_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_521_, v_sz_543_, v___x_544_, v_fvarIds_542_);
v_ys_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_543_, v___x_544_, v_fvarIds_542_);
v___x_547_ = 1;
v___x_548_ = l_Lean_Meta_mkLambdaFVars(v_ys_546_, v_v_541_, v___x_522_, v_nondep_523_, v___x_522_, v_nondep_523_, v___x_547_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_Lean_Meta_mkForallFVars(v_ys_546_, v_type_524_, v___x_522_, v_nondep_523_, v_nondep_523_, v___x_547_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec_ref(v_ys_546_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_551_, v___y_535_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v___x_557_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_n(v_a_553_, 2);
lean_dec_ref(v___x_552_);
v___x_554_ = lean_box_usize(v_sz_543_);
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_556_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_556_, 0, v_fvarIdToPos_521_);
lean_closure_set(v___f_556_, 1, v_subst_525_);
lean_closure_set(v___f_556_, 2, v___x_554_);
lean_closure_set(v___f_556_, 3, v___x_555_);
lean_closure_set(v___f_556_, 4, v_fvarIds_542_);
lean_closure_set(v___f_556_, 5, v_x_533_);
lean_closure_set(v___f_556_, 6, v_xs_520_);
lean_closure_set(v___f_556_, 7, v_xs_x27_526_);
lean_closure_set(v___f_556_, 8, v_args_527_);
lean_closure_set(v___f_556_, 9, v_a_549_);
lean_closure_set(v___f_556_, 10, v_types_528_);
lean_closure_set(v___f_556_, 11, v_a_553_);
lean_closure_set(v___f_556_, 12, v_varDeps_529_);
lean_closure_set(v___f_556_, 13, v_varPos_545_);
lean_closure_set(v___f_556_, 14, v_haveExpr_530_);
lean_closure_set(v___f_556_, 15, v_body_531_);
v___x_557_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_532_, v_a_553_, v___f_556_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_557_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_a_549_);
lean_dec_ref(v_varPos_545_);
lean_dec_ref(v_fvarIds_542_);
lean_dec_ref(v_x_533_);
lean_dec(v_declName_532_);
lean_dec_ref(v_body_531_);
lean_dec_ref(v_haveExpr_530_);
lean_dec_ref(v_varDeps_529_);
lean_dec_ref(v_types_528_);
lean_dec_ref(v_args_527_);
lean_dec_ref(v_xs_x27_526_);
lean_dec_ref(v_subst_525_);
lean_dec(v_fvarIdToPos_521_);
lean_dec_ref(v_xs_520_);
v_a_558_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_552_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_552_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_a_549_);
lean_dec_ref(v_varPos_545_);
lean_dec_ref(v_fvarIds_542_);
lean_dec_ref(v_x_533_);
lean_dec(v_declName_532_);
lean_dec_ref(v_body_531_);
lean_dec_ref(v_haveExpr_530_);
lean_dec_ref(v_varDeps_529_);
lean_dec_ref(v_types_528_);
lean_dec_ref(v_args_527_);
lean_dec_ref(v_xs_x27_526_);
lean_dec_ref(v_subst_525_);
lean_dec(v_fvarIdToPos_521_);
lean_dec_ref(v_xs_520_);
v_a_566_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_550_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_550_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_ys_546_);
lean_dec_ref(v_varPos_545_);
lean_dec_ref(v_fvarIds_542_);
lean_dec_ref(v_x_533_);
lean_dec(v_declName_532_);
lean_dec_ref(v_body_531_);
lean_dec_ref(v_haveExpr_530_);
lean_dec_ref(v_varDeps_529_);
lean_dec_ref(v_types_528_);
lean_dec_ref(v_args_527_);
lean_dec_ref(v_xs_x27_526_);
lean_dec_ref(v_subst_525_);
lean_dec_ref(v_type_524_);
lean_dec(v_fvarIdToPos_521_);
lean_dec_ref(v_xs_520_);
v_a_574_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_548_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_548_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_value_582_ = _args[0];
lean_object* v_xs_583_ = _args[1];
lean_object* v_fvarIdToPos_584_ = _args[2];
lean_object* v___x_585_ = _args[3];
lean_object* v_nondep_586_ = _args[4];
lean_object* v_type_587_ = _args[5];
lean_object* v_subst_588_ = _args[6];
lean_object* v_xs_x27_589_ = _args[7];
lean_object* v_args_590_ = _args[8];
lean_object* v_types_591_ = _args[9];
lean_object* v_varDeps_592_ = _args[10];
lean_object* v_haveExpr_593_ = _args[11];
lean_object* v_body_594_ = _args[12];
lean_object* v_declName_595_ = _args[13];
lean_object* v_x_596_ = _args[14];
lean_object* v___y_597_ = _args[15];
lean_object* v___y_598_ = _args[16];
lean_object* v___y_599_ = _args[17];
lean_object* v___y_600_ = _args[18];
lean_object* v___y_601_ = _args[19];
lean_object* v___y_602_ = _args[20];
lean_object* v___y_603_ = _args[21];
_start:
{
uint8_t v___x_7278__boxed_604_; uint8_t v_nondep_7279__boxed_605_; lean_object* v_res_606_; 
v___x_7278__boxed_604_ = lean_unbox(v___x_585_);
v_nondep_7279__boxed_605_ = lean_unbox(v_nondep_586_);
v_res_606_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_value_582_, v_xs_583_, v_fvarIdToPos_584_, v___x_7278__boxed_604_, v_nondep_7279__boxed_605_, v_type_587_, v_subst_588_, v_xs_x27_589_, v_args_590_, v_types_591_, v_varDeps_592_, v_haveExpr_593_, v_body_594_, v_declName_595_, v_x_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v_value_582_);
return v_res_606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6));
v___x_611_ = lean_unsigned_to_nat(6u);
v___x_612_ = lean_unsigned_to_nat(168u);
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5));
v___x_614_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_615_ = l_mkPanicMessageWithDecl(v___x_614_, v___x_613_, v___x_612_, v___x_611_, v___x_610_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_616_, lean_object* v_e_617_, lean_object* v_xs_618_, lean_object* v_xs_x27_619_, lean_object* v_args_620_, lean_object* v_subst_621_, lean_object* v_types_622_, lean_object* v_varDeps_623_, lean_object* v_fvarIdToPos_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; 
if (lean_obj_tag(v_e_617_) == 8)
{
uint8_t v_nondep_719_; 
v_nondep_719_ = lean_ctor_get_uint8(v_e_617_, sizeof(void*)*4 + 8);
if (v_nondep_719_ == 1)
{
lean_object* v_declName_720_; lean_object* v_type_721_; lean_object* v_value_722_; lean_object* v_body_723_; uint8_t v___x_724_; 
v_declName_720_ = lean_ctor_get(v_e_617_, 0);
lean_inc(v_declName_720_);
v_type_721_ = lean_ctor_get(v_e_617_, 1);
lean_inc_ref(v_type_721_);
v_value_722_ = lean_ctor_get(v_e_617_, 2);
lean_inc_ref(v_value_722_);
v_body_723_ = lean_ctor_get(v_e_617_, 3);
lean_inc_ref(v_body_723_);
lean_dec_ref(v_e_617_);
v___x_724_ = l_Lean_Expr_hasLooseBVars(v_type_721_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___f_727_; lean_object* v___x_728_; 
v___x_725_ = lean_box(v___x_724_);
v___x_726_ = lean_box(v_nondep_719_);
lean_inc(v_declName_720_);
lean_inc_ref(v_type_721_);
v___f_727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 22, 14);
lean_closure_set(v___f_727_, 0, v_value_722_);
lean_closure_set(v___f_727_, 1, v_xs_618_);
lean_closure_set(v___f_727_, 2, v_fvarIdToPos_624_);
lean_closure_set(v___f_727_, 3, v___x_725_);
lean_closure_set(v___f_727_, 4, v___x_726_);
lean_closure_set(v___f_727_, 5, v_type_721_);
lean_closure_set(v___f_727_, 6, v_subst_621_);
lean_closure_set(v___f_727_, 7, v_xs_x27_619_);
lean_closure_set(v___f_727_, 8, v_args_620_);
lean_closure_set(v___f_727_, 9, v_types_622_);
lean_closure_set(v___f_727_, 10, v_varDeps_623_);
lean_closure_set(v___f_727_, 11, v_haveExpr_616_);
lean_closure_set(v___f_727_, 12, v_body_723_);
lean_closure_set(v___f_727_, 13, v_declName_720_);
v___x_728_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_720_, v_type_721_, v___f_727_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_body_723_);
lean_dec_ref(v_value_722_);
lean_dec_ref(v_type_721_);
lean_dec(v_declName_720_);
lean_dec(v_fvarIdToPos_624_);
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_types_622_);
lean_dec_ref(v_subst_621_);
lean_dec_ref(v_args_620_);
lean_dec_ref(v_xs_x27_619_);
lean_dec_ref(v_xs_618_);
lean_dec_ref(v_haveExpr_616_);
v___x_729_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7);
v___x_730_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v___x_729_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_730_;
}
}
else
{
lean_dec(v_fvarIdToPos_624_);
lean_dec_ref(v_xs_618_);
v___y_633_ = v_a_625_;
v___y_634_ = v_a_626_;
v___y_635_ = v_a_627_;
v___y_636_ = v_a_628_;
v___y_637_ = v_a_629_;
v___y_638_ = v_a_630_;
goto v___jp_632_;
}
}
else
{
lean_dec(v_fvarIdToPos_624_);
lean_dec_ref(v_xs_618_);
v___y_633_ = v_a_625_;
v___y_634_ = v_a_626_;
v___y_635_ = v_a_627_;
v___y_636_ = v_a_628_;
v___y_637_ = v_a_629_;
v___y_638_ = v_a_630_;
goto v___jp_632_;
}
v___jp_632_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_array_get_size(v_subst_621_);
v___x_641_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_617_, v___x_639_, v___x_640_, v_subst_621_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec_ref(v_subst_621_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc_n(v_a_642_, 2);
lean_dec_ref(v___x_641_);
v___x_643_ = l_Lean_Meta_Sym_inferType___redArg(v_a_642_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_n(v_a_644_, 2);
lean_dec_ref(v___x_643_);
v___x_645_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_644_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
lean_inc(v_a_644_);
v___x_647_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_622_, v_a_644_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec_ref(v_types_622_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_619_, v_a_642_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec_ref(v_xs_x27_619_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = l_Lean_mkAppN(v_a_650_, v_args_620_);
lean_dec_ref(v_args_620_);
v___x_652_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_651_, v___y_634_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_670_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_670_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_670_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_670_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_658_ = lean_box(0);
lean_inc(v_a_646_);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v_a_646_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_inc_ref(v___x_659_);
v___x_660_ = l_Lean_mkConst(v___x_657_, v___x_659_);
lean_inc(v_a_653_);
lean_inc_ref(v_haveExpr_616_);
lean_inc_n(v_a_644_, 2);
v___x_661_ = l_Lean_mkApp3(v___x_660_, v_a_644_, v_haveExpr_616_, v_a_653_);
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_663_ = l_Lean_mkConst(v___x_662_, v___x_659_);
v___x_664_ = l_Lean_mkAppB(v___x_663_, v_a_644_, v_haveExpr_616_);
v___x_665_ = l_Lean_Meta_mkExpectedPropHint(v___x_664_, v___x_661_);
v___x_666_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_666_, 0, v_a_644_);
lean_ctor_set(v___x_666_, 1, v_a_646_);
lean_ctor_set(v___x_666_, 2, v_a_653_);
lean_ctor_set(v___x_666_, 3, v___x_665_);
lean_ctor_set(v___x_666_, 4, v_varDeps_623_);
lean_ctor_set(v___x_666_, 5, v_a_648_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_666_);
v___x_668_ = v___x_655_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_a_648_);
lean_dec(v_a_646_);
lean_dec(v_a_644_);
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_haveExpr_616_);
v_a_671_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_652_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_652_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v_a_648_);
lean_dec(v_a_646_);
lean_dec(v_a_644_);
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_args_620_);
lean_dec_ref(v_haveExpr_616_);
v_a_679_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_649_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_649_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v_a_646_);
lean_dec(v_a_644_);
lean_dec(v_a_642_);
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_args_620_);
lean_dec_ref(v_xs_x27_619_);
lean_dec_ref(v_haveExpr_616_);
v_a_687_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_647_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_647_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_a_644_);
lean_dec(v_a_642_);
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_types_622_);
lean_dec_ref(v_args_620_);
lean_dec_ref(v_xs_x27_619_);
lean_dec_ref(v_haveExpr_616_);
v_a_695_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_645_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_645_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_a_642_);
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_types_622_);
lean_dec_ref(v_args_620_);
lean_dec_ref(v_xs_x27_619_);
lean_dec_ref(v_haveExpr_616_);
v_a_703_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_643_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_643_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_varDeps_623_);
lean_dec_ref(v_types_622_);
lean_dec_ref(v_args_620_);
lean_dec_ref(v_xs_x27_619_);
lean_dec_ref(v_haveExpr_616_);
v_a_711_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_641_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_641_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_731_, lean_object* v_subst_732_, size_t v_sz_733_, size_t v___x_734_, lean_object* v_fvarIds_735_, lean_object* v_x_736_, lean_object* v_xs_737_, lean_object* v_xs_x27_738_, lean_object* v_args_739_, lean_object* v_a_740_, lean_object* v_types_741_, lean_object* v_a_742_, lean_object* v_varDeps_743_, lean_object* v_varPos_744_, lean_object* v_haveExpr_745_, lean_object* v_body_746_, lean_object* v_x_x27_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_731_, v_subst_732_, v_sz_733_, v___x_734_, v_fvarIds_735_);
lean_inc_ref(v_x_x27_747_);
v___x_756_ = l_Lean_mkAppN(v_x_x27_747_, v___x_755_);
lean_dec_ref(v___x_755_);
v___x_757_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_756_, v___y_749_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_757_);
v___x_759_ = l_Lean_Expr_fvarId_x21(v_x_736_);
v___x_760_ = lean_array_get_size(v_xs_737_);
v___x_761_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_759_, v___x_760_, v_fvarIdToPos_731_);
v___x_762_ = lean_array_push(v_xs_737_, v_x_736_);
v___x_763_ = lean_array_push(v_xs_x27_738_, v_x_x27_747_);
v___x_764_ = lean_array_push(v_args_739_, v_a_740_);
v___x_765_ = lean_array_push(v_subst_732_, v_a_758_);
v___x_766_ = lean_array_push(v_types_741_, v_a_742_);
v___x_767_ = lean_array_push(v_varDeps_743_, v_varPos_744_);
v___x_768_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_745_, v_body_746_, v___x_762_, v___x_763_, v___x_764_, v___x_765_, v___x_766_, v___x_767_, v___x_761_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_768_;
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_x_x27_747_);
lean_dec_ref(v_body_746_);
lean_dec_ref(v_haveExpr_745_);
lean_dec_ref(v_varPos_744_);
lean_dec_ref(v_varDeps_743_);
lean_dec_ref(v_a_742_);
lean_dec_ref(v_types_741_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_args_739_);
lean_dec_ref(v_xs_x27_738_);
lean_dec_ref(v_xs_737_);
lean_dec_ref(v_x_736_);
lean_dec_ref(v_subst_732_);
lean_dec(v_fvarIdToPos_731_);
v_a_769_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_757_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_757_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_777_, lean_object* v_e_778_, lean_object* v_xs_779_, lean_object* v_xs_x27_780_, lean_object* v_args_781_, lean_object* v_subst_782_, lean_object* v_types_783_, lean_object* v_varDeps_784_, lean_object* v_fvarIdToPos_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_777_, v_e_778_, v_xs_779_, v_xs_x27_780_, v_args_781_, v_subst_782_, v_types_783_, v_varDeps_784_, v_fvarIdToPos_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_794_, lean_object* v_t_795_, lean_object* v_k_796_, lean_object* v_fallback_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_795_, v_k_796_, v_fallback_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_799_, lean_object* v_t_800_, lean_object* v_k_801_, lean_object* v_fallback_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_799_, v_t_800_, v_k_801_, v_fallback_802_);
lean_dec(v_fallback_802_);
lean_dec(v_k_801_);
lean_dec(v_t_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_804_, lean_object* v_name_805_, uint8_t v_bi_806_, lean_object* v_type_807_, lean_object* v_k_808_, uint8_t v_kind_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_805_, v_bi_806_, v_type_807_, v_k_808_, v_kind_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_818_, lean_object* v_name_819_, lean_object* v_bi_820_, lean_object* v_type_821_, lean_object* v_k_822_, lean_object* v_kind_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v_bi_boxed_831_; uint8_t v_kind_boxed_832_; lean_object* v_res_833_; 
v_bi_boxed_831_ = lean_unbox(v_bi_820_);
v_kind_boxed_832_ = lean_unbox(v_kind_823_);
v_res_833_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_818_, v_name_819_, v_bi_boxed_831_, v_type_821_, v_k_822_, v_kind_boxed_832_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_834_, lean_object* v_name_835_, lean_object* v_type_836_, lean_object* v_k_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_835_, v_type_836_, v_k_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_846_, lean_object* v_name_847_, lean_object* v_type_848_, lean_object* v_k_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_846_, v_name_847_, v_type_848_, v_k_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_869_ = lean_box(1);
lean_inc_ref(v_haveExpr_860_);
v___x_870_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_860_, v_haveExpr_860_, v___x_868_, v___x_868_, v___x_868_, v___x_868_, v___x_868_, v___x_868_, v___x_869_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_880_, lean_object* v_n_881_){
_start:
{
lean_object* v_zero_882_; uint8_t v_isZero_883_; 
v_zero_882_ = lean_unsigned_to_nat(0u);
v_isZero_883_ = lean_nat_dec_eq(v_n_881_, v_zero_882_);
if (v_isZero_883_ == 1)
{
lean_dec(v_n_881_);
return v_type_880_;
}
else
{
lean_object* v_one_884_; lean_object* v_n_885_; lean_object* v___x_886_; 
v_one_884_ = lean_unsigned_to_nat(1u);
v_n_885_ = lean_nat_sub(v_n_881_, v_one_884_);
lean_dec(v_n_881_);
v___x_886_ = l_Lean_Expr_bindingBody_x21(v_type_880_);
lean_dec_ref(v_type_880_);
v_type_880_ = v___x_886_;
v_n_881_ = v_n_885_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0(void){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_888_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_00_u03b2_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object* v_idx_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = l_Lean_Expr_bvar___override(v_idx_893_);
v___x_896_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_895_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_idx_897_, uint8_t v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v_idx_897_, v___y_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_idx_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___y_21807__boxed_904_; lean_object* v_res_905_; 
v___y_21807__boxed_904_ = lean_unbox(v___y_902_);
v_res_905_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_idx_901_, v___y_21807__boxed_904_, v___y_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_msg_913_, uint8_t v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___f_921_; lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___f_938_; lean_object* v___x_1737__overap_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___f_916_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_917_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_918_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_919_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_920_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_921_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_922_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___f_916_);
lean_ctor_set(v___x_923_, 1, v___f_917_);
v___x_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___f_918_);
lean_ctor_set(v___x_924_, 2, v___f_919_);
lean_ctor_set(v___x_924_, 3, v___f_920_);
lean_ctor_set(v___x_924_, 4, v___f_921_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___f_922_);
lean_inc_ref_n(v___x_925_, 6);
v___f_926_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_926_, 0, v___x_925_);
v___f_927_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_927_, 0, v___x_925_);
v___f_928_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_928_, 0, v___x_925_);
v___f_929_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_929_, 0, v___x_925_);
v___x_930_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_930_, 0, lean_box(0));
lean_closure_set(v___x_930_, 1, lean_box(0));
lean_closure_set(v___x_930_, 2, v___x_925_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___f_926_);
v___x_932_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_932_, 0, lean_box(0));
lean_closure_set(v___x_932_, 1, lean_box(0));
lean_closure_set(v___x_932_, 2, v___x_925_);
v___x_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
lean_ctor_set(v___x_933_, 2, v___f_927_);
lean_ctor_set(v___x_933_, 3, v___f_928_);
lean_ctor_set(v___x_933_, 4, v___f_929_);
v___x_934_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_934_, 0, lean_box(0));
lean_closure_set(v___x_934_, 1, lean_box(0));
lean_closure_set(v___x_934_, 2, v___x_925_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_box(0);
v___x_937_ = l_instInhabitedOfMonad___redArg(v___x_935_, v___x_936_);
v___f_938_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_938_, 0, v___x_937_);
v___x_1737__overap_939_ = lean_panic_fn_borrowed(v___f_938_, v_msg_913_);
lean_dec_ref(v___f_938_);
v___x_940_ = lean_box(v___y_914_);
v___x_941_ = lean_apply_2(v___x_1737__overap_939_, v___x_940_, v___y_915_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_msg_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___y_21829__boxed_945_; lean_object* v_res_946_; 
v___y_21829__boxed_945_ = lean_unbox(v___y_943_);
v_res_946_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_msg_942_, v___y_21829__boxed_945_, v___y_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object* v_structName_947_, lean_object* v_idx_948_, lean_object* v_struct_949_, lean_object* v___y_950_, uint8_t v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___y_954_; lean_object* v___y_955_; 
if (v___y_951_ == 0)
{
v___y_954_ = v___y_950_;
v___y_955_ = v___y_952_;
goto v___jp_953_;
}
else
{
lean_object* v___x_968_; lean_object* v_snd_969_; 
lean_inc_ref(v_struct_949_);
v___x_968_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_949_, v___y_951_, v___y_952_);
v_snd_969_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_snd_969_);
lean_dec_ref(v___x_968_);
v___y_954_ = v___y_950_;
v___y_955_ = v_snd_969_;
goto v___jp_953_;
}
v___jp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
v___x_956_ = l_Lean_Expr_proj___override(v_structName_947_, v_idx_948_, v_struct_949_);
v___x_957_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_956_, v___y_955_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
v_snd_959_ = lean_ctor_get(v___x_957_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_967_ == 0)
{
v___x_961_ = v___x_957_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v___x_957_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___y_954_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fst_958_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___y_954_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v_snd_959_);
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object* v_structName_970_, lean_object* v_idx_971_, lean_object* v_struct_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v___y_21893__boxed_976_; lean_object* v_res_977_; 
v___y_21893__boxed_976_ = lean_unbox(v___y_974_);
v_res_977_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_structName_970_, v_idx_971_, v_struct_972_, v___y_973_, v___y_21893__boxed_976_, v___y_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object* v_x_978_, uint8_t v_bi_979_, lean_object* v_t_980_, lean_object* v_b_981_, lean_object* v___y_982_, uint8_t v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___y_986_; lean_object* v___y_987_; 
if (v___y_983_ == 0)
{
v___y_986_ = v___y_982_;
v___y_987_ = v___y_984_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1000_; lean_object* v_snd_1001_; lean_object* v___x_1002_; lean_object* v_snd_1003_; 
lean_inc_ref(v_t_980_);
v___x_1000_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_980_, v___y_983_, v___y_984_);
v_snd_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_snd_1001_);
lean_dec_ref(v___x_1000_);
lean_inc_ref(v_b_981_);
v___x_1002_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_981_, v___y_983_, v_snd_1001_);
v_snd_1003_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_snd_1003_);
lean_dec_ref(v___x_1002_);
v___y_986_ = v___y_982_;
v___y_987_ = v_snd_1003_;
goto v___jp_985_;
}
v___jp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v___x_988_ = l_Lean_Expr_lam___override(v_x_978_, v_t_980_, v_b_981_, v_bi_979_);
v___x_989_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_988_, v___y_987_);
v_fst_990_ = lean_ctor_get(v___x_989_, 0);
v_snd_991_ = lean_ctor_get(v___x_989_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_snd_991_);
lean_inc(v_fst_990_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___y_986_);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fst_990_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___y_986_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_snd_991_);
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object* v_x_1004_, lean_object* v_bi_1005_, lean_object* v_t_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_bi_boxed_1011_; uint8_t v___y_21937__boxed_1012_; lean_object* v_res_1013_; 
v_bi_boxed_1011_ = lean_unbox(v_bi_1005_);
v___y_21937__boxed_1012_ = lean_unbox(v___y_1009_);
v_res_1013_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_x_1004_, v_bi_boxed_1011_, v_t_1006_, v_b_1007_, v___y_1008_, v___y_21937__boxed_1012_, v___y_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object* v_msg_1014_, lean_object* v___y_1015_, uint8_t v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_21471__overap_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___f_1018_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_1019_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_1020_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_1021_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1022_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1023_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1024_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___f_1018_);
lean_ctor_set(v___x_1025_, 1, v___f_1019_);
v___x_1026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___f_1020_);
lean_ctor_set(v___x_1026_, 2, v___f_1021_);
lean_ctor_set(v___x_1026_, 3, v___f_1022_);
lean_ctor_set(v___x_1026_, 4, v___f_1023_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___f_1024_);
lean_inc_ref_n(v___x_1027_, 6);
v___f_1028_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
v___f_1029_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1029_, 0, v___x_1027_);
v___f_1030_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1030_, 0, v___x_1027_);
v___f_1031_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1031_, 0, v___x_1027_);
v___x_1032_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1032_, 0, lean_box(0));
lean_closure_set(v___x_1032_, 1, lean_box(0));
lean_closure_set(v___x_1032_, 2, v___x_1027_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___f_1028_);
v___x_1034_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1034_, 0, lean_box(0));
lean_closure_set(v___x_1034_, 1, lean_box(0));
lean_closure_set(v___x_1034_, 2, v___x_1027_);
v___x_1035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
lean_ctor_set(v___x_1035_, 2, v___f_1029_);
lean_ctor_set(v___x_1035_, 3, v___f_1030_);
lean_ctor_set(v___x_1035_, 4, v___f_1031_);
v___x_1036_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1036_, 0, lean_box(0));
lean_closure_set(v___x_1036_, 1, lean_box(0));
lean_closure_set(v___x_1036_, 2, v___x_1027_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_ReaderT_instMonad___redArg(v___x_1037_);
lean_inc_ref_n(v___x_1038_, 6);
v___f_1039_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1039_, 0, v___x_1038_);
v___f_1040_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1040_, 0, v___x_1038_);
v___f_1041_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1041_, 0, v___x_1038_);
v___f_1042_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1042_, 0, v___x_1038_);
v___x_1043_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1043_, 0, lean_box(0));
lean_closure_set(v___x_1043_, 1, lean_box(0));
lean_closure_set(v___x_1043_, 2, v___x_1038_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___f_1039_);
v___x_1045_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1045_, 0, lean_box(0));
lean_closure_set(v___x_1045_, 1, lean_box(0));
lean_closure_set(v___x_1045_, 2, v___x_1038_);
v___x_1046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
lean_ctor_set(v___x_1046_, 2, v___f_1040_);
lean_ctor_set(v___x_1046_, 3, v___f_1041_);
lean_ctor_set(v___x_1046_, 4, v___f_1042_);
v___x_1047_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1047_, 0, lean_box(0));
lean_closure_set(v___x_1047_, 1, lean_box(0));
lean_closure_set(v___x_1047_, 2, v___x_1038_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_instInhabitedExpr;
v___x_1050_ = l_instInhabitedOfMonad___redArg(v___x_1048_, v___x_1049_);
v___x_21471__overap_1051_ = lean_panic_fn_borrowed(v___x_1050_, v_msg_1014_);
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(v___y_1016_);
v___x_1053_ = lean_apply_3(v___x_21471__overap_1051_, v___y_1015_, v___x_1052_, v___y_1017_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v___y_21993__boxed_1058_; lean_object* v_res_1059_; 
v___y_21993__boxed_1058_ = lean_unbox(v___y_1056_);
v_res_1059_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v_msg_1054_, v___y_1055_, v___y_21993__boxed_1058_, v___y_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object* v_f_1060_, lean_object* v_a_1061_, lean_object* v___y_1062_, uint8_t v___y_1063_, lean_object* v___y_1064_){
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
lean_inc_ref(v_f_1060_);
v___x_1080_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1060_, v___y_1063_, v___y_1064_);
v_snd_1081_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_snd_1081_);
lean_dec_ref(v___x_1080_);
lean_inc_ref(v_a_1061_);
v___x_1082_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1061_, v___y_1063_, v_snd_1081_);
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
v___x_1068_ = l_Lean_Expr_app___override(v_f_1060_, v_a_1061_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object* v_f_1084_, lean_object* v_a_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v___y_22072__boxed_1089_; lean_object* v_res_1090_; 
v___y_22072__boxed_1089_ = lean_unbox(v___y_1087_);
v_res_1090_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_f_1084_, v_a_1085_, v___y_1086_, v___y_22072__boxed_1089_, v___y_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object* v_x_1091_, uint8_t v_bi_1092_, lean_object* v_t_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, uint8_t v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___y_1099_; lean_object* v___y_1100_; 
if (v___y_1096_ == 0)
{
v___y_1099_ = v___y_1095_;
v___y_1100_ = v___y_1097_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1113_; lean_object* v_snd_1114_; lean_object* v___x_1115_; lean_object* v_snd_1116_; 
lean_inc_ref(v_t_1093_);
v___x_1113_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1093_, v___y_1096_, v___y_1097_);
v_snd_1114_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_snd_1114_);
lean_dec_ref(v___x_1113_);
lean_inc_ref(v_b_1094_);
v___x_1115_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1094_, v___y_1096_, v_snd_1114_);
v_snd_1116_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_snd_1116_);
lean_dec_ref(v___x_1115_);
v___y_1099_ = v___y_1095_;
v___y_1100_ = v_snd_1116_;
goto v___jp_1098_;
}
v___jp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1112_; 
v___x_1101_ = l_Lean_Expr_forallE___override(v_x_1091_, v_t_1093_, v_b_1094_, v_bi_1092_);
v___x_1102_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1101_, v___y_1100_);
v_fst_1103_ = lean_ctor_get(v___x_1102_, 0);
v_snd_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___y_1099_);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1103_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___y_1099_);
v___x_1109_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_snd_1104_);
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object* v_x_1117_, lean_object* v_bi_1118_, lean_object* v_t_1119_, lean_object* v_b_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v_bi_boxed_1124_; uint8_t v___y_22121__boxed_1125_; lean_object* v_res_1126_; 
v_bi_boxed_1124_ = lean_unbox(v_bi_1118_);
v___y_22121__boxed_1125_ = lean_unbox(v___y_1122_);
v_res_1126_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_x_1117_, v_bi_boxed_1124_, v_t_1119_, v_b_1120_, v___y_1121_, v___y_22121__boxed_1125_, v___y_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object* v_x_1127_, lean_object* v_t_1128_, lean_object* v_v_1129_, lean_object* v_b_1130_, uint8_t v_nondep_1131_, lean_object* v___y_1132_, uint8_t v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___y_1136_; lean_object* v___y_1137_; 
if (v___y_1133_ == 0)
{
v___y_1136_ = v___y_1132_;
v___y_1137_ = v___y_1134_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1150_; lean_object* v_snd_1151_; lean_object* v___x_1152_; lean_object* v_snd_1153_; lean_object* v___x_1154_; lean_object* v_snd_1155_; 
lean_inc_ref(v_t_1128_);
v___x_1150_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1128_, v___y_1133_, v___y_1134_);
v_snd_1151_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_snd_1151_);
lean_dec_ref(v___x_1150_);
lean_inc_ref(v_v_1129_);
v___x_1152_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1129_, v___y_1133_, v_snd_1151_);
v_snd_1153_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_snd_1153_);
lean_dec_ref(v___x_1152_);
lean_inc_ref(v_b_1130_);
v___x_1154_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1130_, v___y_1133_, v_snd_1153_);
v_snd_1155_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v___x_1154_);
v___y_1136_ = v___y_1132_;
v___y_1137_ = v_snd_1155_;
goto v___jp_1135_;
}
v___jp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
v___x_1138_ = l_Lean_Expr_letE___override(v_x_1127_, v_t_1128_, v_v_1129_, v_b_1130_, v_nondep_1131_);
v___x_1139_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1138_, v___y_1137_);
v_fst_1140_ = lean_ctor_get(v___x_1139_, 0);
v_snd_1141_ = lean_ctor_get(v___x_1139_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v___x_1139_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v___x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___y_1136_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___y_1136_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_snd_1141_);
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object* v_x_1156_, lean_object* v_t_1157_, lean_object* v_v_1158_, lean_object* v_b_1159_, lean_object* v_nondep_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_nondep_boxed_1164_; uint8_t v___y_22170__boxed_1165_; lean_object* v_res_1166_; 
v_nondep_boxed_1164_ = lean_unbox(v_nondep_1160_);
v___y_22170__boxed_1165_ = lean_unbox(v___y_1162_);
v_res_1166_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_x_1156_, v_t_1157_, v_v_1158_, v_b_1159_, v_nondep_boxed_1164_, v___y_1161_, v___y_22170__boxed_1165_, v___y_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_a_1167_, lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
else
{
lean_object* v_key_1170_; lean_object* v_value_1171_; lean_object* v_tail_1172_; uint8_t v___y_1174_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; uint8_t v___x_1181_; 
v_key_1170_ = lean_ctor_get(v_x_1168_, 0);
v_value_1171_ = lean_ctor_get(v_x_1168_, 1);
v_tail_1172_ = lean_ctor_get(v_x_1168_, 2);
v_fst_1177_ = lean_ctor_get(v_key_1170_, 0);
v_snd_1178_ = lean_ctor_get(v_key_1170_, 1);
v_fst_1179_ = lean_ctor_get(v_a_1167_, 0);
v_snd_1180_ = lean_ctor_get(v_a_1167_, 1);
v___x_1181_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1177_, v_fst_1179_);
if (v___x_1181_ == 0)
{
v___y_1174_ = v___x_1181_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_nat_dec_eq(v_snd_1178_, v_snd_1180_);
v___y_1174_ = v___x_1182_;
goto v___jp_1173_;
}
v___jp_1173_:
{
if (v___y_1174_ == 0)
{
v_x_1168_ = v_tail_1172_;
goto _start;
}
else
{
lean_object* v___x_1176_; 
lean_inc(v_value_1171_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_value_1171_);
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object* v_a_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1183_, v_x_1184_);
lean_dec(v_x_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object* v_m_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_buckets_1188_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; uint64_t v___x_1195_; uint64_t v___x_1196_; uint64_t v_fold_1197_; uint64_t v___x_1198_; uint64_t v___x_1199_; uint64_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_buckets_1188_ = lean_ctor_get(v_m_1186_, 1);
v_fst_1189_ = lean_ctor_get(v_a_1187_, 0);
v_snd_1190_ = lean_ctor_get(v_a_1187_, 1);
v___x_1191_ = lean_array_get_size(v_buckets_1188_);
v___x_1192_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1189_);
v___x_1193_ = lean_uint64_of_nat(v_snd_1190_);
v___x_1194_ = lean_uint64_mix_hash(v___x_1192_, v___x_1193_);
v___x_1195_ = 32ULL;
v___x_1196_ = lean_uint64_shift_right(v___x_1194_, v___x_1195_);
v_fold_1197_ = lean_uint64_xor(v___x_1194_, v___x_1196_);
v___x_1198_ = 16ULL;
v___x_1199_ = lean_uint64_shift_right(v_fold_1197_, v___x_1198_);
v___x_1200_ = lean_uint64_xor(v_fold_1197_, v___x_1199_);
v___x_1201_ = lean_uint64_to_usize(v___x_1200_);
v___x_1202_ = lean_usize_of_nat(v___x_1191_);
v___x_1203_ = ((size_t)1ULL);
v___x_1204_ = lean_usize_sub(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_usize_land(v___x_1201_, v___x_1204_);
v___x_1206_ = lean_array_uget_borrowed(v_buckets_1188_, v___x_1205_);
v___x_1207_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1187_, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1208_, v_a_1209_);
lean_dec_ref(v_a_1209_);
lean_dec_ref(v_m_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object* v_d_1211_, lean_object* v_e_1212_, lean_object* v___y_1213_, uint8_t v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___y_1217_; lean_object* v___y_1218_; 
if (v___y_1214_ == 0)
{
v___y_1217_ = v___y_1213_;
v___y_1218_ = v___y_1215_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1231_; lean_object* v_snd_1232_; 
lean_inc_ref(v_e_1212_);
v___x_1231_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1212_, v___y_1214_, v___y_1215_);
v_snd_1232_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_snd_1232_);
lean_dec_ref(v___x_1231_);
v___y_1217_ = v___y_1213_;
v___y_1218_ = v_snd_1232_;
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_fst_1221_; lean_object* v_snd_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
v___x_1219_ = l_Lean_Expr_mdata___override(v_d_1211_, v_e_1212_);
v___x_1220_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1219_, v___y_1218_);
v_fst_1221_ = lean_ctor_get(v___x_1220_, 0);
v_snd_1222_ = lean_ctor_get(v___x_1220_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1224_ = v___x_1220_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_snd_1222_);
lean_inc(v_fst_1221_);
lean_dec(v___x_1220_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___y_1217_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_fst_1221_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___y_1217_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v_snd_1222_);
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object* v_d_1233_, lean_object* v_e_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___y_22293__boxed_1238_; lean_object* v_res_1239_; 
v___y_22293__boxed_1238_ = lean_unbox(v___y_1236_);
v_res_1239_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_d_1233_, v_e_1234_, v___y_1235_, v___y_22293__boxed_1238_, v___y_1237_);
return v_res_1239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Array_instInhabited(lean_box(0));
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2));
v___x_1244_ = lean_unsigned_to_nat(12u);
v___x_1245_ = lean_unsigned_to_nat(234u);
v___x_1246_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1));
v___x_1247_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1248_ = l_mkPanicMessageWithDecl(v___x_1247_, v___x_1246_, v___x_1245_, v___x_1244_, v___x_1243_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1253_ = lean_unsigned_to_nat(67u);
v___x_1254_ = lean_unsigned_to_nat(35u);
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1));
v___x_1256_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0));
v___x_1257_ = l_mkPanicMessageWithDecl(v___x_1256_, v___x_1255_, v___x_1254_, v___x_1253_, v___x_1252_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_n_1258_, lean_object* v_varDeps_1259_, lean_object* v_xs_1260_, lean_object* v_e_1261_, lean_object* v_offset_1262_, lean_object* v_a_1263_, uint8_t v_a_1264_, lean_object* v_a_1265_){
_start:
{
switch(lean_obj_tag(v_e_1261_))
{
case 5:
{
lean_object* v_fn_1266_; lean_object* v_arg_1267_; lean_object* v___x_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___x_1273_; lean_object* v_fst_1274_; lean_object* v_snd_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1296_; 
v_fn_1266_ = lean_ctor_get(v_e_1261_, 0);
v_arg_1267_ = lean_ctor_get(v_e_1261_, 1);
lean_inc(v_offset_1262_);
lean_inc_ref(v_fn_1266_);
v___x_1268_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_fn_1266_, v_offset_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_fst_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_fst_1269_);
v_snd_1270_ = lean_ctor_get(v___x_1268_, 1);
lean_inc(v_snd_1270_);
lean_dec_ref(v___x_1268_);
v_fst_1271_ = lean_ctor_get(v_fst_1269_, 0);
lean_inc(v_fst_1271_);
v_snd_1272_ = lean_ctor_get(v_fst_1269_, 1);
lean_inc(v_snd_1272_);
lean_dec(v_fst_1269_);
lean_inc_ref(v_arg_1267_);
v___x_1273_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_arg_1267_, v_offset_1262_, v_snd_1272_, v_a_1264_, v_snd_1270_);
v_fst_1274_ = lean_ctor_get(v___x_1273_, 0);
v_snd_1275_ = lean_ctor_get(v___x_1273_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1277_ = v___x_1273_;
v_isShared_1278_ = v_isSharedCheck_1296_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_snd_1275_);
lean_inc(v_fst_1274_);
lean_dec(v___x_1273_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1296_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_fst_1279_; lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1295_; 
v_fst_1279_ = lean_ctor_get(v_fst_1274_, 0);
v_snd_1280_ = lean_ctor_get(v_fst_1274_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_fst_1274_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1282_ = v_fst_1274_;
v_isShared_1283_ = v_isSharedCheck_1295_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_inc(v_fst_1279_);
lean_dec(v_fst_1274_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1295_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
uint8_t v___y_1285_; uint8_t v___x_1293_; 
v___x_1293_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1266_, v_fst_1271_);
if (v___x_1293_ == 0)
{
v___y_1285_ = v___x_1293_;
goto v___jp_1284_;
}
else
{
uint8_t v___x_1294_; 
v___x_1294_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1267_, v_fst_1279_);
v___y_1285_ = v___x_1294_;
goto v___jp_1284_;
}
v___jp_1284_:
{
if (v___y_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_del_object(v___x_1282_);
lean_del_object(v___x_1277_);
lean_dec_ref(v_e_1261_);
v___x_1286_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_fst_1271_, v_fst_1279_, v_snd_1280_, v_a_1264_, v_snd_1275_);
return v___x_1286_;
}
else
{
lean_object* v___x_1288_; 
lean_dec(v_fst_1279_);
lean_dec(v_fst_1271_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_e_1261_);
v___x_1288_ = v___x_1282_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_e_1261_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_snd_1280_);
v___x_1288_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1290_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1288_);
v___x_1290_ = v___x_1277_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_snd_1275_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_1297_; lean_object* v_binderType_1298_; lean_object* v_body_1299_; uint8_t v_binderInfo_1300_; lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_fst_1309_; lean_object* v_snd_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1331_; 
v_binderName_1297_ = lean_ctor_get(v_e_1261_, 0);
v_binderType_1298_ = lean_ctor_get(v_e_1261_, 1);
v_body_1299_ = lean_ctor_get(v_e_1261_, 2);
v_binderInfo_1300_ = lean_ctor_get_uint8(v_e_1261_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1262_);
lean_inc_ref(v_binderType_1298_);
v___x_1301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_binderType_1298_, v_offset_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___x_1301_);
v_fst_1304_ = lean_ctor_get(v_fst_1302_, 0);
lean_inc(v_fst_1304_);
v_snd_1305_ = lean_ctor_get(v_fst_1302_, 1);
lean_inc(v_snd_1305_);
lean_dec(v_fst_1302_);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_add(v_offset_1262_, v___x_1306_);
lean_dec(v_offset_1262_);
lean_inc_ref(v_body_1299_);
v___x_1308_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_body_1299_, v___x_1307_, v_snd_1305_, v_a_1264_, v_snd_1303_);
v_fst_1309_ = lean_ctor_get(v___x_1308_, 0);
v_snd_1310_ = lean_ctor_get(v___x_1308_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1312_ = v___x_1308_;
v_isShared_1313_ = v_isSharedCheck_1331_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_snd_1310_);
lean_inc(v_fst_1309_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1331_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1330_; 
v_fst_1314_ = lean_ctor_get(v_fst_1309_, 0);
v_snd_1315_ = lean_ctor_get(v_fst_1309_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_fst_1309_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1317_ = v_fst_1309_;
v_isShared_1318_ = v_isSharedCheck_1330_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_fst_1309_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1330_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___y_1320_; uint8_t v___x_1328_; 
v___x_1328_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1298_, v_fst_1304_);
if (v___x_1328_ == 0)
{
v___y_1320_ = v___x_1328_;
goto v___jp_1319_;
}
else
{
uint8_t v___x_1329_; 
v___x_1329_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1299_, v_fst_1314_);
v___y_1320_ = v___x_1329_;
goto v___jp_1319_;
}
v___jp_1319_:
{
if (v___y_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_inc(v_binderName_1297_);
lean_del_object(v___x_1317_);
lean_del_object(v___x_1312_);
lean_dec_ref(v_e_1261_);
v___x_1321_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_binderName_1297_, v_binderInfo_1300_, v_fst_1304_, v_fst_1314_, v_snd_1315_, v_a_1264_, v_snd_1310_);
return v___x_1321_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_fst_1314_);
lean_dec(v_fst_1304_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_e_1261_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_e_1261_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_snd_1315_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1323_);
v___x_1325_ = v___x_1312_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_snd_1310_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1332_; lean_object* v_binderType_1333_; lean_object* v_body_1334_; uint8_t v_binderInfo_1335_; lean_object* v___x_1336_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1366_; 
v_binderName_1332_ = lean_ctor_get(v_e_1261_, 0);
v_binderType_1333_ = lean_ctor_get(v_e_1261_, 1);
v_body_1334_ = lean_ctor_get(v_e_1261_, 2);
v_binderInfo_1335_ = lean_ctor_get_uint8(v_e_1261_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1262_);
lean_inc_ref(v_binderType_1333_);
v___x_1336_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_binderType_1333_, v_offset_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_fst_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_fst_1337_);
v_snd_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v___x_1336_);
v_fst_1339_ = lean_ctor_get(v_fst_1337_, 0);
lean_inc(v_fst_1339_);
v_snd_1340_ = lean_ctor_get(v_fst_1337_, 1);
lean_inc(v_snd_1340_);
lean_dec(v_fst_1337_);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_add(v_offset_1262_, v___x_1341_);
lean_dec(v_offset_1262_);
lean_inc_ref(v_body_1334_);
v___x_1343_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_body_1334_, v___x_1342_, v_snd_1340_, v_a_1264_, v_snd_1338_);
v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
v_snd_1345_ = lean_ctor_get(v___x_1343_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1347_ = v___x_1343_;
v_isShared_1348_ = v_isSharedCheck_1366_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v___x_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1366_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1365_; 
v_fst_1349_ = lean_ctor_get(v_fst_1344_, 0);
v_snd_1350_ = lean_ctor_get(v_fst_1344_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_fst_1344_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1352_ = v_fst_1344_;
v_isShared_1353_ = v_isSharedCheck_1365_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snd_1350_);
lean_inc(v_fst_1349_);
lean_dec(v_fst_1344_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1365_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
uint8_t v___y_1355_; uint8_t v___x_1363_; 
v___x_1363_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1333_, v_fst_1339_);
if (v___x_1363_ == 0)
{
v___y_1355_ = v___x_1363_;
goto v___jp_1354_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1334_, v_fst_1349_);
v___y_1355_ = v___x_1364_;
goto v___jp_1354_;
}
v___jp_1354_:
{
if (v___y_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_inc(v_binderName_1332_);
lean_del_object(v___x_1352_);
lean_del_object(v___x_1347_);
lean_dec_ref(v_e_1261_);
v___x_1356_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_binderName_1332_, v_binderInfo_1335_, v_fst_1339_, v_fst_1349_, v_snd_1350_, v_a_1264_, v_snd_1345_);
return v___x_1356_;
}
else
{
lean_object* v___x_1358_; 
lean_dec(v_fst_1349_);
lean_dec(v_fst_1339_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_e_1261_);
v___x_1358_ = v___x_1352_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_e_1261_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_snd_1350_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1358_);
v___x_1360_ = v___x_1347_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_snd_1345_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1367_; lean_object* v_type_1368_; lean_object* v_value_1369_; lean_object* v_body_1370_; uint8_t v_nondep_1371_; lean_object* v___x_1372_; lean_object* v_fst_1373_; lean_object* v_snd_1374_; lean_object* v_fst_1375_; lean_object* v_snd_1376_; lean_object* v___x_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_fst_1385_; lean_object* v_snd_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1409_; 
v_declName_1367_ = lean_ctor_get(v_e_1261_, 0);
v_type_1368_ = lean_ctor_get(v_e_1261_, 1);
v_value_1369_ = lean_ctor_get(v_e_1261_, 2);
v_body_1370_ = lean_ctor_get(v_e_1261_, 3);
v_nondep_1371_ = lean_ctor_get_uint8(v_e_1261_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_1262_, 2);
lean_inc_ref(v_type_1368_);
v___x_1372_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_type_1368_, v_offset_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_fst_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_fst_1373_);
v_snd_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_snd_1374_);
lean_dec_ref(v___x_1372_);
v_fst_1375_ = lean_ctor_get(v_fst_1373_, 0);
lean_inc(v_fst_1375_);
v_snd_1376_ = lean_ctor_get(v_fst_1373_, 1);
lean_inc(v_snd_1376_);
lean_dec(v_fst_1373_);
lean_inc_ref(v_value_1369_);
v___x_1377_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_value_1369_, v_offset_1262_, v_snd_1376_, v_a_1264_, v_snd_1374_);
v_fst_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_fst_1378_);
v_snd_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_snd_1379_);
lean_dec_ref(v___x_1377_);
v_fst_1380_ = lean_ctor_get(v_fst_1378_, 0);
lean_inc(v_fst_1380_);
v_snd_1381_ = lean_ctor_get(v_fst_1378_, 1);
lean_inc(v_snd_1381_);
lean_dec(v_fst_1378_);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_offset_1262_, v___x_1382_);
lean_dec(v_offset_1262_);
lean_inc_ref(v_body_1370_);
v___x_1384_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_body_1370_, v___x_1383_, v_snd_1381_, v_a_1264_, v_snd_1379_);
v_fst_1385_ = lean_ctor_get(v___x_1384_, 0);
v_snd_1386_ = lean_ctor_get(v___x_1384_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1388_ = v___x_1384_;
v_isShared_1389_ = v_isSharedCheck_1409_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snd_1386_);
lean_inc(v_fst_1385_);
lean_dec(v___x_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1409_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v_fst_1390_; lean_object* v_snd_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1408_; 
v_fst_1390_ = lean_ctor_get(v_fst_1385_, 0);
v_snd_1391_ = lean_ctor_get(v_fst_1385_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_fst_1385_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1393_ = v_fst_1385_;
v_isShared_1394_ = v_isSharedCheck_1408_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_snd_1391_);
lean_inc(v_fst_1390_);
lean_dec(v_fst_1385_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1408_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v___y_1396_; uint8_t v___x_1406_; 
v___x_1406_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1368_, v_fst_1375_);
if (v___x_1406_ == 0)
{
v___y_1396_ = v___x_1406_;
goto v___jp_1395_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1369_, v_fst_1380_);
v___y_1396_ = v___x_1407_;
goto v___jp_1395_;
}
v___jp_1395_:
{
if (v___y_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_inc(v_declName_1367_);
lean_del_object(v___x_1393_);
lean_del_object(v___x_1388_);
lean_dec_ref(v_e_1261_);
v___x_1397_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1367_, v_fst_1375_, v_fst_1380_, v_fst_1390_, v_nondep_1371_, v_snd_1391_, v_a_1264_, v_snd_1386_);
return v___x_1397_;
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1370_, v_fst_1390_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_inc(v_declName_1367_);
lean_del_object(v___x_1393_);
lean_del_object(v___x_1388_);
lean_dec_ref(v_e_1261_);
v___x_1399_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1367_, v_fst_1375_, v_fst_1380_, v_fst_1390_, v_nondep_1371_, v_snd_1391_, v_a_1264_, v_snd_1386_);
return v___x_1399_;
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_fst_1390_);
lean_dec(v_fst_1380_);
lean_dec(v_fst_1375_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_e_1261_);
v___x_1401_ = v___x_1393_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_e_1261_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_snd_1391_);
v___x_1401_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1401_);
v___x_1403_ = v___x_1388_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1386_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
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
lean_object* v_data_1410_; lean_object* v_expr_1411_; lean_object* v___x_1412_; lean_object* v_fst_1413_; lean_object* v_snd_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1432_; 
v_data_1410_ = lean_ctor_get(v_e_1261_, 0);
v_expr_1411_ = lean_ctor_get(v_e_1261_, 1);
lean_inc_ref(v_expr_1411_);
v___x_1412_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_expr_1411_, v_offset_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_fst_1413_ = lean_ctor_get(v___x_1412_, 0);
v_snd_1414_ = lean_ctor_get(v___x_1412_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_snd_1414_);
lean_inc(v_fst_1413_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1431_; 
v_fst_1418_ = lean_ctor_get(v_fst_1413_, 0);
v_snd_1419_ = lean_ctor_get(v_fst_1413_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_fst_1413_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1421_ = v_fst_1413_;
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_inc(v_fst_1418_);
lean_dec(v_fst_1413_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
uint8_t v___x_1423_; 
v___x_1423_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1411_, v_fst_1418_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_inc(v_data_1410_);
lean_del_object(v___x_1421_);
lean_del_object(v___x_1416_);
lean_dec_ref(v_e_1261_);
v___x_1424_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_data_1410_, v_fst_1418_, v_snd_1419_, v_a_1264_, v_snd_1414_);
return v___x_1424_;
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_fst_1418_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_e_1261_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_e_1261_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1419_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1426_);
v___x_1428_ = v___x_1416_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_snd_1414_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1433_; lean_object* v_idx_1434_; lean_object* v_struct_1435_; lean_object* v___x_1436_; lean_object* v_fst_1437_; lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1456_; 
v_typeName_1433_ = lean_ctor_get(v_e_1261_, 0);
v_idx_1434_ = lean_ctor_get(v_e_1261_, 1);
v_struct_1435_ = lean_ctor_get(v_e_1261_, 2);
lean_inc_ref(v_struct_1435_);
v___x_1436_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1258_, v_varDeps_1259_, v_xs_1260_, v_struct_1435_, v_offset_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
v_fst_1437_ = lean_ctor_get(v___x_1436_, 0);
v_snd_1438_ = lean_ctor_get(v___x_1436_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1440_ = v___x_1436_;
v_isShared_1441_ = v_isSharedCheck_1456_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_inc(v_fst_1437_);
lean_dec(v___x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1456_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_fst_1442_; lean_object* v_snd_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1455_; 
v_fst_1442_ = lean_ctor_get(v_fst_1437_, 0);
v_snd_1443_ = lean_ctor_get(v_fst_1437_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_fst_1437_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1445_ = v_fst_1437_;
v_isShared_1446_ = v_isSharedCheck_1455_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_snd_1443_);
lean_inc(v_fst_1442_);
lean_dec(v_fst_1437_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1455_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
uint8_t v___x_1447_; 
v___x_1447_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1435_, v_fst_1442_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_inc(v_idx_1434_);
lean_inc(v_typeName_1433_);
lean_del_object(v___x_1445_);
lean_del_object(v___x_1440_);
lean_dec_ref(v_e_1261_);
v___x_1448_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_typeName_1433_, v_idx_1434_, v_fst_1442_, v_snd_1443_, v_a_1264_, v_snd_1438_);
return v___x_1448_;
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_fst_1442_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_e_1261_);
v___x_1450_ = v___x_1445_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_e_1261_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_snd_1443_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1450_);
v___x_1452_ = v___x_1440_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_snd_1438_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_offset_1262_);
lean_dec_ref(v_e_1261_);
v___x_1457_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3);
v___x_1458_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v___x_1457_, v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object* v_n_1459_, lean_object* v_varDeps_1460_, lean_object* v_xs_1461_, lean_object* v_e_1462_, lean_object* v_offset_1463_, lean_object* v_a_1464_, uint8_t v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_key_1467_; lean_object* v_snd_1469_; lean_object* v___x_1482_; 
lean_inc(v_offset_1463_);
lean_inc_ref(v_e_1462_);
v_key_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1467_, 0, v_e_1462_);
lean_ctor_set(v_key_1467_, 1, v_offset_1463_);
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_a_1464_, v_key_1467_);
if (lean_obj_tag(v___x_1482_) == 1)
{
lean_object* v_val_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_key_1467_);
lean_dec(v_offset_1463_);
lean_dec_ref(v_e_1462_);
v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_val_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_val_1483_);
lean_ctor_set(v___x_1484_, 1, v_a_1464_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_a_1466_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
lean_dec(v___x_1482_);
v___x_1486_ = l_Lean_Expr_looseBVarRange(v_e_1462_);
v___x_1487_ = lean_nat_dec_le(v___x_1486_, v_offset_1463_);
lean_dec(v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Expr_getAppFn(v_e_1462_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_deBruijnIndex_1489_; uint8_t v___x_1490_; 
v_deBruijnIndex_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_deBruijnIndex_1489_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = lean_nat_dec_le(v_offset_1463_, v_deBruijnIndex_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec(v_deBruijnIndex_1489_);
lean_dec(v_offset_1463_);
v___x_1491_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_nat_add(v_offset_1463_, v_n_1459_);
v___x_1493_ = lean_nat_dec_lt(v_deBruijnIndex_1489_, v___x_1492_);
lean_dec(v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1498_; 
lean_dec(v_offset_1463_);
lean_dec_ref(v_e_1462_);
v___x_1494_ = lean_nat_sub(v_deBruijnIndex_1489_, v_n_1459_);
lean_dec(v_deBruijnIndex_1489_);
v___x_1495_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1494_, v_a_1466_);
v_fst_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v___x_1495_, 1);
lean_inc(v_snd_1497_);
lean_dec_ref(v___x_1495_);
v___x_1498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_fst_1496_, v_a_1464_, v_a_1465_, v_snd_1497_);
return v___x_1498_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_i_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_expectedNumArgs_1505_; lean_object* v_numArgs_1506_; uint8_t v___x_1507_; 
v___x_1499_ = lean_nat_sub(v_deBruijnIndex_1489_, v_offset_1463_);
lean_dec(v_deBruijnIndex_1489_);
v___x_1500_ = lean_nat_sub(v_n_1459_, v___x_1499_);
lean_dec(v___x_1499_);
v___x_1501_ = lean_unsigned_to_nat(1u);
v_i_1502_ = lean_nat_sub(v___x_1500_, v___x_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1504_ = lean_array_get_borrowed(v___x_1503_, v_varDeps_1460_, v_i_1502_);
v_expectedNumArgs_1505_ = lean_array_get_size(v___x_1504_);
v_numArgs_1506_ = l_Lean_Expr_getAppNumArgs(v_e_1462_);
v___x_1507_ = lean_nat_dec_lt(v_expectedNumArgs_1505_, v_numArgs_1506_);
if (v___x_1507_ == 0)
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_nat_dec_eq(v_numArgs_1506_, v_expectedNumArgs_1505_);
lean_dec(v_numArgs_1506_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_fst_1511_; 
lean_dec(v_i_1502_);
v___x_1509_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1510_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1509_, v_a_1465_, v_a_1466_);
v_fst_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_fst_1511_);
if (lean_obj_tag(v_fst_1511_) == 1)
{
lean_object* v_snd_1512_; lean_object* v_val_1513_; lean_object* v___x_1514_; 
lean_dec(v_offset_1463_);
lean_dec_ref(v_e_1462_);
v_snd_1512_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_snd_1512_);
lean_dec_ref(v___x_1510_);
v_val_1513_ = lean_ctor_get(v_fst_1511_, 0);
lean_inc(v_val_1513_);
lean_dec_ref(v_fst_1511_);
v___x_1514_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_val_1513_, v_a_1464_, v_a_1465_, v_snd_1512_);
return v___x_1514_;
}
else
{
lean_object* v_snd_1515_; 
lean_dec(v_fst_1511_);
v_snd_1515_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_snd_1515_);
lean_dec_ref(v___x_1510_);
v_snd_1469_ = v_snd_1515_;
goto v___jp_1468_;
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_offset_1463_);
lean_dec_ref(v_e_1462_);
v___x_1516_ = lean_array_fget_borrowed(v_xs_1461_, v_i_1502_);
lean_dec(v_i_1502_);
lean_inc(v___x_1516_);
v___x_1517_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v___x_1516_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1517_;
}
}
else
{
lean_dec(v_numArgs_1506_);
lean_dec(v_i_1502_);
v_snd_1469_ = v_a_1466_;
goto v___jp_1468_;
}
}
}
}
else
{
lean_dec_ref(v___x_1488_);
v_snd_1469_ = v_a_1466_;
goto v___jp_1468_;
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_offset_1463_);
v___x_1518_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1518_;
}
}
v___jp_1468_:
{
switch(lean_obj_tag(v_e_1462_))
{
case 9:
{
lean_object* v___x_1470_; 
lean_dec(v_offset_1463_);
v___x_1470_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_snd_1469_);
return v___x_1470_;
}
case 2:
{
lean_object* v___x_1471_; 
lean_dec(v_offset_1463_);
v___x_1471_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_snd_1469_);
return v___x_1471_;
}
case 0:
{
lean_object* v___x_1472_; 
lean_dec(v_offset_1463_);
v___x_1472_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_snd_1469_);
return v___x_1472_;
}
case 1:
{
lean_object* v___x_1473_; 
lean_dec(v_offset_1463_);
v___x_1473_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_snd_1469_);
return v___x_1473_;
}
case 4:
{
lean_object* v___x_1474_; 
lean_dec(v_offset_1463_);
v___x_1474_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_snd_1469_);
return v___x_1474_;
}
case 3:
{
lean_object* v___x_1475_; 
lean_dec(v_offset_1463_);
v___x_1475_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_e_1462_, v_a_1464_, v_a_1465_, v_snd_1469_);
return v___x_1475_;
}
default: 
{
lean_object* v___x_1476_; lean_object* v_fst_1477_; lean_object* v_snd_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1481_; 
v___x_1476_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1459_, v_varDeps_1460_, v_xs_1461_, v_e_1462_, v_offset_1463_, v_a_1464_, v_a_1465_, v_snd_1469_);
v_fst_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_fst_1477_);
v_snd_1478_ = lean_ctor_get(v___x_1476_, 1);
lean_inc(v_snd_1478_);
lean_dec_ref(v___x_1476_);
v_fst_1479_ = lean_ctor_get(v_fst_1477_, 0);
lean_inc(v_fst_1479_);
v_snd_1480_ = lean_ctor_get(v_fst_1477_, 1);
lean_inc(v_snd_1480_);
lean_dec(v_fst_1477_);
v___x_1481_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1467_, v_fst_1479_, v_snd_1480_, v_a_1465_, v_snd_1478_);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object* v_n_1519_, lean_object* v_varDeps_1520_, lean_object* v_xs_1521_, lean_object* v_e_1522_, lean_object* v_offset_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
uint8_t v_a_boxed_1527_; lean_object* v_res_1528_; 
v_a_boxed_1527_ = lean_unbox(v_a_1525_);
v_res_1528_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1519_, v_varDeps_1520_, v_xs_1521_, v_e_1522_, v_offset_1523_, v_a_1524_, v_a_boxed_1527_, v_a_1526_);
lean_dec_ref(v_xs_1521_);
lean_dec_ref(v_varDeps_1520_);
lean_dec(v_n_1519_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_n_1529_, lean_object* v_varDeps_1530_, lean_object* v_xs_1531_, lean_object* v_e_1532_, lean_object* v_offset_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
uint8_t v_a_boxed_1537_; lean_object* v_res_1538_; 
v_a_boxed_1537_ = lean_unbox(v_a_1535_);
v_res_1538_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1529_, v_varDeps_1530_, v_xs_1531_, v_e_1532_, v_offset_1533_, v_a_1534_, v_a_boxed_1537_, v_a_1536_);
lean_dec_ref(v_xs_1531_);
lean_dec_ref(v_varDeps_1530_);
lean_dec(v_n_1529_);
return v_res_1538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0(void){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_box(0));
return v___x_1539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_unsigned_to_nat(16u);
v___x_1542_ = lean_mk_array(v___x_1541_, v___x_1540_);
return v___x_1542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object* v_e_1546_, lean_object* v_xs_1547_, lean_object* v_varDeps_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v_share_1552_; lean_object* v_maxFVar_1553_; lean_object* v_proofInstInfo_1554_; lean_object* v_inferType_1555_; lean_object* v_getLevel_1556_; lean_object* v_congrInfo_1557_; lean_object* v_defEqI_1558_; lean_object* v_extensions_1559_; lean_object* v_issues_1560_; lean_object* v_canon_1561_; uint8_t v_debug_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1632_; 
v___x_1551_ = lean_st_ref_take(v_a_1549_);
v_share_1552_ = lean_ctor_get(v___x_1551_, 0);
v_maxFVar_1553_ = lean_ctor_get(v___x_1551_, 1);
v_proofInstInfo_1554_ = lean_ctor_get(v___x_1551_, 2);
v_inferType_1555_ = lean_ctor_get(v___x_1551_, 3);
v_getLevel_1556_ = lean_ctor_get(v___x_1551_, 4);
v_congrInfo_1557_ = lean_ctor_get(v___x_1551_, 5);
v_defEqI_1558_ = lean_ctor_get(v___x_1551_, 6);
v_extensions_1559_ = lean_ctor_get(v___x_1551_, 7);
v_issues_1560_ = lean_ctor_get(v___x_1551_, 8);
v_canon_1561_ = lean_ctor_get(v___x_1551_, 9);
v_debug_1562_ = lean_ctor_get_uint8(v___x_1551_, sizeof(void*)*10);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1564_ = v___x_1551_;
v_isShared_1565_ = v_isSharedCheck_1632_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_canon_1561_);
lean_inc(v_issues_1560_);
lean_inc(v_extensions_1559_);
lean_inc(v_defEqI_1558_);
lean_inc(v_congrInfo_1557_);
lean_inc(v_getLevel_1556_);
lean_inc(v_inferType_1555_);
lean_inc(v_proofInstInfo_1554_);
lean_inc(v_maxFVar_1553_);
lean_inc(v_share_1552_);
lean_dec(v___x_1551_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1632_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_maxFVar_1553_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_proofInstInfo_1554_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_inferType_1555_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_getLevel_1556_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v_congrInfo_1557_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_defEqI_1558_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v_extensions_1559_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_issues_1560_);
lean_ctor_set(v_reuseFailAlloc_1631_, 9, v_canon_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1631_, sizeof(void*)*10, v_debug_1562_);
v___x_1568_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; uint8_t v_debug_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1569_ = lean_st_ref_set(v_a_1549_, v___x_1568_);
v___x_1570_ = lean_st_ref_get(v_a_1549_);
v_debug_1595_ = lean_ctor_get_uint8(v___x_1570_, sizeof(void*)*10);
lean_dec(v___x_1570_);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = l_Lean_Expr_looseBVarRange(v_e_1546_);
v___x_1598_ = lean_nat_dec_le(v___x_1597_, v___x_1596_);
lean_dec(v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v_n_1599_; lean_object* v_snd_1601_; lean_object* v___x_1607_; 
v_n_1599_ = lean_array_get_size(v_xs_1547_);
v___x_1607_ = l_Lean_Expr_getAppFn(v_e_1546_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_deBruijnIndex_1608_; uint8_t v___x_1609_; 
v_deBruijnIndex_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_deBruijnIndex_1608_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = lean_nat_dec_le(v___x_1596_, v_deBruijnIndex_1608_);
if (v___x_1609_ == 0)
{
lean_dec(v_deBruijnIndex_1608_);
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_share_1552_;
goto v___jp_1571_;
}
else
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_lt(v_deBruijnIndex_1608_, v_n_1599_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_fst_1613_; lean_object* v_snd_1614_; 
lean_dec_ref(v_e_1546_);
v___x_1611_ = lean_nat_sub(v_deBruijnIndex_1608_, v_n_1599_);
lean_dec(v_deBruijnIndex_1608_);
v___x_1612_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1611_, v_share_1552_);
v_fst_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_fst_1613_);
v_snd_1614_ = lean_ctor_get(v___x_1612_, 1);
lean_inc(v_snd_1614_);
lean_dec_ref(v___x_1612_);
v_fst_1572_ = v_fst_1613_;
v_snd_1573_ = v_snd_1614_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_i_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v_expectedNumArgs_1620_; lean_object* v_numArgs_1621_; uint8_t v___x_1622_; 
v___x_1615_ = lean_nat_sub(v_n_1599_, v_deBruijnIndex_1608_);
lean_dec(v_deBruijnIndex_1608_);
v___x_1616_ = lean_unsigned_to_nat(1u);
v_i_1617_ = lean_nat_sub(v___x_1615_, v___x_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1619_ = lean_array_get_borrowed(v___x_1618_, v_varDeps_1548_, v_i_1617_);
v_expectedNumArgs_1620_ = lean_array_get_size(v___x_1619_);
v_numArgs_1621_ = l_Lean_Expr_getAppNumArgs(v_e_1546_);
v___x_1622_ = lean_nat_dec_lt(v_expectedNumArgs_1620_, v_numArgs_1621_);
if (v___x_1622_ == 0)
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_eq(v_numArgs_1621_, v_expectedNumArgs_1620_);
lean_dec(v_numArgs_1621_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_fst_1626_; 
lean_dec(v_i_1617_);
v___x_1624_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1625_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1624_, v_debug_1595_, v_share_1552_);
v_fst_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_fst_1626_);
if (lean_obj_tag(v_fst_1626_) == 1)
{
lean_object* v_snd_1627_; lean_object* v_val_1628_; 
lean_dec_ref(v_e_1546_);
v_snd_1627_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_snd_1627_);
lean_dec_ref(v___x_1625_);
v_val_1628_ = lean_ctor_get(v_fst_1626_, 0);
lean_inc(v_val_1628_);
lean_dec_ref(v_fst_1626_);
v_fst_1572_ = v_val_1628_;
v_snd_1573_ = v_snd_1627_;
goto v___jp_1571_;
}
else
{
lean_object* v_snd_1629_; 
lean_dec(v_fst_1626_);
v_snd_1629_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1625_);
v_snd_1601_ = v_snd_1629_;
goto v___jp_1600_;
}
}
else
{
lean_object* v___x_1630_; 
lean_dec_ref(v_e_1546_);
v___x_1630_ = lean_array_fget_borrowed(v_xs_1547_, v_i_1617_);
lean_dec(v_i_1617_);
lean_inc(v___x_1630_);
v_fst_1572_ = v___x_1630_;
v_snd_1573_ = v_share_1552_;
goto v___jp_1571_;
}
}
else
{
lean_dec(v_numArgs_1621_);
lean_dec(v_i_1617_);
v_snd_1601_ = v_share_1552_;
goto v___jp_1600_;
}
}
}
}
else
{
lean_dec_ref(v___x_1607_);
v_snd_1601_ = v_share_1552_;
goto v___jp_1600_;
}
v___jp_1600_:
{
switch(lean_obj_tag(v_e_1546_))
{
case 9:
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_snd_1601_;
goto v___jp_1571_;
}
case 2:
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_snd_1601_;
goto v___jp_1571_;
}
case 0:
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_snd_1601_;
goto v___jp_1571_;
}
case 1:
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_snd_1601_;
goto v___jp_1571_;
}
case 4:
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_snd_1601_;
goto v___jp_1571_;
}
case 3:
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_snd_1601_;
goto v___jp_1571_;
}
default: 
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v_fst_1604_; lean_object* v_snd_1605_; lean_object* v_fst_1606_; 
v___x_1602_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2);
v___x_1603_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1599_, v_varDeps_1548_, v_xs_1547_, v_e_1546_, v___x_1596_, v___x_1602_, v_debug_1595_, v_snd_1601_);
v_fst_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_fst_1604_);
v_snd_1605_ = lean_ctor_get(v___x_1603_, 1);
lean_inc(v_snd_1605_);
lean_dec_ref(v___x_1603_);
v_fst_1606_ = lean_ctor_get(v_fst_1604_, 0);
lean_inc(v_fst_1606_);
lean_dec(v_fst_1604_);
v_fst_1572_ = v_fst_1606_;
v_snd_1573_ = v_snd_1605_;
goto v___jp_1571_;
}
}
}
}
else
{
v_fst_1572_ = v_e_1546_;
v_snd_1573_ = v_share_1552_;
goto v___jp_1571_;
}
v___jp_1571_:
{
lean_object* v___x_1574_; lean_object* v_maxFVar_1575_; lean_object* v_proofInstInfo_1576_; lean_object* v_inferType_1577_; lean_object* v_getLevel_1578_; lean_object* v_congrInfo_1579_; lean_object* v_defEqI_1580_; lean_object* v_extensions_1581_; lean_object* v_issues_1582_; lean_object* v_canon_1583_; uint8_t v_debug_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1593_; 
v___x_1574_ = lean_st_ref_take(v_a_1549_);
v_maxFVar_1575_ = lean_ctor_get(v___x_1574_, 1);
v_proofInstInfo_1576_ = lean_ctor_get(v___x_1574_, 2);
v_inferType_1577_ = lean_ctor_get(v___x_1574_, 3);
v_getLevel_1578_ = lean_ctor_get(v___x_1574_, 4);
v_congrInfo_1579_ = lean_ctor_get(v___x_1574_, 5);
v_defEqI_1580_ = lean_ctor_get(v___x_1574_, 6);
v_extensions_1581_ = lean_ctor_get(v___x_1574_, 7);
v_issues_1582_ = lean_ctor_get(v___x_1574_, 8);
v_canon_1583_ = lean_ctor_get(v___x_1574_, 9);
v_debug_1584_ = lean_ctor_get_uint8(v___x_1574_, sizeof(void*)*10);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v___x_1574_, 0);
lean_dec(v_unused_1594_);
v___x_1586_ = v___x_1574_;
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_canon_1583_);
lean_inc(v_issues_1582_);
lean_inc(v_extensions_1581_);
lean_inc(v_defEqI_1580_);
lean_inc(v_congrInfo_1579_);
lean_inc(v_getLevel_1578_);
lean_inc(v_inferType_1577_);
lean_inc(v_proofInstInfo_1576_);
lean_inc(v_maxFVar_1575_);
lean_dec(v___x_1574_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_snd_1573_);
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_snd_1573_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_maxFVar_1575_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_proofInstInfo_1576_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_inferType_1577_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_getLevel_1578_);
lean_ctor_set(v_reuseFailAlloc_1592_, 5, v_congrInfo_1579_);
lean_ctor_set(v_reuseFailAlloc_1592_, 6, v_defEqI_1580_);
lean_ctor_set(v_reuseFailAlloc_1592_, 7, v_extensions_1581_);
lean_ctor_set(v_reuseFailAlloc_1592_, 8, v_issues_1582_);
lean_ctor_set(v_reuseFailAlloc_1592_, 9, v_canon_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1592_, sizeof(void*)*10, v_debug_1584_);
v___x_1589_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_st_ref_set(v_a_1549_, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_fst_1572_);
return v___x_1591_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object* v_e_1633_, lean_object* v_xs_1634_, lean_object* v_varDeps_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1633_, v_xs_1634_, v_varDeps_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_varDeps_1635_);
lean_dec_ref(v_xs_1634_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1639_, lean_object* v_xs_1640_, lean_object* v_varDeps_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1639_, v_xs_1640_, v_varDeps_1641_, v_a_1643_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1650_, lean_object* v_xs_1651_, lean_object* v_varDeps_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1650_, v_xs_1651_, v_varDeps_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_varDeps_1652_);
lean_dec_ref(v_xs_1651_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1661_, lean_object* v_m_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1662_, v_a_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_m_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(v_00_u03b2_1665_, v_m_1666_, v_a_1667_);
lean_dec_ref(v_a_1667_);
lean_dec_ref(v_m_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_1669_, lean_object* v_a_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1673_, lean_object* v_a_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(v_00_u03b2_1673_, v_a_1674_, v_x_1675_);
lean_dec(v_x_1675_);
lean_dec_ref(v_a_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1677_, lean_object* v_type_1678_, lean_object* v_val_1679_, lean_object* v_k_1680_, uint8_t v_nondep_1681_, uint8_t v_kind_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; 
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1690_, 0, v_k_1680_);
lean_closure_set(v___f_1690_, 1, v___y_1683_);
lean_closure_set(v___f_1690_, 2, v___y_1684_);
v___x_1691_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1677_, v_type_1678_, v_val_1679_, v___f_1690_, v_nondep_1681_, v_kind_1682_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1691_) == 0)
{
return v___x_1691_;
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1700_, lean_object* v_type_1701_, lean_object* v_val_1702_, lean_object* v_k_1703_, lean_object* v_nondep_1704_, lean_object* v_kind_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v_nondep_boxed_1713_; uint8_t v_kind_boxed_1714_; lean_object* v_res_1715_; 
v_nondep_boxed_1713_ = lean_unbox(v_nondep_1704_);
v_kind_boxed_1714_ = lean_unbox(v_kind_1705_);
v_res_1715_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1700_, v_type_1701_, v_val_1702_, v_k_1703_, v_nondep_boxed_1713_, v_kind_boxed_1714_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1716_, lean_object* v_name_1717_, lean_object* v_type_1718_, lean_object* v_val_1719_, lean_object* v_k_1720_, uint8_t v_nondep_1721_, uint8_t v_kind_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1717_, v_type_1718_, v_val_1719_, v_k_1720_, v_nondep_1721_, v_kind_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_1731_, lean_object* v_name_1732_, lean_object* v_type_1733_, lean_object* v_val_1734_, lean_object* v_k_1735_, lean_object* v_nondep_1736_, lean_object* v_kind_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_nondep_boxed_1745_; uint8_t v_kind_boxed_1746_; lean_object* v_res_1747_; 
v_nondep_boxed_1745_ = lean_unbox(v_nondep_1736_);
v_kind_boxed_1746_ = lean_unbox(v_kind_1737_);
v_res_1747_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_1731_, v_name_1732_, v_type_1733_, v_val_1734_, v_k_1735_, v_nondep_boxed_1745_, v_kind_boxed_1746_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1747_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object* v_msg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_2402__overap_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0);
v___x_2402__overap_1758_ = lean_panic_fn_borrowed(v___x_1757_, v_msg_1749_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1752_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
v___x_1759_ = lean_apply_7(v___x_2402__overap_1758_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, lean_box(0));
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_1769_, size_t v_sz_1770_, size_t v_i_1771_, lean_object* v_bs_1772_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_usize_dec_lt(v_i_1771_, v_sz_1770_);
if (v___x_1773_ == 0)
{
return v_bs_1772_;
}
else
{
lean_object* v_v_1774_; lean_object* v___x_1775_; lean_object* v_bs_x27_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v_v_1774_ = lean_array_uget(v_bs_1772_, v_i_1771_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v_bs_x27_1776_ = lean_array_uset(v_bs_1772_, v_i_1771_, v___x_1775_);
v___x_1777_ = l_Lean_instInhabitedExpr;
v___x_1778_ = lean_array_get_borrowed(v___x_1777_, v_xs_1769_, v_v_1774_);
lean_dec(v_v_1774_);
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1771_, v___x_1779_);
lean_inc(v___x_1778_);
v___x_1781_ = lean_array_uset(v_bs_x27_1776_, v_i_1771_, v___x_1778_);
v_i_1771_ = v___x_1780_;
v_bs_1772_ = v___x_1781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_1783_, lean_object* v_sz_1784_, lean_object* v_i_1785_, lean_object* v_bs_1786_){
_start:
{
size_t v_sz_boxed_1787_; size_t v_i_boxed_1788_; lean_object* v_res_1789_; 
v_sz_boxed_1787_ = lean_unbox_usize(v_sz_1784_);
lean_dec(v_sz_1784_);
v_i_boxed_1788_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1783_, v_sz_boxed_1787_, v_i_boxed_1788_, v_bs_1786_);
lean_dec_ref(v_xs_1783_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_1790_, lean_object* v_i_1791_, lean_object* v_varDeps_1792_, lean_object* v_args_1793_, lean_object* v_body_1794_, lean_object* v_x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_1790_, v_i_1791_, v_varDeps_1792_, v_args_1793_, v_body_1794_, v_x_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v_i_1791_);
return v_res_1803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1806_ = lean_unsigned_to_nat(30u);
v___x_1807_ = lean_unsigned_to_nat(254u);
v___x_1808_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_1809_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1810_ = l_mkPanicMessageWithDecl(v___x_1809_, v___x_1808_, v___x_1807_, v___x_1806_, v___x_1805_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_1811_, lean_object* v_args_1812_, lean_object* v_f_1813_, lean_object* v_xs_1814_, lean_object* v_i_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_array_get_size(v_args_1812_);
v___x_1824_ = lean_nat_dec_lt(v_i_1815_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v_a_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_i_1815_);
lean_dec_ref(v_args_1812_);
v___x_1825_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_f_1813_, v_xs_1814_, v_varDeps_1811_, v_a_1817_);
lean_dec_ref(v_varDeps_1811_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = 1;
v___x_1828_ = l_Lean_Meta_mkLetFVars(v_xs_1814_, v_a_1826_, v___x_1824_, v___x_1824_, v___x_1827_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec_ref(v_xs_1814_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_1829_, v_a_1817_);
return v___x_1830_;
}
else
{
return v___x_1828_;
}
}
else
{
if (lean_obj_tag(v_f_1813_) == 6)
{
lean_object* v_binderName_1831_; lean_object* v_binderType_1832_; lean_object* v_body_1833_; lean_object* v_varPos_1834_; size_t v_sz_1835_; size_t v___x_1836_; lean_object* v_ys_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_binderName_1831_ = lean_ctor_get(v_f_1813_, 0);
lean_inc(v_binderName_1831_);
v_binderType_1832_ = lean_ctor_get(v_f_1813_, 1);
lean_inc_ref(v_binderType_1832_);
v_body_1833_ = lean_ctor_get(v_f_1813_, 2);
lean_inc_ref(v_body_1833_);
lean_dec_ref(v_f_1813_);
v_varPos_1834_ = lean_array_fget(v_varDeps_1811_, v_i_1815_);
v_sz_1835_ = lean_array_size(v_varPos_1834_);
v___x_1836_ = ((size_t)0ULL);
lean_inc(v_varPos_1834_);
v_ys_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1814_, v_sz_1835_, v___x_1836_, v_varPos_1834_);
v___x_1838_ = lean_array_fget_borrowed(v_args_1812_, v_i_1815_);
v___x_1839_ = 0;
lean_inc(v___x_1838_);
v___x_1840_ = l_Lean_Expr_betaRev(v___x_1838_, v_ys_1837_, v___x_1839_, v___x_1839_);
lean_dec_ref(v_ys_1837_);
v___x_1841_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1840_, v_a_1817_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v_type_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1843_, 0, v_xs_1814_);
lean_closure_set(v___f_1843_, 1, v_i_1815_);
lean_closure_set(v___f_1843_, 2, v_varDeps_1811_);
lean_closure_set(v___f_1843_, 3, v_args_1812_);
lean_closure_set(v___f_1843_, 4, v_body_1833_);
v___x_1844_ = lean_array_get_size(v_varPos_1834_);
lean_dec(v_varPos_1834_);
v_type_1845_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_1832_, v___x_1844_);
v___x_1846_ = 0;
v___x_1847_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_1831_, v_type_1845_, v_a_1842_, v___f_1843_, v___x_1824_, v___x_1846_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1847_;
}
else
{
lean_dec(v_varPos_1834_);
lean_dec_ref(v_body_1833_);
lean_dec_ref(v_binderType_1832_);
lean_dec(v_binderName_1831_);
lean_dec(v_i_1815_);
lean_dec_ref(v_xs_1814_);
lean_dec_ref(v_args_1812_);
lean_dec_ref(v_varDeps_1811_);
return v___x_1841_;
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v_i_1815_);
lean_dec_ref(v_xs_1814_);
lean_dec_ref(v_f_1813_);
lean_dec_ref(v_args_1812_);
lean_dec_ref(v_varDeps_1811_);
v___x_1848_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_1849_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1848_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_1850_, lean_object* v_i_1851_, lean_object* v_varDeps_1852_, lean_object* v_args_1853_, lean_object* v_body_1854_, lean_object* v_x_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_x_1855_, v___y_1857_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = lean_array_push(v_xs_1850_, v_a_1864_);
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_i_1851_, v___x_1866_);
v___x_1868_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1852_, v_args_1853_, v_body_1854_, v___x_1865_, v___x_1867_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1868_;
}
else
{
lean_dec_ref(v_body_1854_);
lean_dec_ref(v_args_1853_);
lean_dec_ref(v_varDeps_1852_);
lean_dec_ref(v_xs_1850_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_1869_, lean_object* v_args_1870_, lean_object* v_f_1871_, lean_object* v_xs_1872_, lean_object* v_i_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1869_, v_args_1870_, v_f_1871_, v_xs_1872_, v_i_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_1882_, lean_object* v_args_1883_, lean_object* v___h_1884_, lean_object* v_f_1885_, lean_object* v_xs_1886_, lean_object* v_i_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1882_, v_args_1883_, v_f_1885_, v_xs_1886_, v_i_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_1896_, lean_object* v_args_1897_, lean_object* v___h_1898_, lean_object* v_f_1899_, lean_object* v_xs_1900_, lean_object* v_i_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_1896_, v_args_1897_, v___h_1898_, v_f_1899_, v_xs_1900_, v_i_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
return v_res_1909_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1912_ = lean_unsigned_to_nat(40u);
v___x_1913_ = lean_unsigned_to_nat(251u);
v___x_1914_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1916_ = l_mkPanicMessageWithDecl(v___x_1915_, v___x_1914_, v___x_1913_, v___x_1912_, v___x_1911_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
if (lean_obj_tag(v_x_1918_) == 5)
{
lean_object* v_fn_1928_; lean_object* v_arg_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_fn_1928_ = lean_ctor_get(v_x_1918_, 0);
lean_inc_ref(v_fn_1928_);
v_arg_1929_ = lean_ctor_get(v_x_1918_, 1);
lean_inc_ref(v_arg_1929_);
lean_dec_ref(v_x_1918_);
v___x_1930_ = lean_array_set(v_x_1919_, v_x_1920_, v_arg_1929_);
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_sub(v_x_1920_, v___x_1931_);
lean_dec(v_x_1920_);
v_x_1918_ = v_fn_1928_;
v_x_1919_ = v___x_1930_;
v_x_1920_ = v___x_1932_;
goto _start;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
lean_dec(v_x_1920_);
v___x_1934_ = lean_array_get_size(v_x_1919_);
v___x_1935_ = lean_array_get_size(v_varDeps_1917_);
v___x_1936_ = lean_nat_dec_eq(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec_ref(v_x_1919_);
lean_dec_ref(v_x_1918_);
lean_dec_ref(v_varDeps_1917_);
v___x_1937_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_1938_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1937_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_1941_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1917_, v_x_1919_, v_x_1918_, v___x_1940_, v___x_1939_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_1942_, v_x_1943_, v_x_1944_, v_x_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1953_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_1954_; lean_object* v_dummy_1955_; 
v___x_1954_ = lean_box(0);
v_dummy_1955_ = l_Lean_Expr_sort___override(v___x_1954_);
return v_dummy_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_1956_, lean_object* v_varDeps_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_dummy_1965_; lean_object* v_nargs_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_dummy_1965_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_1966_ = l_Lean_Expr_getAppNumArgs(v_e_1956_);
lean_inc(v_nargs_1966_);
v___x_1967_ = lean_mk_array(v_nargs_1966_, v_dummy_1965_);
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_nat_sub(v_nargs_1966_, v___x_1968_);
lean_dec(v_nargs_1966_);
v___x_1970_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_1957_, v_e_1956_, v___x_1967_, v___x_1969_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_1971_, lean_object* v_varDeps_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_1971_, v_varDeps_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_1981_, lean_object* v_b_1982_){
_start:
{
lean_object* v_snd_1984_; lean_object* v_fst_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2018_; 
v_snd_1984_ = lean_ctor_get(v_b_1982_, 1);
v_fst_1985_ = lean_ctor_get(v_b_1982_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_b_1982_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1987_ = v_b_1982_;
v_isShared_1988_ = v_isSharedCheck_2018_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snd_1984_);
lean_inc(v_fst_1985_);
lean_dec(v_b_1982_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2018_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2017_; 
v_fst_1989_ = lean_ctor_get(v_snd_1984_, 0);
v_snd_1990_ = lean_ctor_get(v_snd_1984_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_snd_1984_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1992_ = v_snd_1984_;
v_isShared_1993_ = v_isSharedCheck_2017_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_snd_1990_);
lean_inc(v_fst_1989_);
lean_dec(v_snd_1984_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2017_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_nat_dec_lt(v___x_1994_, v_fst_1989_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1997_; 
if (v_isShared_1993_ == 0)
{
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_fst_1989_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_snd_1990_);
v___x_1997_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_1997_);
v___x_1999_ = v___x_1987_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_fst_1985_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_sub(v_fst_1989_, v___x_2003_);
lean_dec(v_fst_1989_);
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_array_get_borrowed(v___x_2005_, v_argUnivs_1981_, v___x_2004_);
lean_inc(v___x_2006_);
v___x_2007_ = l_Lean_mkLevelIMax_x27(v___x_2006_, v_fst_1985_);
v___x_2008_ = l_Lean_Level_normalize(v___x_2007_);
lean_dec(v___x_2007_);
lean_inc(v___x_2008_);
v___x_2009_ = lean_array_push(v_snd_1990_, v___x_2008_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v___x_2009_);
lean_ctor_set(v___x_1992_, 0, v___x_2004_);
v___x_2011_ = v___x_1992_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_2011_);
lean_ctor_set(v___x_1987_, 0, v___x_2008_);
v___x_2013_ = v___x_1987_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
v_b_1982_ = v___x_2013_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2019_, v_b_2020_);
lean_dec_ref(v_argUnivs_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2025_, lean_object* v_argUnivs_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
if (lean_obj_tag(v_type_2025_) == 7)
{
lean_object* v_binderType_2034_; lean_object* v_body_2035_; lean_object* v___x_2036_; 
v_binderType_2034_ = lean_ctor_get(v_type_2025_, 1);
lean_inc_ref(v_binderType_2034_);
v_body_2035_ = lean_ctor_get(v_type_2025_, 2);
lean_inc_ref(v_body_2035_);
lean_dec_ref(v_type_2025_);
v___x_2036_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2034_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2036_);
v___x_2038_ = lean_array_push(v_argUnivs_2026_, v_a_2037_);
v_type_2025_ = v_body_2035_;
v_argUnivs_2026_ = v___x_2038_;
goto _start;
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_body_2035_);
lean_dec_ref(v_argUnivs_2026_);
v_a_2040_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2036_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2036_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2025_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_array_get_size(v_argUnivs_2026_);
v___x_2051_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_a_2049_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2026_, v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2073_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2073_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2073_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_snd_2059_; lean_object* v_snd_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2071_; 
v_snd_2059_ = lean_ctor_get(v_a_2055_, 1);
lean_inc(v_snd_2059_);
lean_dec(v_a_2055_);
v_snd_2060_ = lean_ctor_get(v_snd_2059_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_snd_2059_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_snd_2059_, 0);
lean_dec(v_unused_2072_);
v___x_2062_ = v_snd_2059_;
v_isShared_2063_ = v_isSharedCheck_2071_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_snd_2060_);
lean_dec(v_snd_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2071_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = l_Array_reverse___redArg(v_snd_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2064_);
lean_ctor_set(v___x_2062_, 0, v_argUnivs_2026_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_argUnivs_2026_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2066_);
v___x_2068_ = v___x_2057_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v_argUnivs_2026_);
v_a_2074_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2054_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2054_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_argUnivs_2026_);
v_a_2082_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2048_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2048_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2090_, lean_object* v_argUnivs_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2090_, v_argUnivs_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2100_, lean_object* v_b_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2100_, v_b_2101_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2110_, v_b_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_argUnivs_2110_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2129_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2120_, v___x_2128_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2139_, lean_object* v_argUnivs_2140_, lean_object* v_declName_2141_, lean_object* v_fType_2142_, lean_object* v_i_2143_){
_start:
{
lean_object* v___x_2145_; lean_object* v_00_u03b1_2146_; lean_object* v_00_u03b2_2147_; lean_object* v_u_2148_; lean_object* v_v_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2145_ = lean_box(0);
v_00_u03b1_2146_ = l_Lean_Expr_bindingDomain_x21(v_fType_2142_);
v_00_u03b2_2147_ = l_Lean_Expr_bindingBody_x21(v_fType_2142_);
v_u_2148_ = lean_array_get_borrowed(v___x_2145_, v_argUnivs_2140_, v_i_2143_);
v_v_2149_ = lean_array_get_borrowed(v___x_2145_, v_fnUnivs_2139_, v_i_2143_);
v___x_2150_ = lean_box(0);
lean_inc(v_v_2149_);
v___x_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_v_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
lean_inc(v_u_2148_);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_u_2148_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_mkConst(v_declName_2141_, v___x_2152_);
v___x_2154_ = l_Lean_mkAppB(v___x_2153_, v_00_u03b1_2146_, v_00_u03b2_2147_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2156_, lean_object* v_argUnivs_2157_, lean_object* v_declName_2158_, lean_object* v_fType_2159_, lean_object* v_i_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2156_, v_argUnivs_2157_, v_declName_2158_, v_fType_2159_, v_i_2160_);
lean_dec(v_i_2160_);
lean_dec_ref(v_fType_2159_);
lean_dec_ref(v_argUnivs_2157_);
lean_dec_ref(v_fnUnivs_2156_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2163_, lean_object* v_argUnivs_2164_, lean_object* v_declName_2165_, lean_object* v_fType_2166_, lean_object* v_i_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2163_, v_argUnivs_2164_, v_declName_2165_, v_fType_2166_, v_i_2167_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2176_, lean_object* v_argUnivs_2177_, lean_object* v_declName_2178_, lean_object* v_fType_2179_, lean_object* v_i_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2176_, v_argUnivs_2177_, v_declName_2178_, v_fType_2179_, v_i_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_i_2180_);
lean_dec_ref(v_fType_2179_);
lean_dec_ref(v_argUnivs_2177_);
lean_dec_ref(v_fnUnivs_2176_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2189_, lean_object* v_a_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___y_2199_; lean_object* v___x_2202_; uint8_t v_debug_2203_; 
v___x_2202_ = lean_st_ref_get(v___y_2192_);
v_debug_2203_ = lean_ctor_get_uint8(v___x_2202_, sizeof(void*)*10);
lean_dec(v___x_2202_);
if (v_debug_2203_ == 0)
{
v___y_2199_ = v___y_2192_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2204_; 
lean_inc_ref(v_f_2189_);
v___x_2204_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2189_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2205_; 
lean_dec_ref(v___x_2204_);
lean_inc_ref(v_a_2190_);
v___x_2205_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref(v___x_2205_);
v___y_2199_ = v___y_2192_;
goto v___jp_2198_;
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_f_2189_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_f_2189_);
v_a_2214_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2204_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2204_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
v___jp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = l_Lean_Expr_app___override(v_f_2189_, v_a_2190_);
v___x_2201_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2200_, v___y_2199_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2222_, lean_object* v_a_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2222_, v_a_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2232_, lean_object* v_a_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2232_, v_a_2233_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2245_, lean_object* v_a_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2245_, v_a_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
return v_res_2257_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_15370__overap_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15370__overap_2271_ = lean_panic_fn_borrowed(v___x_2270_, v_msg_2259_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc(v___y_2260_);
v___x_2272_ = lean_apply_10(v___x_15370__overap_2271_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, lean_box(0));
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
return v_res_2284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_2296_ = lean_unsigned_to_nat(11u);
v___x_2297_ = lean_unsigned_to_nat(346u);
v___x_2298_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2299_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_2300_ = l_mkPanicMessageWithDecl(v___x_2299_, v___x_2298_, v___x_2297_, v___x_2296_, v___x_2295_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2301_, lean_object* v_fnUnivs_2302_, lean_object* v_argUnivs_2303_, lean_object* v_simpBody_2304_, lean_object* v_e_2305_, lean_object* v_i_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
switch(lean_obj_tag(v_e_2305_))
{
case 5:
{
lean_object* v_fn_2317_; lean_object* v_arg_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_fn_2317_ = lean_ctor_get(v_e_2305_, 0);
lean_inc_ref_n(v_fn_2317_, 2);
v_arg_2318_ = lean_ctor_get(v_e_2305_, 1);
lean_inc_ref(v_arg_2318_);
lean_dec_ref(v_e_2305_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = lean_nat_sub(v_i_2306_, v___x_2319_);
v___x_2321_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2301_, v_fnUnivs_2302_, v_argUnivs_2303_, v_simpBody_2304_, v_fn_2317_, v___x_2320_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
lean_dec(v___x_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2442_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2442_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2442_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_fst_2326_; lean_object* v_snd_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2441_; 
v_fst_2326_ = lean_ctor_get(v_a_2322_, 0);
v_snd_2327_ = lean_ctor_get(v_a_2322_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_a_2322_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2329_ = v_a_2322_;
v_isShared_2330_ = v_isSharedCheck_2441_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_snd_2327_);
lean_inc(v_fst_2326_);
lean_dec(v_a_2322_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2441_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_r_2332_; lean_object* v___x_2340_; 
lean_inc(v_a_2315_);
lean_inc_ref(v_a_2314_);
lean_inc(v_a_2313_);
lean_inc_ref(v_a_2312_);
lean_inc(v_a_2311_);
lean_inc_ref(v_a_2310_);
lean_inc(v_a_2309_);
lean_inc_ref(v_a_2308_);
lean_inc(v_a_2307_);
lean_inc_ref(v_arg_2318_);
v___x_2340_ = lean_sym_simp(v_arg_2318_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; uint8_t v___y_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2340_);
if (lean_obj_tag(v_fst_2326_) == 0)
{
if (lean_obj_tag(v_a_2341_) == 0)
{
uint8_t v_contextDependent_2345_; 
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
v_contextDependent_2345_ = lean_ctor_get_uint8(v_fst_2326_, 1);
lean_dec_ref(v_fst_2326_);
if (v_contextDependent_2345_ == 0)
{
uint8_t v_contextDependent_2346_; 
v_contextDependent_2346_ = lean_ctor_get_uint8(v_a_2341_, 1);
lean_dec_ref(v_a_2341_);
v___y_2343_ = v_contextDependent_2346_;
goto v___jp_2342_;
}
else
{
lean_dec_ref(v_a_2341_);
v___y_2343_ = v_contextDependent_2345_;
goto v___jp_2342_;
}
}
else
{
uint8_t v_contextDependent_2347_; lean_object* v_e_x27_2348_; lean_object* v_proof_2349_; uint8_t v_contextDependent_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2374_; 
v_contextDependent_2347_ = lean_ctor_get_uint8(v_fst_2326_, 1);
lean_dec_ref(v_fst_2326_);
v_e_x27_2348_ = lean_ctor_get(v_a_2341_, 0);
v_proof_2349_ = lean_ctor_get(v_a_2341_, 1);
v_contextDependent_2350_ = lean_ctor_get_uint8(v_a_2341_, sizeof(void*)*2 + 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2352_ = v_a_2341_;
v_isShared_2353_ = v_isSharedCheck_2374_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_proof_2349_);
lean_inc(v_e_x27_2348_);
lean_dec(v_a_2341_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2374_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; 
lean_inc_ref(v_e_x27_2348_);
lean_inc_ref(v_fn_2317_);
v___x_2354_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2317_, v_e_x27_2348_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v_a_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; uint8_t v___y_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2357_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2302_, v_argUnivs_2303_, v___x_2356_, v_snd_2327_, v_i_2306_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = l_Lean_mkApp4(v_a_2358_, v_arg_2318_, v_e_x27_2348_, v_fn_2317_, v_proof_2349_);
v___x_2360_ = 0;
if (v_contextDependent_2347_ == 0)
{
v___y_2362_ = v_contextDependent_2350_;
goto v___jp_2361_;
}
else
{
v___y_2362_ = v_contextDependent_2347_;
goto v___jp_2361_;
}
v___jp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v___x_2359_);
lean_ctor_set(v___x_2352_, 0, v_a_2355_);
v___x_2364_ = v___x_2352_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2355_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v___x_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2, v___x_2360_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2 + 1, v___y_2362_);
v_r_2332_ = v___x_2364_;
goto v___jp_2331_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_del_object(v___x_2352_);
lean_dec_ref(v_proof_2349_);
lean_dec_ref(v_e_x27_2348_);
lean_del_object(v___x_2329_);
lean_dec(v_snd_2327_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
v_a_2366_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2354_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2354_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2341_) == 0)
{
lean_object* v_e_x27_2375_; lean_object* v_proof_2376_; uint8_t v_contextDependent_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2402_; 
v_e_x27_2375_ = lean_ctor_get(v_fst_2326_, 0);
v_proof_2376_ = lean_ctor_get(v_fst_2326_, 1);
v_contextDependent_2377_ = lean_ctor_get_uint8(v_fst_2326_, sizeof(void*)*2 + 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_fst_2326_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2379_ = v_fst_2326_;
v_isShared_2380_ = v_isSharedCheck_2402_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_proof_2376_);
lean_inc(v_e_x27_2375_);
lean_dec(v_fst_2326_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2402_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
uint8_t v_contextDependent_2381_; lean_object* v___x_2382_; 
v_contextDependent_2381_ = lean_ctor_get_uint8(v_a_2341_, 1);
lean_dec_ref(v_a_2341_);
lean_inc_ref(v_arg_2318_);
lean_inc_ref(v_e_x27_2375_);
v___x_2382_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2375_, v_arg_2318_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_a_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; uint8_t v___y_2390_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2385_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2302_, v_argUnivs_2303_, v___x_2384_, v_snd_2327_, v_i_2306_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = l_Lean_mkApp4(v_a_2386_, v_fn_2317_, v_e_x27_2375_, v_proof_2376_, v_arg_2318_);
v___x_2388_ = 0;
if (v_contextDependent_2377_ == 0)
{
v___y_2390_ = v_contextDependent_2381_;
goto v___jp_2389_;
}
else
{
v___y_2390_ = v_contextDependent_2377_;
goto v___jp_2389_;
}
v___jp_2389_:
{
lean_object* v___x_2392_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v___x_2387_);
lean_ctor_set(v___x_2379_, 0, v_a_2383_);
v___x_2392_ = v___x_2379_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2383_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*2, v___x_2388_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*2 + 1, v___y_2390_);
v_r_2332_ = v___x_2392_;
goto v___jp_2331_;
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_del_object(v___x_2379_);
lean_dec_ref(v_proof_2376_);
lean_dec_ref(v_e_x27_2375_);
lean_del_object(v___x_2329_);
lean_dec(v_snd_2327_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
v_a_2394_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2382_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2382_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2403_; lean_object* v_proof_2404_; uint8_t v_contextDependent_2405_; lean_object* v_e_x27_2406_; lean_object* v_proof_2407_; uint8_t v_contextDependent_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2432_; 
v_e_x27_2403_ = lean_ctor_get(v_fst_2326_, 0);
lean_inc_ref(v_e_x27_2403_);
v_proof_2404_ = lean_ctor_get(v_fst_2326_, 1);
lean_inc_ref(v_proof_2404_);
v_contextDependent_2405_ = lean_ctor_get_uint8(v_fst_2326_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_2326_);
v_e_x27_2406_ = lean_ctor_get(v_a_2341_, 0);
v_proof_2407_ = lean_ctor_get(v_a_2341_, 1);
v_contextDependent_2408_ = lean_ctor_get_uint8(v_a_2341_, sizeof(void*)*2 + 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2410_ = v_a_2341_;
v_isShared_2411_ = v_isSharedCheck_2432_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_proof_2407_);
lean_inc(v_e_x27_2406_);
lean_dec(v_a_2341_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2432_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; 
lean_inc_ref(v_e_x27_2406_);
lean_inc_ref(v_e_x27_2403_);
v___x_2412_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2403_, v_e_x27_2406_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; uint8_t v___y_2420_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2415_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2302_, v_argUnivs_2303_, v___x_2414_, v_snd_2327_, v_i_2306_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref(v___x_2415_);
v___x_2417_ = l_Lean_mkApp6(v_a_2416_, v_fn_2317_, v_e_x27_2403_, v_arg_2318_, v_e_x27_2406_, v_proof_2404_, v_proof_2407_);
v___x_2418_ = 0;
if (v_contextDependent_2405_ == 0)
{
v___y_2420_ = v_contextDependent_2408_;
goto v___jp_2419_;
}
else
{
v___y_2420_ = v_contextDependent_2405_;
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2422_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v___x_2417_);
lean_ctor_set(v___x_2410_, 0, v_a_2413_);
v___x_2422_ = v___x_2410_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2413_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*2, v___x_2418_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*2 + 1, v___y_2420_);
v_r_2332_ = v___x_2422_;
goto v___jp_2331_;
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_del_object(v___x_2410_);
lean_dec_ref(v_proof_2407_);
lean_dec_ref(v_e_x27_2406_);
lean_dec_ref(v_proof_2404_);
lean_dec_ref(v_e_x27_2403_);
lean_del_object(v___x_2329_);
lean_dec(v_snd_2327_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
v_a_2424_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2412_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2412_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
v___jp_2342_:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2343_);
v_r_2332_ = v___x_2344_;
goto v___jp_2331_;
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_del_object(v___x_2329_);
lean_dec(v_snd_2327_);
lean_dec(v_fst_2326_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
v_a_2433_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2340_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2340_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
v___jp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = l_Lean_Expr_bindingBody_x21(v_snd_2327_);
lean_dec(v_snd_2327_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v___x_2333_);
lean_ctor_set(v___x_2329_, 0, v_r_2332_);
v___x_2335_ = v___x_2329_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_r_2332_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2335_);
v___x_2337_ = v___x_2324_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2318_);
lean_dec_ref(v_fn_2317_);
return v___x_2321_;
}
}
case 6:
{
lean_object* v___x_2443_; 
lean_inc(v_a_2315_);
lean_inc_ref(v_a_2314_);
lean_inc(v_a_2313_);
lean_inc_ref(v_a_2312_);
lean_inc(v_a_2311_);
lean_inc_ref(v_a_2310_);
lean_inc(v_a_2309_);
lean_inc_ref(v_a_2308_);
lean_inc(v_a_2307_);
v___x_2443_ = lean_apply_11(v_simpBody_2304_, v_e_2305_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, lean_box(0));
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2452_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2444_);
lean_ctor_set(v___x_2448_, 1, v_fType_2301_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2448_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v_fType_2301_);
v_a_2453_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2443_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2443_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
default: 
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref(v_e_2305_);
lean_dec_ref(v_simpBody_2304_);
lean_dec_ref(v_fType_2301_);
v___x_2461_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2462_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2461_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2463_, lean_object* v_fnUnivs_2464_, lean_object* v_argUnivs_2465_, lean_object* v_simpBody_2466_, lean_object* v_e_2467_, lean_object* v_i_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2463_, v_fnUnivs_2464_, v_argUnivs_2465_, v_simpBody_2466_, v_e_2467_, v_i_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec(v_i_2468_);
lean_dec_ref(v_argUnivs_2465_);
lean_dec_ref(v_fnUnivs_2464_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2480_, lean_object* v_fType_2481_, lean_object* v_fnUnivs_2482_, lean_object* v_argUnivs_2483_, lean_object* v_simpBody_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_numArgs_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_numArgs_2495_ = lean_array_get_size(v_argUnivs_2483_);
v___x_2496_ = lean_unsigned_to_nat(1u);
v___x_2497_ = lean_nat_sub(v_numArgs_2495_, v___x_2496_);
v___x_2498_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2481_, v_fnUnivs_2482_, v_argUnivs_2483_, v_simpBody_2484_, v_e_2480_, v___x_2497_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v___x_2497_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2507_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2507_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2507_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_fst_2503_; lean_object* v___x_2505_; 
v_fst_2503_ = lean_ctor_get(v_a_2499_, 0);
lean_inc(v_fst_2503_);
lean_dec(v_a_2499_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v_fst_2503_);
v___x_2505_ = v___x_2501_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_fst_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2498_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2498_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2516_, lean_object* v_fType_2517_, lean_object* v_fnUnivs_2518_, lean_object* v_argUnivs_2519_, lean_object* v_simpBody_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2516_, v_fType_2517_, v_fnUnivs_2518_, v_argUnivs_2519_, v_simpBody_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_argUnivs_2519_);
lean_dec_ref(v_fnUnivs_2518_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2536_, lean_object* v_simpBody_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; 
lean_inc_ref(v_e_2536_);
v___x_2548_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2536_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v_00_u03b1_2550_; lean_object* v_u_2551_; lean_object* v_e_2552_; lean_object* v_h_2553_; lean_object* v_varDeps_2554_; lean_object* v_fType_2555_; lean_object* v___x_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v_00_u03b1_2550_ = lean_ctor_get(v_a_2549_, 0);
lean_inc_ref(v_00_u03b1_2550_);
v_u_2551_ = lean_ctor_get(v_a_2549_, 1);
lean_inc(v_u_2551_);
v_e_2552_ = lean_ctor_get(v_a_2549_, 2);
lean_inc_ref(v_e_2552_);
v_h_2553_ = lean_ctor_get(v_a_2549_, 3);
lean_inc_ref(v_h_2553_);
v_varDeps_2554_ = lean_ctor_get(v_a_2549_, 4);
lean_inc_ref(v_varDeps_2554_);
v_fType_2555_ = lean_ctor_get(v_a_2549_, 5);
lean_inc_ref_n(v_fType_2555_, 2);
lean_dec(v_a_2549_);
v___x_2556_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2555_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v_argUnivs_2558_; lean_object* v_fnUnivs_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2627_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2556_);
v_argUnivs_2558_ = lean_ctor_get(v_a_2557_, 0);
v_fnUnivs_2559_ = lean_ctor_get(v_a_2557_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_a_2557_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2561_ = v_a_2557_;
v_isShared_2562_ = v_isSharedCheck_2627_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_fnUnivs_2559_);
lean_inc(v_argUnivs_2558_);
lean_dec(v_a_2557_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2627_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; 
lean_inc_ref(v_e_2552_);
v___x_2563_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2552_, v_fType_2555_, v_fnUnivs_2559_, v_argUnivs_2558_, v_simpBody_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec_ref(v_argUnivs_2558_);
lean_dec_ref(v_fnUnivs_2559_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2618_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2618_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2618_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
if (lean_obj_tag(v_a_2564_) == 0)
{
uint8_t v_contextDependent_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_del_object(v___x_2561_);
lean_dec_ref(v_varDeps_2554_);
lean_dec_ref(v_h_2553_);
lean_dec_ref(v_e_2552_);
lean_dec_ref(v_e_2536_);
v_contextDependent_2568_ = lean_ctor_get_uint8(v_a_2564_, 1);
lean_dec_ref(v_a_2564_);
v___x_2569_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2568_);
v___x_2570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v_00_u03b1_2550_);
lean_ctor_set(v___x_2570_, 2, v_u_2551_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2570_);
v___x_2572_ = v___x_2566_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
else
{
lean_object* v_e_x27_2574_; lean_object* v_proof_2575_; uint8_t v_contextDependent_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2617_; 
lean_del_object(v___x_2566_);
v_e_x27_2574_ = lean_ctor_get(v_a_2564_, 0);
v_proof_2575_ = lean_ctor_get(v_a_2564_, 1);
v_contextDependent_2576_ = lean_ctor_get_uint8(v_a_2564_, sizeof(void*)*2 + 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2564_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2578_ = v_a_2564_;
v_isShared_2579_ = v_isSharedCheck_2617_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_proof_2575_);
lean_inc(v_e_x27_2574_);
lean_dec(v_a_2564_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2617_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2580_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2581_ = lean_box(0);
lean_inc(v_u_2551_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 1);
lean_ctor_set(v___x_2561_, 1, v___x_2581_);
lean_ctor_set(v___x_2561_, 0, v_u_2551_);
v___x_2583_ = v___x_2561_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_u_2551_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_inc_ref(v___x_2583_);
v___x_2584_ = l_Lean_mkConst(v___x_2580_, v___x_2583_);
lean_inc_ref_n(v_e_x27_2574_, 2);
lean_inc_ref(v_e_2536_);
lean_inc_ref(v_00_u03b1_2550_);
lean_inc_ref(v___x_2584_);
v___x_2585_ = l_Lean_mkApp6(v___x_2584_, v_00_u03b1_2550_, v_e_2536_, v_e_2552_, v_e_x27_2574_, v_h_2553_, v_proof_2575_);
v___x_2586_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2574_, v_varDeps_2554_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2607_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2607_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2607_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; lean_object* v___x_2601_; 
v___x_2591_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2583_);
v___x_2592_ = l_Lean_mkConst(v___x_2591_, v___x_2583_);
lean_inc_n(v_a_2587_, 2);
lean_inc_ref_n(v_e_x27_2574_, 2);
lean_inc_ref_n(v_00_u03b1_2550_, 3);
v___x_2593_ = l_Lean_mkApp3(v___x_2592_, v_00_u03b1_2550_, v_e_x27_2574_, v_a_2587_);
v___x_2594_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2595_ = l_Lean_mkConst(v___x_2594_, v___x_2583_);
v___x_2596_ = l_Lean_mkAppB(v___x_2595_, v_00_u03b1_2550_, v_e_x27_2574_);
v___x_2597_ = l_Lean_Meta_mkExpectedPropHint(v___x_2596_, v___x_2593_);
v___x_2598_ = l_Lean_mkApp6(v___x_2584_, v_00_u03b1_2550_, v_e_2536_, v_e_x27_2574_, v_a_2587_, v___x_2585_, v___x_2597_);
v___x_2599_ = 0;
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v___x_2598_);
lean_ctor_set(v___x_2578_, 0, v_a_2587_);
v___x_2601_ = v___x_2578_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2587_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v___x_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, sizeof(void*)*2 + 1, v_contextDependent_2576_);
v___x_2601_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*2, v___x_2599_);
v___x_2602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v_00_u03b1_2550_);
lean_ctor_set(v___x_2602_, 2, v_u_2551_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2602_);
v___x_2604_ = v___x_2589_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref(v___x_2585_);
lean_dec_ref(v___x_2584_);
lean_dec_ref(v___x_2583_);
lean_del_object(v___x_2578_);
lean_dec_ref(v_e_x27_2574_);
lean_dec(v_u_2551_);
lean_dec_ref(v_00_u03b1_2550_);
lean_dec_ref(v_e_2536_);
v_a_2608_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2586_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2586_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
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
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_del_object(v___x_2561_);
lean_dec_ref(v_varDeps_2554_);
lean_dec_ref(v_h_2553_);
lean_dec_ref(v_e_2552_);
lean_dec(v_u_2551_);
lean_dec_ref(v_00_u03b1_2550_);
lean_dec_ref(v_e_2536_);
v_a_2619_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2563_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2563_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v_fType_2555_);
lean_dec_ref(v_varDeps_2554_);
lean_dec_ref(v_h_2553_);
lean_dec_ref(v_e_2552_);
lean_dec(v_u_2551_);
lean_dec_ref(v_00_u03b1_2550_);
lean_dec_ref(v_simpBody_2537_);
lean_dec_ref(v_e_2536_);
v_a_2628_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2556_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2556_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v_simpBody_2537_);
lean_dec_ref(v_e_2536_);
v_a_2636_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2548_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2548_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2644_, lean_object* v_simpBody_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2644_, v_simpBody_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2657_, lean_object* v_simpBody_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2657_, v_simpBody_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2678_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_result_2674_; lean_object* v___x_2676_; 
v_result_2674_ = lean_ctor_get(v_a_2670_, 0);
lean_inc_ref(v_result_2674_);
lean_dec(v_a_2670_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v_result_2674_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_result_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2669_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2669_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2687_, lean_object* v_simpBody_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2687_, v_simpBody_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2700_, lean_object* v_simpBody_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v___x_2712_; 
lean_inc_ref(v_e_u2081_2700_);
v___x_2712_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2700_, v_simpBody_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v_result_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref(v___x_2712_);
v_result_2714_ = lean_ctor_get(v_a_2713_, 0);
lean_inc_ref(v_result_2714_);
if (lean_obj_tag(v_result_2714_) == 0)
{
lean_object* v_00_u03b1_2715_; lean_object* v_u_2716_; uint8_t v_contextDependent_2717_; lean_object* v___x_2718_; 
v_00_u03b1_2715_ = lean_ctor_get(v_a_2713_, 1);
lean_inc_ref(v_00_u03b1_2715_);
v_u_2716_ = lean_ctor_get(v_a_2713_, 2);
lean_inc(v_u_2716_);
lean_dec(v_a_2713_);
v_contextDependent_2717_ = lean_ctor_get_uint8(v_result_2714_, 1);
lean_dec_ref(v_result_2714_);
lean_inc_ref(v_e_u2081_2700_);
v___x_2718_ = l_Lean_Meta_zetaUnused(v_e_u2081_2700_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2737_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2737_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2737_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
uint8_t v___x_2723_; 
v___x_2723_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_u2081_2700_, v_a_2719_);
lean_dec_ref(v_e_u2081_2700_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2724_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_u_2716_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l_Lean_mkConst(v___x_2724_, v___x_2726_);
lean_inc(v_a_2719_);
v___x_2728_ = l_Lean_mkAppB(v___x_2727_, v_00_u03b1_2715_, v_a_2719_);
v___x_2729_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2729_, 0, v_a_2719_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*2, v___x_2723_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*2 + 1, v_contextDependent_2717_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2729_);
v___x_2731_ = v___x_2721_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
lean_dec(v_a_2719_);
lean_dec(v_u_2716_);
lean_dec_ref(v_00_u03b1_2715_);
v___x_2733_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2717_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2733_);
v___x_2735_ = v___x_2721_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_u_2716_);
lean_dec_ref(v_00_u03b1_2715_);
lean_dec_ref(v_e_u2081_2700_);
v_a_2738_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2718_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2718_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_00_u03b1_2746_; lean_object* v_u_2747_; lean_object* v_e_x27_2748_; lean_object* v_proof_2749_; uint8_t v_contextDependent_2750_; lean_object* v___x_2751_; 
v_00_u03b1_2746_ = lean_ctor_get(v_a_2713_, 1);
lean_inc_ref(v_00_u03b1_2746_);
v_u_2747_ = lean_ctor_get(v_a_2713_, 2);
lean_inc(v_u_2747_);
lean_dec(v_a_2713_);
v_e_x27_2748_ = lean_ctor_get(v_result_2714_, 0);
v_proof_2749_ = lean_ctor_get(v_result_2714_, 1);
v_contextDependent_2750_ = lean_ctor_get_uint8(v_result_2714_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_2748_);
v___x_2751_ = l_Lean_Meta_zetaUnused(v_e_x27_2748_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2780_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2780_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2780_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
uint8_t v___x_2756_; 
v___x_2756_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_2748_, v_a_2752_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2774_; 
lean_inc_ref(v_proof_2749_);
lean_inc_ref(v_e_x27_2748_);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_result_2714_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; lean_object* v_unused_2776_; 
v_unused_2775_ = lean_ctor_get(v_result_2714_, 1);
lean_dec(v_unused_2775_);
v_unused_2776_ = lean_ctor_get(v_result_2714_, 0);
lean_dec(v_unused_2776_);
v___x_2758_ = v_result_2714_;
v_isShared_2759_ = v_isSharedCheck_2774_;
goto v_resetjp_2757_;
}
else
{
lean_dec(v_result_2714_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2774_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_u_2747_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
lean_inc_ref(v___x_2762_);
v___x_2763_ = l_Lean_mkConst(v___x_2760_, v___x_2762_);
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2765_ = l_Lean_mkConst(v___x_2764_, v___x_2762_);
lean_inc_n(v_a_2752_, 2);
lean_inc_ref(v_00_u03b1_2746_);
v___x_2766_ = l_Lean_mkAppB(v___x_2765_, v_00_u03b1_2746_, v_a_2752_);
v___x_2767_ = l_Lean_mkApp6(v___x_2763_, v_00_u03b1_2746_, v_e_u2081_2700_, v_e_x27_2748_, v_a_2752_, v_proof_2749_, v___x_2766_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2767_);
lean_ctor_set(v___x_2758_, 0, v_a_2752_);
v___x_2769_ = v___x_2758_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2752_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2767_);
lean_ctor_set_uint8(v_reuseFailAlloc_2773_, sizeof(void*)*2 + 1, v_contextDependent_2750_);
v___x_2769_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2771_; 
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*2, v___x_2756_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2769_);
v___x_2771_ = v___x_2754_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v___x_2778_; 
lean_dec(v_a_2752_);
lean_dec(v_u_2747_);
lean_dec_ref(v_00_u03b1_2746_);
lean_dec_ref(v_e_u2081_2700_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_result_2714_);
v___x_2778_ = v___x_2754_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_result_2714_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_u_2747_);
lean_dec_ref(v_00_u03b1_2746_);
lean_dec_ref(v_result_2714_);
lean_dec_ref(v_e_u2081_2700_);
v_a_2781_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2751_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2751_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref(v_e_u2081_2700_);
v_a_2789_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2712_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2712_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_2797_, lean_object* v_simpBody_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_2797_, v_simpBody_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_2810_, lean_object* v_e_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = l_Lean_Expr_letNondep_x21(v_e_2811_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec_ref(v_e_2811_);
lean_dec_ref(v_simpBody_2810_);
v___x_2823_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2823_, 0, v___x_2822_);
lean_ctor_set_uint8(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_2811_, v_simpBody_2810_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_2826_, lean_object* v_e_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_2826_, v_e_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_2852_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_2851_, v_e_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
return v_res_2864_;
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
