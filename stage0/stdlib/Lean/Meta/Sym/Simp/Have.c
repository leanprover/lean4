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
lean_dec(v___y_126_);
v___x_128_ = lean_nat_dec_le(v___y_127_, v___y_124_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec(v___y_124_);
lean_inc(v___y_127_);
v___x_129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_122_, v___y_125_, v___y_127_, v___y_127_);
lean_dec(v___y_127_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_122_, v___y_125_, v___y_127_, v___y_124_);
lean_dec(v___y_124_);
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
v___y_124_ = v___x_137_;
v___y_125_ = v___y_133_;
v___y_126_ = v___x_134_;
v___y_127_ = v___x_137_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_137_;
v___y_125_ = v___y_133_;
v___y_126_ = v___x_134_;
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
v_debug_212_ = lean_ctor_get_uint8(v___x_211_, sizeof(void*)*8);
lean_dec(v___x_211_);
if (v_debug_212_ == 0)
{
v___y_208_ = v___y_201_;
goto v___jp_207_;
}
else
{
lean_object* v___x_213_; 
lean_inc_ref(v_t_198_);
v___x_213_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_198_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; 
lean_dec_ref(v___x_213_);
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
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
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
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
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
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
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
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec_ref(v_00_u03b1s_314_);
return v_res_323_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_6003__overap_334_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0);
v___x_6003__overap_334_ = lean_panic_fn(v___x_333_, v_msg_325_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
v___x_335_ = lean_apply_7(v___x_6003__overap_334_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, lean_box(0));
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_345_, lean_object* v_subst_346_, size_t v_sz_347_, size_t v_i_348_, lean_object* v_bs_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = lean_usize_dec_lt(v_i_348_, v_sz_347_);
if (v___x_350_ == 0)
{
return v_bs_349_;
}
else
{
lean_object* v_v_351_; lean_object* v___x_352_; lean_object* v_bs_x27_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
v_v_351_ = lean_array_uget(v_bs_349_, v_i_348_);
v___x_352_ = lean_unsigned_to_nat(0u);
v_bs_x27_353_ = lean_array_uset(v_bs_349_, v_i_348_, v___x_352_);
v___x_354_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_352_, v_fvarIdToPos_345_, v_v_351_);
lean_dec(v_v_351_);
v___x_355_ = l_Lean_instInhabitedExpr;
v___x_356_ = lean_array_get_borrowed(v___x_355_, v_subst_346_, v___x_354_);
lean_dec(v___x_354_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_348_, v___x_357_);
lean_inc(v___x_356_);
v___x_359_ = lean_array_uset(v_bs_x27_353_, v_i_348_, v___x_356_);
v_i_348_ = v___x_358_;
v_bs_349_ = v___x_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_361_, lean_object* v_subst_362_, lean_object* v_sz_363_, lean_object* v_i_364_, lean_object* v_bs_365_){
_start:
{
size_t v_sz_boxed_366_; size_t v_i_boxed_367_; lean_object* v_res_368_; 
v_sz_boxed_366_ = lean_unbox_usize(v_sz_363_);
lean_dec(v_sz_363_);
v_i_boxed_367_ = lean_unbox_usize(v_i_364_);
lean_dec(v_i_364_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_361_, v_subst_362_, v_sz_boxed_366_, v_i_boxed_367_, v_bs_365_);
lean_dec_ref(v_subst_362_);
lean_dec(v_fvarIdToPos_361_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_369_, size_t v_i_370_, lean_object* v_bs_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_372_ == 0)
{
return v_bs_371_;
}
else
{
lean_object* v_v_373_; lean_object* v___x_374_; lean_object* v_bs_x27_375_; lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v_v_373_ = lean_array_uget(v_bs_371_, v_i_370_);
v___x_374_ = lean_unsigned_to_nat(0u);
v_bs_x27_375_ = lean_array_uset(v_bs_371_, v_i_370_, v___x_374_);
v___x_376_ = l_Lean_mkFVar(v_v_373_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_370_, v___x_377_);
v___x_379_ = lean_array_uset(v_bs_x27_375_, v_i_370_, v___x_376_);
v_i_370_ = v___x_378_;
v_bs_371_ = v___x_379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_bs_383_){
_start:
{
size_t v_sz_boxed_384_; size_t v_i_boxed_385_; lean_object* v_res_386_; 
v_sz_boxed_384_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_384_, v_i_boxed_385_, v_bs_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v_b_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
v___x_396_ = lean_apply_8(v_k_387_, v_b_390_, v___y_388_, v___y_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, lean_box(0));
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v_b_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_397_, v___y_398_, v___y_399_, v_b_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_407_, uint8_t v_bi_408_, lean_object* v_type_409_, lean_object* v_k_410_, uint8_t v_kind_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; 
lean_inc(v___y_413_);
lean_inc_ref(v___y_412_);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_419_, 0, v_k_410_);
lean_closure_set(v___f_419_, 1, v___y_412_);
lean_closure_set(v___f_419_, 2, v___y_413_);
v___x_420_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_407_, v_bi_408_, v_type_409_, v___f_419_, v_kind_411_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_420_) == 0)
{
return v___x_420_;
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_429_, lean_object* v_bi_430_, lean_object* v_type_431_, lean_object* v_k_432_, lean_object* v_kind_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_bi_boxed_441_; uint8_t v_kind_boxed_442_; lean_object* v_res_443_; 
v_bi_boxed_441_ = lean_unbox(v_bi_430_);
v_kind_boxed_442_ = lean_unbox(v_kind_433_);
v_res_443_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_429_, v_bi_boxed_441_, v_type_431_, v_k_432_, v_kind_boxed_442_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_444_, lean_object* v_type_445_, lean_object* v_k_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v___x_454_ = 0;
v___x_455_ = 0;
v___x_456_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_444_, v___x_454_, v_type_445_, v_k_446_, v___x_455_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_457_, lean_object* v_type_458_, lean_object* v_k_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_457_, v_type_458_, v_k_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_468_, lean_object* v_k_469_, lean_object* v_fallback_470_){
_start:
{
if (lean_obj_tag(v_t_468_) == 0)
{
lean_object* v_k_471_; lean_object* v_v_472_; lean_object* v_l_473_; lean_object* v_r_474_; uint8_t v___x_475_; 
v_k_471_ = lean_ctor_get(v_t_468_, 1);
v_v_472_ = lean_ctor_get(v_t_468_, 2);
v_l_473_ = lean_ctor_get(v_t_468_, 3);
v_r_474_ = lean_ctor_get(v_t_468_, 4);
v___x_475_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_469_, v_k_471_);
switch(v___x_475_)
{
case 0:
{
v_t_468_ = v_l_473_;
goto _start;
}
case 1:
{
lean_inc(v_v_472_);
return v_v_472_;
}
default: 
{
v_t_468_ = v_r_474_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_470_);
return v_fallback_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_478_, lean_object* v_k_479_, lean_object* v_fallback_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_478_, v_k_479_, v_fallback_480_);
lean_dec(v_fallback_480_);
lean_dec(v_k_479_);
lean_dec(v_t_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_482_, size_t v_sz_483_, size_t v_i_484_, lean_object* v_bs_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_484_, v_sz_483_);
if (v___x_486_ == 0)
{
return v_bs_485_;
}
else
{
lean_object* v_v_487_; lean_object* v___x_488_; lean_object* v_bs_x27_489_; lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_v_487_ = lean_array_uget(v_bs_485_, v_i_484_);
v___x_488_ = lean_unsigned_to_nat(0u);
v_bs_x27_489_ = lean_array_uset(v_bs_485_, v_i_484_, v___x_488_);
v___x_490_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_482_, v_v_487_, v___x_488_);
lean_dec(v_v_487_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_484_, v___x_491_);
v___x_493_ = lean_array_uset(v_bs_x27_489_, v_i_484_, v___x_490_);
v_i_484_ = v___x_492_;
v_bs_485_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_495_, lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_bs_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_500_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_495_, v_sz_boxed_499_, v_i_boxed_500_, v_bs_498_);
lean_dec(v_fvarIdToPos_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_511_ = _args[0];
lean_object* v_subst_512_ = _args[1];
lean_object* v_sz_513_ = _args[2];
lean_object* v___x_514_ = _args[3];
lean_object* v_fvarIds_515_ = _args[4];
lean_object* v_x_516_ = _args[5];
lean_object* v_xs_517_ = _args[6];
lean_object* v_xs_x27_518_ = _args[7];
lean_object* v_args_519_ = _args[8];
lean_object* v_a_520_ = _args[9];
lean_object* v_types_521_ = _args[10];
lean_object* v_a_522_ = _args[11];
lean_object* v_varDeps_523_ = _args[12];
lean_object* v_varPos_524_ = _args[13];
lean_object* v_haveExpr_525_ = _args[14];
lean_object* v_body_526_ = _args[15];
lean_object* v_x_x27_527_ = _args[16];
lean_object* v___y_528_ = _args[17];
lean_object* v___y_529_ = _args[18];
lean_object* v___y_530_ = _args[19];
lean_object* v___y_531_ = _args[20];
lean_object* v___y_532_ = _args[21];
lean_object* v___y_533_ = _args[22];
lean_object* v___y_534_ = _args[23];
_start:
{
size_t v_sz_boxed_535_; size_t v___x_7252__boxed_536_; lean_object* v_res_537_; 
v_sz_boxed_535_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v___x_7252__boxed_536_ = lean_unbox_usize(v___x_514_);
lean_dec(v___x_514_);
v_res_537_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_511_, v_subst_512_, v_sz_boxed_535_, v___x_7252__boxed_536_, v_fvarIds_515_, v_x_516_, v_xs_517_, v_xs_x27_518_, v_args_519_, v_a_520_, v_types_521_, v_a_522_, v_varDeps_523_, v_varPos_524_, v_haveExpr_525_, v_body_526_, v_x_x27_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_value_538_, lean_object* v_xs_539_, lean_object* v_fvarIdToPos_540_, uint8_t v___x_541_, uint8_t v_nondep_542_, lean_object* v_type_543_, lean_object* v_subst_544_, lean_object* v_xs_x27_545_, lean_object* v_args_546_, lean_object* v_types_547_, lean_object* v_varDeps_548_, lean_object* v_haveExpr_549_, lean_object* v_body_550_, lean_object* v_declName_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_v_560_; lean_object* v_fvarIds_561_; size_t v_sz_562_; size_t v___x_563_; lean_object* v_varPos_564_; lean_object* v_ys_565_; uint8_t v___x_566_; lean_object* v___x_567_; 
v_v_560_ = lean_expr_instantiate_rev(v_value_538_, v_xs_539_);
lean_inc(v_fvarIdToPos_540_);
lean_inc_ref(v_v_560_);
v_fvarIds_561_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_560_, v_fvarIdToPos_540_);
v_sz_562_ = lean_array_size(v_fvarIds_561_);
v___x_563_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_561_);
v_varPos_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_540_, v_sz_562_, v___x_563_, v_fvarIds_561_);
lean_inc_ref(v_fvarIds_561_);
v_ys_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_562_, v___x_563_, v_fvarIds_561_);
v___x_566_ = 1;
v___x_567_ = l_Lean_Meta_mkLambdaFVars(v_ys_565_, v_v_560_, v___x_541_, v_nondep_542_, v___x_541_, v_nondep_542_, v___x_566_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = l_Lean_Meta_mkForallFVars(v_ys_565_, v_type_543_, v___x_541_, v_nondep_542_, v_nondep_542_, v___x_566_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec_ref(v_ys_565_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v___x_571_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_570_, v___y_554_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
v___x_573_ = lean_box_usize(v_sz_562_);
v___x_574_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
lean_inc(v_a_572_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_575_, 0, v_fvarIdToPos_540_);
lean_closure_set(v___f_575_, 1, v_subst_544_);
lean_closure_set(v___f_575_, 2, v___x_573_);
lean_closure_set(v___f_575_, 3, v___x_574_);
lean_closure_set(v___f_575_, 4, v_fvarIds_561_);
lean_closure_set(v___f_575_, 5, v_x_552_);
lean_closure_set(v___f_575_, 6, v_xs_539_);
lean_closure_set(v___f_575_, 7, v_xs_x27_545_);
lean_closure_set(v___f_575_, 8, v_args_546_);
lean_closure_set(v___f_575_, 9, v_a_568_);
lean_closure_set(v___f_575_, 10, v_types_547_);
lean_closure_set(v___f_575_, 11, v_a_572_);
lean_closure_set(v___f_575_, 12, v_varDeps_548_);
lean_closure_set(v___f_575_, 13, v_varPos_564_);
lean_closure_set(v___f_575_, 14, v_haveExpr_549_);
lean_closure_set(v___f_575_, 15, v_body_550_);
v___x_576_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_551_, v_a_572_, v___f_575_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_568_);
lean_dec_ref(v_varPos_564_);
lean_dec_ref(v_fvarIds_561_);
lean_dec_ref(v_x_552_);
lean_dec(v_declName_551_);
lean_dec_ref(v_body_550_);
lean_dec_ref(v_haveExpr_549_);
lean_dec_ref(v_varDeps_548_);
lean_dec_ref(v_types_547_);
lean_dec_ref(v_args_546_);
lean_dec_ref(v_xs_x27_545_);
lean_dec_ref(v_subst_544_);
lean_dec(v_fvarIdToPos_540_);
lean_dec_ref(v_xs_539_);
v_a_577_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_571_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_571_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_a_568_);
lean_dec_ref(v_varPos_564_);
lean_dec_ref(v_fvarIds_561_);
lean_dec_ref(v_x_552_);
lean_dec(v_declName_551_);
lean_dec_ref(v_body_550_);
lean_dec_ref(v_haveExpr_549_);
lean_dec_ref(v_varDeps_548_);
lean_dec_ref(v_types_547_);
lean_dec_ref(v_args_546_);
lean_dec_ref(v_xs_x27_545_);
lean_dec_ref(v_subst_544_);
lean_dec(v_fvarIdToPos_540_);
lean_dec_ref(v_xs_539_);
v_a_585_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_569_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_569_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_ys_565_);
lean_dec_ref(v_varPos_564_);
lean_dec_ref(v_fvarIds_561_);
lean_dec_ref(v_x_552_);
lean_dec(v_declName_551_);
lean_dec_ref(v_body_550_);
lean_dec_ref(v_haveExpr_549_);
lean_dec_ref(v_varDeps_548_);
lean_dec_ref(v_types_547_);
lean_dec_ref(v_args_546_);
lean_dec_ref(v_xs_x27_545_);
lean_dec_ref(v_subst_544_);
lean_dec_ref(v_type_543_);
lean_dec(v_fvarIdToPos_540_);
lean_dec_ref(v_xs_539_);
v_a_593_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_567_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_567_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_value_601_ = _args[0];
lean_object* v_xs_602_ = _args[1];
lean_object* v_fvarIdToPos_603_ = _args[2];
lean_object* v___x_604_ = _args[3];
lean_object* v_nondep_605_ = _args[4];
lean_object* v_type_606_ = _args[5];
lean_object* v_subst_607_ = _args[6];
lean_object* v_xs_x27_608_ = _args[7];
lean_object* v_args_609_ = _args[8];
lean_object* v_types_610_ = _args[9];
lean_object* v_varDeps_611_ = _args[10];
lean_object* v_haveExpr_612_ = _args[11];
lean_object* v_body_613_ = _args[12];
lean_object* v_declName_614_ = _args[13];
lean_object* v_x_615_ = _args[14];
lean_object* v___y_616_ = _args[15];
lean_object* v___y_617_ = _args[16];
lean_object* v___y_618_ = _args[17];
lean_object* v___y_619_ = _args[18];
lean_object* v___y_620_ = _args[19];
lean_object* v___y_621_ = _args[20];
lean_object* v___y_622_ = _args[21];
_start:
{
uint8_t v___x_7280__boxed_623_; uint8_t v_nondep_7281__boxed_624_; lean_object* v_res_625_; 
v___x_7280__boxed_623_ = lean_unbox(v___x_604_);
v_nondep_7281__boxed_624_ = lean_unbox(v_nondep_605_);
v_res_625_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_value_601_, v_xs_602_, v_fvarIdToPos_603_, v___x_7280__boxed_623_, v_nondep_7281__boxed_624_, v_type_606_, v_subst_607_, v_xs_x27_608_, v_args_609_, v_types_610_, v_varDeps_611_, v_haveExpr_612_, v_body_613_, v_declName_614_, v_x_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_value_601_);
return v_res_625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6));
v___x_630_ = lean_unsigned_to_nat(6u);
v___x_631_ = lean_unsigned_to_nat(168u);
v___x_632_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5));
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_634_ = l_mkPanicMessageWithDecl(v___x_633_, v___x_632_, v___x_631_, v___x_630_, v___x_629_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_635_, lean_object* v_e_636_, lean_object* v_xs_637_, lean_object* v_xs_x27_638_, lean_object* v_args_639_, lean_object* v_subst_640_, lean_object* v_types_641_, lean_object* v_varDeps_642_, lean_object* v_fvarIdToPos_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; 
if (lean_obj_tag(v_e_636_) == 8)
{
uint8_t v_nondep_738_; 
v_nondep_738_ = lean_ctor_get_uint8(v_e_636_, sizeof(void*)*4 + 8);
if (v_nondep_738_ == 1)
{
lean_object* v_declName_739_; lean_object* v_type_740_; lean_object* v_value_741_; lean_object* v_body_742_; uint8_t v___x_743_; 
v_declName_739_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_declName_739_);
v_type_740_ = lean_ctor_get(v_e_636_, 1);
lean_inc_ref(v_type_740_);
v_value_741_ = lean_ctor_get(v_e_636_, 2);
lean_inc_ref(v_value_741_);
v_body_742_ = lean_ctor_get(v_e_636_, 3);
lean_inc_ref(v_body_742_);
lean_dec_ref(v_e_636_);
v___x_743_ = l_Lean_Expr_hasLooseBVars(v_type_740_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___x_747_; 
v___x_744_ = lean_box(v___x_743_);
v___x_745_ = lean_box(v_nondep_738_);
lean_inc(v_declName_739_);
lean_inc_ref(v_type_740_);
v___f_746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 22, 14);
lean_closure_set(v___f_746_, 0, v_value_741_);
lean_closure_set(v___f_746_, 1, v_xs_637_);
lean_closure_set(v___f_746_, 2, v_fvarIdToPos_643_);
lean_closure_set(v___f_746_, 3, v___x_744_);
lean_closure_set(v___f_746_, 4, v___x_745_);
lean_closure_set(v___f_746_, 5, v_type_740_);
lean_closure_set(v___f_746_, 6, v_subst_640_);
lean_closure_set(v___f_746_, 7, v_xs_x27_638_);
lean_closure_set(v___f_746_, 8, v_args_639_);
lean_closure_set(v___f_746_, 9, v_types_641_);
lean_closure_set(v___f_746_, 10, v_varDeps_642_);
lean_closure_set(v___f_746_, 11, v_haveExpr_635_);
lean_closure_set(v___f_746_, 12, v_body_742_);
lean_closure_set(v___f_746_, 13, v_declName_739_);
v___x_747_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_739_, v_type_740_, v___f_746_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v_body_742_);
lean_dec_ref(v_value_741_);
lean_dec_ref(v_type_740_);
lean_dec(v_declName_739_);
lean_dec(v_fvarIdToPos_643_);
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_types_641_);
lean_dec_ref(v_subst_640_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v_xs_x27_638_);
lean_dec_ref(v_xs_637_);
lean_dec_ref(v_haveExpr_635_);
v___x_748_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7);
v___x_749_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v___x_748_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_749_;
}
}
else
{
lean_dec(v_fvarIdToPos_643_);
lean_dec_ref(v_xs_637_);
v___y_652_ = v_a_644_;
v___y_653_ = v_a_645_;
v___y_654_ = v_a_646_;
v___y_655_ = v_a_647_;
v___y_656_ = v_a_648_;
v___y_657_ = v_a_649_;
goto v___jp_651_;
}
}
else
{
lean_dec(v_fvarIdToPos_643_);
lean_dec_ref(v_xs_637_);
v___y_652_ = v_a_644_;
v___y_653_ = v_a_645_;
v___y_654_ = v_a_646_;
v___y_655_ = v_a_647_;
v___y_656_ = v_a_648_;
v___y_657_ = v_a_649_;
goto v___jp_651_;
}
v___jp_651_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_array_get_size(v_subst_640_);
v___x_660_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_636_, v___x_658_, v___x_659_, v_subst_640_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec_ref(v_subst_640_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_660_);
lean_inc(v_a_661_);
v___x_662_ = l_Lean_Meta_Sym_inferType___redArg(v_a_661_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref(v___x_662_);
lean_inc(v_a_663_);
v___x_664_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_663_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_666_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
lean_inc(v_a_663_);
v___x_666_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_641_, v_a_663_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec_ref(v_types_641_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_638_, v_a_661_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec_ref(v_xs_x27_638_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref(v___x_668_);
v___x_670_ = l_Lean_mkAppN(v_a_669_, v_args_639_);
lean_dec_ref(v_args_639_);
v___x_671_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_670_, v___y_653_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_689_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_689_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_689_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_689_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_677_ = lean_box(0);
lean_inc(v_a_665_);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v_a_665_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
lean_inc_ref(v___x_678_);
v___x_679_ = l_Lean_mkConst(v___x_676_, v___x_678_);
lean_inc(v_a_672_);
lean_inc_ref(v_haveExpr_635_);
lean_inc(v_a_663_);
v___x_680_ = l_Lean_mkApp3(v___x_679_, v_a_663_, v_haveExpr_635_, v_a_672_);
v___x_681_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_682_ = l_Lean_mkConst(v___x_681_, v___x_678_);
lean_inc(v_a_663_);
v___x_683_ = l_Lean_mkAppB(v___x_682_, v_a_663_, v_haveExpr_635_);
v___x_684_ = l_Lean_Meta_mkExpectedPropHint(v___x_683_, v___x_680_);
v___x_685_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_685_, 0, v_a_663_);
lean_ctor_set(v___x_685_, 1, v_a_665_);
lean_ctor_set(v___x_685_, 2, v_a_672_);
lean_ctor_set(v___x_685_, 3, v___x_684_);
lean_ctor_set(v___x_685_, 4, v_varDeps_642_);
lean_ctor_set(v___x_685_, 5, v_a_667_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_685_);
v___x_687_ = v___x_674_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_a_667_);
lean_dec(v_a_665_);
lean_dec(v_a_663_);
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_haveExpr_635_);
v_a_690_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_671_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_671_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_a_667_);
lean_dec(v_a_665_);
lean_dec(v_a_663_);
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v_haveExpr_635_);
v_a_698_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_668_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_668_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_665_);
lean_dec(v_a_663_);
lean_dec(v_a_661_);
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v_xs_x27_638_);
lean_dec_ref(v_haveExpr_635_);
v_a_706_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_666_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_666_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_663_);
lean_dec(v_a_661_);
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_types_641_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v_xs_x27_638_);
lean_dec_ref(v_haveExpr_635_);
v_a_714_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_664_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_664_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_661_);
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_types_641_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v_xs_x27_638_);
lean_dec_ref(v_haveExpr_635_);
v_a_722_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_662_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_662_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_varDeps_642_);
lean_dec_ref(v_types_641_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v_xs_x27_638_);
lean_dec_ref(v_haveExpr_635_);
v_a_730_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_660_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_660_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_750_, lean_object* v_subst_751_, size_t v_sz_752_, size_t v___x_753_, lean_object* v_fvarIds_754_, lean_object* v_x_755_, lean_object* v_xs_756_, lean_object* v_xs_x27_757_, lean_object* v_args_758_, lean_object* v_a_759_, lean_object* v_types_760_, lean_object* v_a_761_, lean_object* v_varDeps_762_, lean_object* v_varPos_763_, lean_object* v_haveExpr_764_, lean_object* v_body_765_, lean_object* v_x_x27_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_750_, v_subst_751_, v_sz_752_, v___x_753_, v_fvarIds_754_);
lean_inc_ref(v_x_x27_766_);
v___x_775_ = l_Lean_mkAppN(v_x_x27_766_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_775_, v___y_768_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = l_Lean_Expr_fvarId_x21(v_x_755_);
v___x_779_ = lean_array_get_size(v_xs_756_);
v___x_780_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_778_, v___x_779_, v_fvarIdToPos_750_);
v___x_781_ = lean_array_push(v_xs_756_, v_x_755_);
v___x_782_ = lean_array_push(v_xs_x27_757_, v_x_x27_766_);
v___x_783_ = lean_array_push(v_args_758_, v_a_759_);
v___x_784_ = lean_array_push(v_subst_751_, v_a_777_);
v___x_785_ = lean_array_push(v_types_760_, v_a_761_);
v___x_786_ = lean_array_push(v_varDeps_762_, v_varPos_763_);
v___x_787_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_764_, v_body_765_, v___x_781_, v___x_782_, v___x_783_, v___x_784_, v___x_785_, v___x_786_, v___x_780_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_x_x27_766_);
lean_dec_ref(v_body_765_);
lean_dec_ref(v_haveExpr_764_);
lean_dec_ref(v_varPos_763_);
lean_dec_ref(v_varDeps_762_);
lean_dec_ref(v_a_761_);
lean_dec_ref(v_types_760_);
lean_dec_ref(v_a_759_);
lean_dec_ref(v_args_758_);
lean_dec_ref(v_xs_x27_757_);
lean_dec_ref(v_xs_756_);
lean_dec_ref(v_x_755_);
lean_dec_ref(v_subst_751_);
lean_dec(v_fvarIdToPos_750_);
v_a_788_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_776_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_776_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_796_, lean_object* v_e_797_, lean_object* v_xs_798_, lean_object* v_xs_x27_799_, lean_object* v_args_800_, lean_object* v_subst_801_, lean_object* v_types_802_, lean_object* v_varDeps_803_, lean_object* v_fvarIdToPos_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_796_, v_e_797_, v_xs_798_, v_xs_x27_799_, v_args_800_, v_subst_801_, v_types_802_, v_varDeps_803_, v_fvarIdToPos_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_813_, lean_object* v_t_814_, lean_object* v_k_815_, lean_object* v_fallback_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_814_, v_k_815_, v_fallback_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_818_, lean_object* v_t_819_, lean_object* v_k_820_, lean_object* v_fallback_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_818_, v_t_819_, v_k_820_, v_fallback_821_);
lean_dec(v_fallback_821_);
lean_dec(v_k_820_);
lean_dec(v_t_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_823_, lean_object* v_name_824_, uint8_t v_bi_825_, lean_object* v_type_826_, lean_object* v_k_827_, uint8_t v_kind_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_824_, v_bi_825_, v_type_826_, v_k_827_, v_kind_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_837_, lean_object* v_name_838_, lean_object* v_bi_839_, lean_object* v_type_840_, lean_object* v_k_841_, lean_object* v_kind_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v_bi_boxed_850_; uint8_t v_kind_boxed_851_; lean_object* v_res_852_; 
v_bi_boxed_850_ = lean_unbox(v_bi_839_);
v_kind_boxed_851_ = lean_unbox(v_kind_842_);
v_res_852_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_837_, v_name_838_, v_bi_boxed_850_, v_type_840_, v_k_841_, v_kind_boxed_851_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_853_, lean_object* v_name_854_, lean_object* v_type_855_, lean_object* v_k_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_854_, v_type_855_, v_k_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_865_, lean_object* v_name_866_, lean_object* v_type_867_, lean_object* v_k_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_865_, v_name_866_, v_type_867_, v_k_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_888_ = lean_box(1);
lean_inc_ref(v_haveExpr_879_);
v___x_889_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_879_, v_haveExpr_879_, v___x_887_, v___x_887_, v___x_887_, v___x_887_, v___x_887_, v___x_887_, v___x_888_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_899_, lean_object* v_n_900_){
_start:
{
lean_object* v_zero_901_; uint8_t v_isZero_902_; 
v_zero_901_ = lean_unsigned_to_nat(0u);
v_isZero_902_ = lean_nat_dec_eq(v_n_900_, v_zero_901_);
if (v_isZero_902_ == 1)
{
lean_dec(v_n_900_);
return v_type_899_;
}
else
{
lean_object* v_one_903_; lean_object* v_n_904_; lean_object* v___x_905_; 
v_one_903_ = lean_unsigned_to_nat(1u);
v_n_904_ = lean_nat_sub(v_n_900_, v_one_903_);
lean_dec(v_n_900_);
v___x_905_ = l_Lean_Expr_bindingBody_x21(v_type_899_);
lean_dec_ref(v_type_899_);
v_type_899_ = v___x_905_;
v_n_900_ = v_n_904_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0(void){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_907_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_00_u03b2_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object* v_idx_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = l_Lean_Expr_bvar___override(v_idx_912_);
v___x_915_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_914_, v___y_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_idx_916_, uint8_t v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v_idx_916_, v___y_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_idx_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v___y_21803__boxed_923_; lean_object* v_res_924_; 
v___y_21803__boxed_923_ = lean_unbox(v___y_921_);
v_res_924_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_idx_920_, v___y_21803__boxed_923_, v___y_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_msg_932_, uint8_t v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___f_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_1733__overap_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___f_935_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_936_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_937_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_938_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_939_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_940_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_941_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___f_935_);
lean_ctor_set(v___x_942_, 1, v___f_936_);
v___x_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___f_937_);
lean_ctor_set(v___x_943_, 2, v___f_938_);
lean_ctor_set(v___x_943_, 3, v___f_939_);
lean_ctor_set(v___x_943_, 4, v___f_940_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___f_941_);
lean_inc_ref(v___x_944_);
v___f_945_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_945_, 0, v___x_944_);
lean_inc_ref(v___x_944_);
v___f_946_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_946_, 0, v___x_944_);
lean_inc_ref(v___x_944_);
v___f_947_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_947_, 0, v___x_944_);
lean_inc_ref(v___x_944_);
v___f_948_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_948_, 0, v___x_944_);
lean_inc_ref(v___x_944_);
v___x_949_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_949_, 0, lean_box(0));
lean_closure_set(v___x_949_, 1, lean_box(0));
lean_closure_set(v___x_949_, 2, v___x_944_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___f_945_);
lean_inc_ref(v___x_944_);
v___x_951_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_951_, 0, lean_box(0));
lean_closure_set(v___x_951_, 1, lean_box(0));
lean_closure_set(v___x_951_, 2, v___x_944_);
v___x_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
lean_ctor_set(v___x_952_, 2, v___f_946_);
lean_ctor_set(v___x_952_, 3, v___f_947_);
lean_ctor_set(v___x_952_, 4, v___f_948_);
v___x_953_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_953_, 0, lean_box(0));
lean_closure_set(v___x_953_, 1, lean_box(0));
lean_closure_set(v___x_953_, 2, v___x_944_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_box(0);
v___x_956_ = l_instInhabitedOfMonad___redArg(v___x_954_, v___x_955_);
v___f_957_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_957_, 0, v___x_956_);
v___x_1733__overap_958_ = lean_panic_fn(v___f_957_, v_msg_932_);
v___x_959_ = lean_box(v___y_933_);
v___x_960_ = lean_apply_2(v___x_1733__overap_958_, v___x_959_, v___y_934_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v___y_21825__boxed_964_; lean_object* v_res_965_; 
v___y_21825__boxed_964_ = lean_unbox(v___y_962_);
v_res_965_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_msg_961_, v___y_21825__boxed_964_, v___y_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object* v_structName_966_, lean_object* v_idx_967_, lean_object* v_struct_968_, lean_object* v___y_969_, uint8_t v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___y_973_; lean_object* v___y_974_; 
if (v___y_970_ == 0)
{
v___y_973_ = v___y_969_;
v___y_974_ = v___y_971_;
goto v___jp_972_;
}
else
{
lean_object* v___x_987_; lean_object* v_snd_988_; 
lean_inc_ref(v_struct_968_);
v___x_987_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_968_, v___y_970_, v___y_971_);
v_snd_988_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_snd_988_);
lean_dec_ref(v___x_987_);
v___y_973_ = v___y_969_;
v___y_974_ = v_snd_988_;
goto v___jp_972_;
}
v___jp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v___x_975_ = l_Lean_Expr_proj___override(v_structName_966_, v_idx_967_, v_struct_968_);
v___x_976_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_975_, v___y_974_);
v_fst_977_ = lean_ctor_get(v___x_976_, 0);
v_snd_978_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v___x_976_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v___x_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___y_973_);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_977_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___y_973_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_snd_978_);
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object* v_structName_989_, lean_object* v_idx_990_, lean_object* v_struct_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___y_21889__boxed_995_; lean_object* v_res_996_; 
v___y_21889__boxed_995_ = lean_unbox(v___y_993_);
v_res_996_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_structName_989_, v_idx_990_, v_struct_991_, v___y_992_, v___y_21889__boxed_995_, v___y_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object* v_x_997_, uint8_t v_bi_998_, lean_object* v_t_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, uint8_t v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___y_1005_; lean_object* v___y_1006_; 
if (v___y_1002_ == 0)
{
v___y_1005_ = v___y_1001_;
v___y_1006_ = v___y_1003_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; lean_object* v_snd_1022_; 
lean_inc_ref(v_t_999_);
v___x_1019_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_999_, v___y_1002_, v___y_1003_);
v_snd_1020_ = lean_ctor_get(v___x_1019_, 1);
lean_inc(v_snd_1020_);
lean_dec_ref(v___x_1019_);
lean_inc_ref(v_b_1000_);
v___x_1021_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1000_, v___y_1002_, v_snd_1020_);
v_snd_1022_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1022_);
lean_dec_ref(v___x_1021_);
v___y_1005_ = v___y_1001_;
v___y_1006_ = v_snd_1022_;
goto v___jp_1004_;
}
v___jp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_fst_1009_; lean_object* v_snd_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1018_; 
v___x_1007_ = l_Lean_Expr_lam___override(v_x_997_, v_t_999_, v_b_1000_, v_bi_998_);
v___x_1008_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1007_, v___y_1006_);
v_fst_1009_ = lean_ctor_get(v___x_1008_, 0);
v_snd_1010_ = lean_ctor_get(v___x_1008_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1012_ = v___x_1008_;
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snd_1010_);
lean_inc(v_fst_1009_);
lean_dec(v___x_1008_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v___y_1005_);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_1009_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___y_1005_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_snd_1010_);
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object* v_x_1023_, lean_object* v_bi_1024_, lean_object* v_t_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v_bi_boxed_1030_; uint8_t v___y_21933__boxed_1031_; lean_object* v_res_1032_; 
v_bi_boxed_1030_ = lean_unbox(v_bi_1024_);
v___y_21933__boxed_1031_ = lean_unbox(v___y_1028_);
v_res_1032_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_x_1023_, v_bi_boxed_1030_, v_t_1025_, v_b_1026_, v___y_1027_, v___y_21933__boxed_1031_, v___y_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object* v_msg_1033_, lean_object* v___y_1034_, uint8_t v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_21467__overap_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___f_1037_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_1038_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_1039_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_1040_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1041_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1042_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1043_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___f_1037_);
lean_ctor_set(v___x_1044_, 1, v___f_1038_);
v___x_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___f_1039_);
lean_ctor_set(v___x_1045_, 2, v___f_1040_);
lean_ctor_set(v___x_1045_, 3, v___f_1041_);
lean_ctor_set(v___x_1045_, 4, v___f_1042_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___f_1043_);
lean_inc_ref(v___x_1046_);
v___f_1047_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1047_, 0, v___x_1046_);
lean_inc_ref(v___x_1046_);
v___f_1048_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1048_, 0, v___x_1046_);
lean_inc_ref(v___x_1046_);
v___f_1049_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1049_, 0, v___x_1046_);
lean_inc_ref(v___x_1046_);
v___f_1050_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1050_, 0, v___x_1046_);
lean_inc_ref(v___x_1046_);
v___x_1051_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1051_, 0, lean_box(0));
lean_closure_set(v___x_1051_, 1, lean_box(0));
lean_closure_set(v___x_1051_, 2, v___x_1046_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___f_1047_);
lean_inc_ref(v___x_1046_);
v___x_1053_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1053_, 0, lean_box(0));
lean_closure_set(v___x_1053_, 1, lean_box(0));
lean_closure_set(v___x_1053_, 2, v___x_1046_);
v___x_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_ctor_set(v___x_1054_, 2, v___f_1048_);
lean_ctor_set(v___x_1054_, 3, v___f_1049_);
lean_ctor_set(v___x_1054_, 4, v___f_1050_);
v___x_1055_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1055_, 0, lean_box(0));
lean_closure_set(v___x_1055_, 1, lean_box(0));
lean_closure_set(v___x_1055_, 2, v___x_1046_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_ReaderT_instMonad___redArg(v___x_1056_);
lean_inc_ref(v___x_1057_);
v___f_1058_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1058_, 0, v___x_1057_);
lean_inc_ref(v___x_1057_);
v___f_1059_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1059_, 0, v___x_1057_);
lean_inc_ref(v___x_1057_);
v___f_1060_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1060_, 0, v___x_1057_);
lean_inc_ref(v___x_1057_);
v___f_1061_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1061_, 0, v___x_1057_);
lean_inc_ref(v___x_1057_);
v___x_1062_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, lean_box(0));
lean_closure_set(v___x_1062_, 2, v___x_1057_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___f_1058_);
lean_inc_ref(v___x_1057_);
v___x_1064_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1064_, 0, lean_box(0));
lean_closure_set(v___x_1064_, 1, lean_box(0));
lean_closure_set(v___x_1064_, 2, v___x_1057_);
v___x_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
lean_ctor_set(v___x_1065_, 2, v___f_1059_);
lean_ctor_set(v___x_1065_, 3, v___f_1060_);
lean_ctor_set(v___x_1065_, 4, v___f_1061_);
v___x_1066_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1066_, 0, lean_box(0));
lean_closure_set(v___x_1066_, 1, lean_box(0));
lean_closure_set(v___x_1066_, 2, v___x_1057_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_Lean_instInhabitedExpr;
v___x_1069_ = l_instInhabitedOfMonad___redArg(v___x_1067_, v___x_1068_);
v___x_21467__overap_1070_ = lean_panic_fn(v___x_1069_, v_msg_1033_);
v___x_1071_ = lean_box(v___y_1035_);
v___x_1072_ = lean_apply_3(v___x_21467__overap_1070_, v___y_1034_, v___x_1071_, v___y_1036_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v___y_21989__boxed_1077_; lean_object* v_res_1078_; 
v___y_21989__boxed_1077_ = lean_unbox(v___y_1075_);
v_res_1078_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v_msg_1073_, v___y_1074_, v___y_21989__boxed_1077_, v___y_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object* v_f_1079_, lean_object* v_a_1080_, lean_object* v___y_1081_, uint8_t v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___y_1085_; lean_object* v___y_1086_; 
if (v___y_1082_ == 0)
{
v___y_1085_ = v___y_1081_;
v___y_1086_ = v___y_1083_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1099_; lean_object* v_snd_1100_; lean_object* v___x_1101_; lean_object* v_snd_1102_; 
lean_inc_ref(v_f_1079_);
v___x_1099_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1079_, v___y_1082_, v___y_1083_);
v_snd_1100_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_snd_1100_);
lean_dec_ref(v___x_1099_);
lean_inc_ref(v_a_1080_);
v___x_1101_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1080_, v___y_1082_, v_snd_1100_);
v_snd_1102_ = lean_ctor_get(v___x_1101_, 1);
lean_inc(v_snd_1102_);
lean_dec_ref(v___x_1101_);
v___y_1085_ = v___y_1081_;
v___y_1086_ = v_snd_1102_;
goto v___jp_1084_;
}
v___jp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v___x_1087_ = l_Lean_Expr_app___override(v_f_1079_, v_a_1080_);
v___x_1088_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1087_, v___y_1086_);
v_fst_1089_ = lean_ctor_get(v___x_1088_, 0);
v_snd_1090_ = lean_ctor_get(v___x_1088_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v___x_1088_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_snd_1090_);
lean_inc(v_fst_1089_);
lean_dec(v___x_1088_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v___y_1085_);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_fst_1089_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___y_1085_);
v___x_1095_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_snd_1090_);
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object* v_f_1103_, lean_object* v_a_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v___y_22068__boxed_1108_; lean_object* v_res_1109_; 
v___y_22068__boxed_1108_ = lean_unbox(v___y_1106_);
v_res_1109_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_f_1103_, v_a_1104_, v___y_1105_, v___y_22068__boxed_1108_, v___y_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object* v_x_1110_, uint8_t v_bi_1111_, lean_object* v_t_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, uint8_t v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___y_1118_; lean_object* v___y_1119_; 
if (v___y_1115_ == 0)
{
v___y_1118_ = v___y_1114_;
v___y_1119_ = v___y_1116_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1132_; lean_object* v_snd_1133_; lean_object* v___x_1134_; lean_object* v_snd_1135_; 
lean_inc_ref(v_t_1112_);
v___x_1132_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1112_, v___y_1115_, v___y_1116_);
v_snd_1133_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_snd_1133_);
lean_dec_ref(v___x_1132_);
lean_inc_ref(v_b_1113_);
v___x_1134_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1113_, v___y_1115_, v_snd_1133_);
v_snd_1135_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_snd_1135_);
lean_dec_ref(v___x_1134_);
v___y_1118_ = v___y_1114_;
v___y_1119_ = v_snd_1135_;
goto v___jp_1117_;
}
v___jp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v___x_1120_ = l_Lean_Expr_forallE___override(v_x_1110_, v_t_1112_, v_b_1113_, v_bi_1111_);
v___x_1121_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1120_, v___y_1119_);
v_fst_1122_ = lean_ctor_get(v___x_1121_, 0);
v_snd_1123_ = lean_ctor_get(v___x_1121_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snd_1123_);
lean_inc(v_fst_1122_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___y_1118_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_fst_1122_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___y_1118_);
v___x_1128_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_snd_1123_);
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object* v_x_1136_, lean_object* v_bi_1137_, lean_object* v_t_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_bi_boxed_1143_; uint8_t v___y_22117__boxed_1144_; lean_object* v_res_1145_; 
v_bi_boxed_1143_ = lean_unbox(v_bi_1137_);
v___y_22117__boxed_1144_ = lean_unbox(v___y_1141_);
v_res_1145_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_x_1136_, v_bi_boxed_1143_, v_t_1138_, v_b_1139_, v___y_1140_, v___y_22117__boxed_1144_, v___y_1142_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object* v_x_1146_, lean_object* v_t_1147_, lean_object* v_v_1148_, lean_object* v_b_1149_, uint8_t v_nondep_1150_, lean_object* v___y_1151_, uint8_t v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___y_1155_; lean_object* v___y_1156_; 
if (v___y_1152_ == 0)
{
v___y_1155_ = v___y_1151_;
v___y_1156_ = v___y_1153_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1169_; lean_object* v_snd_1170_; lean_object* v___x_1171_; lean_object* v_snd_1172_; lean_object* v___x_1173_; lean_object* v_snd_1174_; 
lean_inc_ref(v_t_1147_);
v___x_1169_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1147_, v___y_1152_, v___y_1153_);
v_snd_1170_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_snd_1170_);
lean_dec_ref(v___x_1169_);
lean_inc_ref(v_v_1148_);
v___x_1171_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1148_, v___y_1152_, v_snd_1170_);
v_snd_1172_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_snd_1172_);
lean_dec_ref(v___x_1171_);
lean_inc_ref(v_b_1149_);
v___x_1173_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1149_, v___y_1152_, v_snd_1172_);
v_snd_1174_ = lean_ctor_get(v___x_1173_, 1);
lean_inc(v_snd_1174_);
lean_dec_ref(v___x_1173_);
v___y_1155_ = v___y_1151_;
v___y_1156_ = v_snd_1174_;
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_fst_1159_; lean_object* v_snd_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v___x_1157_ = l_Lean_Expr_letE___override(v_x_1146_, v_t_1147_, v_v_1148_, v_b_1149_, v_nondep_1150_);
v___x_1158_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1157_, v___y_1156_);
v_fst_1159_ = lean_ctor_get(v___x_1158_, 0);
v_snd_1160_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v___x_1158_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_snd_1160_);
lean_inc(v_fst_1159_);
lean_dec(v___x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___y_1155_);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_fst_1159_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___y_1155_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_snd_1160_);
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object* v_x_1175_, lean_object* v_t_1176_, lean_object* v_v_1177_, lean_object* v_b_1178_, lean_object* v_nondep_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_nondep_boxed_1183_; uint8_t v___y_22166__boxed_1184_; lean_object* v_res_1185_; 
v_nondep_boxed_1183_ = lean_unbox(v_nondep_1179_);
v___y_22166__boxed_1184_ = lean_unbox(v___y_1181_);
v_res_1185_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_x_1175_, v_t_1176_, v_v_1177_, v_b_1178_, v_nondep_boxed_1183_, v___y_1180_, v___y_22166__boxed_1184_, v___y_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_a_1186_, lean_object* v_x_1187_){
_start:
{
if (lean_obj_tag(v_x_1187_) == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
else
{
lean_object* v_key_1189_; lean_object* v_value_1190_; lean_object* v_tail_1191_; uint8_t v___y_1193_; lean_object* v_fst_1196_; lean_object* v_snd_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; uint8_t v___x_1200_; 
v_key_1189_ = lean_ctor_get(v_x_1187_, 0);
v_value_1190_ = lean_ctor_get(v_x_1187_, 1);
v_tail_1191_ = lean_ctor_get(v_x_1187_, 2);
v_fst_1196_ = lean_ctor_get(v_key_1189_, 0);
v_snd_1197_ = lean_ctor_get(v_key_1189_, 1);
v_fst_1198_ = lean_ctor_get(v_a_1186_, 0);
v_snd_1199_ = lean_ctor_get(v_a_1186_, 1);
v___x_1200_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1196_, v_fst_1198_);
if (v___x_1200_ == 0)
{
v___y_1193_ = v___x_1200_;
goto v___jp_1192_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_eq(v_snd_1197_, v_snd_1199_);
v___y_1193_ = v___x_1201_;
goto v___jp_1192_;
}
v___jp_1192_:
{
if (v___y_1193_ == 0)
{
v_x_1187_ = v_tail_1191_;
goto _start;
}
else
{
lean_object* v___x_1195_; 
lean_inc(v_value_1190_);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_value_1190_);
return v___x_1195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1202_, v_x_1203_);
lean_dec(v_x_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_buckets_1207_; lean_object* v_fst_1208_; lean_object* v_snd_1209_; lean_object* v___x_1210_; uint64_t v___x_1211_; uint64_t v___x_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; uint64_t v___x_1215_; uint64_t v_fold_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; uint64_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_buckets_1207_ = lean_ctor_get(v_m_1205_, 1);
v_fst_1208_ = lean_ctor_get(v_a_1206_, 0);
v_snd_1209_ = lean_ctor_get(v_a_1206_, 1);
v___x_1210_ = lean_array_get_size(v_buckets_1207_);
v___x_1211_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1208_);
v___x_1212_ = lean_uint64_of_nat(v_snd_1209_);
v___x_1213_ = lean_uint64_mix_hash(v___x_1211_, v___x_1212_);
v___x_1214_ = 32ULL;
v___x_1215_ = lean_uint64_shift_right(v___x_1213_, v___x_1214_);
v_fold_1216_ = lean_uint64_xor(v___x_1213_, v___x_1215_);
v___x_1217_ = 16ULL;
v___x_1218_ = lean_uint64_shift_right(v_fold_1216_, v___x_1217_);
v___x_1219_ = lean_uint64_xor(v_fold_1216_, v___x_1218_);
v___x_1220_ = lean_uint64_to_usize(v___x_1219_);
v___x_1221_ = lean_usize_of_nat(v___x_1210_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_sub(v___x_1221_, v___x_1222_);
v___x_1224_ = lean_usize_land(v___x_1220_, v___x_1223_);
v___x_1225_ = lean_array_uget_borrowed(v_buckets_1207_, v___x_1224_);
v___x_1226_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1206_, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1227_, v_a_1228_);
lean_dec_ref(v_a_1228_);
lean_dec_ref(v_m_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object* v_d_1230_, lean_object* v_e_1231_, lean_object* v___y_1232_, uint8_t v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___y_1236_; lean_object* v___y_1237_; 
if (v___y_1233_ == 0)
{
v___y_1236_ = v___y_1232_;
v___y_1237_ = v___y_1234_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1250_; lean_object* v_snd_1251_; 
lean_inc_ref(v_e_1231_);
v___x_1250_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1231_, v___y_1233_, v___y_1234_);
v_snd_1251_ = lean_ctor_get(v___x_1250_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v___x_1250_);
v___y_1236_ = v___y_1232_;
v___y_1237_ = v_snd_1251_;
goto v___jp_1235_;
}
v___jp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v___x_1238_ = l_Lean_Expr_mdata___override(v_d_1230_, v_e_1231_);
v___x_1239_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1238_, v___y_1237_);
v_fst_1240_ = lean_ctor_get(v___x_1239_, 0);
v_snd_1241_ = lean_ctor_get(v___x_1239_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1243_ = v___x_1239_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v___x_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___y_1236_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_fst_1240_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___y_1236_);
v___x_1246_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v_snd_1241_);
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object* v_d_1252_, lean_object* v_e_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v___y_22289__boxed_1257_; lean_object* v_res_1258_; 
v___y_22289__boxed_1257_ = lean_unbox(v___y_1255_);
v_res_1258_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_d_1252_, v_e_1253_, v___y_1254_, v___y_22289__boxed_1257_, v___y_1256_);
return v_res_1258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Array_instInhabited(lean_box(0));
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2));
v___x_1263_ = lean_unsigned_to_nat(12u);
v___x_1264_ = lean_unsigned_to_nat(234u);
v___x_1265_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1));
v___x_1266_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1267_ = l_mkPanicMessageWithDecl(v___x_1266_, v___x_1265_, v___x_1264_, v___x_1263_, v___x_1262_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1272_ = lean_unsigned_to_nat(67u);
v___x_1273_ = lean_unsigned_to_nat(35u);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1));
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0));
v___x_1276_ = l_mkPanicMessageWithDecl(v___x_1275_, v___x_1274_, v___x_1273_, v___x_1272_, v___x_1271_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_n_1277_, lean_object* v_varDeps_1278_, lean_object* v_xs_1279_, lean_object* v_e_1280_, lean_object* v_offset_1281_, lean_object* v_a_1282_, uint8_t v_a_1283_, lean_object* v_a_1284_){
_start:
{
switch(lean_obj_tag(v_e_1280_))
{
case 5:
{
lean_object* v_fn_1285_; lean_object* v_arg_1286_; lean_object* v___x_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1315_; 
v_fn_1285_ = lean_ctor_get(v_e_1280_, 0);
v_arg_1286_ = lean_ctor_get(v_e_1280_, 1);
lean_inc(v_offset_1281_);
lean_inc_ref(v_fn_1285_);
v___x_1287_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_fn_1285_, v_offset_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
v_fst_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1289_);
lean_dec_ref(v___x_1287_);
v_fst_1290_ = lean_ctor_get(v_fst_1288_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v_fst_1288_, 1);
lean_inc(v_snd_1291_);
lean_dec(v_fst_1288_);
lean_inc_ref(v_arg_1286_);
v___x_1292_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_arg_1286_, v_offset_1281_, v_snd_1291_, v_a_1283_, v_snd_1289_);
v_fst_1293_ = lean_ctor_get(v___x_1292_, 0);
v_snd_1294_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1296_ = v___x_1292_;
v_isShared_1297_ = v_isSharedCheck_1315_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_inc(v_fst_1293_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1315_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1314_; 
v_fst_1298_ = lean_ctor_get(v_fst_1293_, 0);
v_snd_1299_ = lean_ctor_get(v_fst_1293_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_fst_1293_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1301_ = v_fst_1293_;
v_isShared_1302_ = v_isSharedCheck_1314_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snd_1299_);
lean_inc(v_fst_1298_);
lean_dec(v_fst_1293_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1314_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
uint8_t v___y_1304_; uint8_t v___x_1312_; 
v___x_1312_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1285_, v_fst_1290_);
if (v___x_1312_ == 0)
{
v___y_1304_ = v___x_1312_;
goto v___jp_1303_;
}
else
{
uint8_t v___x_1313_; 
v___x_1313_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1286_, v_fst_1298_);
v___y_1304_ = v___x_1313_;
goto v___jp_1303_;
}
v___jp_1303_:
{
if (v___y_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_del_object(v___x_1301_);
lean_del_object(v___x_1296_);
lean_dec_ref(v_e_1280_);
v___x_1305_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_fst_1290_, v_fst_1298_, v_snd_1299_, v_a_1283_, v_snd_1294_);
return v___x_1305_;
}
else
{
lean_object* v___x_1307_; 
lean_dec(v_fst_1298_);
lean_dec(v_fst_1290_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v_e_1280_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_e_1280_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_snd_1299_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1307_);
v___x_1309_ = v___x_1296_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_snd_1294_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_1316_; lean_object* v_binderType_1317_; lean_object* v_body_1318_; uint8_t v_binderInfo_1319_; lean_object* v___x_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1350_; 
v_binderName_1316_ = lean_ctor_get(v_e_1280_, 0);
v_binderType_1317_ = lean_ctor_get(v_e_1280_, 1);
v_body_1318_ = lean_ctor_get(v_e_1280_, 2);
v_binderInfo_1319_ = lean_ctor_get_uint8(v_e_1280_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1281_);
lean_inc_ref(v_binderType_1317_);
v___x_1320_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_binderType_1317_, v_offset_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
v_fst_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_fst_1321_);
v_snd_1322_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_snd_1322_);
lean_dec_ref(v___x_1320_);
v_fst_1323_ = lean_ctor_get(v_fst_1321_, 0);
lean_inc(v_fst_1323_);
v_snd_1324_ = lean_ctor_get(v_fst_1321_, 1);
lean_inc(v_snd_1324_);
lean_dec(v_fst_1321_);
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = lean_nat_add(v_offset_1281_, v___x_1325_);
lean_dec(v_offset_1281_);
lean_inc_ref(v_body_1318_);
v___x_1327_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_body_1318_, v___x_1326_, v_snd_1324_, v_a_1283_, v_snd_1322_);
v_fst_1328_ = lean_ctor_get(v___x_1327_, 0);
v_snd_1329_ = lean_ctor_get(v___x_1327_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1331_ = v___x_1327_;
v_isShared_1332_ = v_isSharedCheck_1350_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_snd_1329_);
lean_inc(v_fst_1328_);
lean_dec(v___x_1327_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1350_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1349_; 
v_fst_1333_ = lean_ctor_get(v_fst_1328_, 0);
v_snd_1334_ = lean_ctor_get(v_fst_1328_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_fst_1328_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1336_ = v_fst_1328_;
v_isShared_1337_ = v_isSharedCheck_1349_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snd_1334_);
lean_inc(v_fst_1333_);
lean_dec(v_fst_1328_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1349_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
uint8_t v___y_1339_; uint8_t v___x_1347_; 
v___x_1347_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1317_, v_fst_1323_);
if (v___x_1347_ == 0)
{
v___y_1339_ = v___x_1347_;
goto v___jp_1338_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1318_, v_fst_1333_);
v___y_1339_ = v___x_1348_;
goto v___jp_1338_;
}
v___jp_1338_:
{
if (v___y_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_inc(v_binderName_1316_);
lean_del_object(v___x_1336_);
lean_del_object(v___x_1331_);
lean_dec_ref(v_e_1280_);
v___x_1340_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_binderName_1316_, v_binderInfo_1319_, v_fst_1323_, v_fst_1333_, v_snd_1334_, v_a_1283_, v_snd_1329_);
return v___x_1340_;
}
else
{
lean_object* v___x_1342_; 
lean_dec(v_fst_1333_);
lean_dec(v_fst_1323_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_e_1280_);
v___x_1342_ = v___x_1336_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_e_1280_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_snd_1334_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1342_);
v___x_1344_ = v___x_1331_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_snd_1329_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1351_; lean_object* v_binderType_1352_; lean_object* v_body_1353_; uint8_t v_binderInfo_1354_; lean_object* v___x_1355_; lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1385_; 
v_binderName_1351_ = lean_ctor_get(v_e_1280_, 0);
v_binderType_1352_ = lean_ctor_get(v_e_1280_, 1);
v_body_1353_ = lean_ctor_get(v_e_1280_, 2);
v_binderInfo_1354_ = lean_ctor_get_uint8(v_e_1280_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1281_);
lean_inc_ref(v_binderType_1352_);
v___x_1355_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_binderType_1352_, v_offset_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
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
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_nat_add(v_offset_1281_, v___x_1360_);
lean_dec(v_offset_1281_);
lean_inc_ref(v_body_1353_);
v___x_1362_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_body_1353_, v___x_1361_, v_snd_1359_, v_a_1283_, v_snd_1357_);
v_fst_1363_ = lean_ctor_get(v___x_1362_, 0);
v_snd_1364_ = lean_ctor_get(v___x_1362_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1366_ = v___x_1362_;
v_isShared_1367_ = v_isSharedCheck_1385_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snd_1364_);
lean_inc(v_fst_1363_);
lean_dec(v___x_1362_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1385_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_fst_1368_; lean_object* v_snd_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1384_; 
v_fst_1368_ = lean_ctor_get(v_fst_1363_, 0);
v_snd_1369_ = lean_ctor_get(v_fst_1363_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_fst_1363_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1371_ = v_fst_1363_;
v_isShared_1372_ = v_isSharedCheck_1384_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_snd_1369_);
lean_inc(v_fst_1368_);
lean_dec(v_fst_1363_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1384_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___y_1374_; uint8_t v___x_1382_; 
v___x_1382_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1352_, v_fst_1358_);
if (v___x_1382_ == 0)
{
v___y_1374_ = v___x_1382_;
goto v___jp_1373_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1353_, v_fst_1368_);
v___y_1374_ = v___x_1383_;
goto v___jp_1373_;
}
v___jp_1373_:
{
if (v___y_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_inc(v_binderName_1351_);
lean_del_object(v___x_1371_);
lean_del_object(v___x_1366_);
lean_dec_ref(v_e_1280_);
v___x_1375_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_binderName_1351_, v_binderInfo_1354_, v_fst_1358_, v_fst_1368_, v_snd_1369_, v_a_1283_, v_snd_1364_);
return v___x_1375_;
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_fst_1368_);
lean_dec(v_fst_1358_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_e_1280_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_e_1280_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_snd_1369_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1377_);
v___x_1379_ = v___x_1366_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_snd_1364_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1386_; lean_object* v_type_1387_; lean_object* v_value_1388_; lean_object* v_body_1389_; uint8_t v_nondep_1390_; lean_object* v___x_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1396_; lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1428_; 
v_declName_1386_ = lean_ctor_get(v_e_1280_, 0);
v_type_1387_ = lean_ctor_get(v_e_1280_, 1);
v_value_1388_ = lean_ctor_get(v_e_1280_, 2);
v_body_1389_ = lean_ctor_get(v_e_1280_, 3);
v_nondep_1390_ = lean_ctor_get_uint8(v_e_1280_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1281_);
lean_inc_ref(v_type_1387_);
v___x_1391_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_type_1387_, v_offset_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
v_fst_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_fst_1392_);
v_snd_1393_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_snd_1393_);
lean_dec_ref(v___x_1391_);
v_fst_1394_ = lean_ctor_get(v_fst_1392_, 0);
lean_inc(v_fst_1394_);
v_snd_1395_ = lean_ctor_get(v_fst_1392_, 1);
lean_inc(v_snd_1395_);
lean_dec(v_fst_1392_);
lean_inc(v_offset_1281_);
lean_inc_ref(v_value_1388_);
v___x_1396_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_value_1388_, v_offset_1281_, v_snd_1395_, v_a_1283_, v_snd_1393_);
v_fst_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_fst_1397_);
v_snd_1398_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_snd_1398_);
lean_dec_ref(v___x_1396_);
v_fst_1399_ = lean_ctor_get(v_fst_1397_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v_fst_1397_, 1);
lean_inc(v_snd_1400_);
lean_dec(v_fst_1397_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v_offset_1281_, v___x_1401_);
lean_dec(v_offset_1281_);
lean_inc_ref(v_body_1389_);
v___x_1403_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_body_1389_, v___x_1402_, v_snd_1400_, v_a_1283_, v_snd_1398_);
v_fst_1404_ = lean_ctor_get(v___x_1403_, 0);
v_snd_1405_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1407_ = v___x_1403_;
v_isShared_1408_ = v_isSharedCheck_1428_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1404_);
lean_dec(v___x_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1428_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1427_; 
v_fst_1409_ = lean_ctor_get(v_fst_1404_, 0);
v_snd_1410_ = lean_ctor_get(v_fst_1404_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_fst_1404_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1412_ = v_fst_1404_;
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_inc(v_fst_1409_);
lean_dec(v_fst_1404_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
uint8_t v___y_1415_; uint8_t v___x_1425_; 
v___x_1425_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1387_, v_fst_1394_);
if (v___x_1425_ == 0)
{
v___y_1415_ = v___x_1425_;
goto v___jp_1414_;
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1388_, v_fst_1399_);
v___y_1415_ = v___x_1426_;
goto v___jp_1414_;
}
v___jp_1414_:
{
if (v___y_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_inc(v_declName_1386_);
lean_del_object(v___x_1412_);
lean_del_object(v___x_1407_);
lean_dec_ref(v_e_1280_);
v___x_1416_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1386_, v_fst_1394_, v_fst_1399_, v_fst_1409_, v_nondep_1390_, v_snd_1410_, v_a_1283_, v_snd_1405_);
return v___x_1416_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1389_, v_fst_1409_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_inc(v_declName_1386_);
lean_del_object(v___x_1412_);
lean_del_object(v___x_1407_);
lean_dec_ref(v_e_1280_);
v___x_1418_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1386_, v_fst_1394_, v_fst_1399_, v_fst_1409_, v_nondep_1390_, v_snd_1410_, v_a_1283_, v_snd_1405_);
return v___x_1418_;
}
else
{
lean_object* v___x_1420_; 
lean_dec(v_fst_1409_);
lean_dec(v_fst_1399_);
lean_dec(v_fst_1394_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v_e_1280_);
v___x_1420_ = v___x_1412_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_e_1280_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_snd_1410_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1420_);
v___x_1422_ = v___x_1407_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1405_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
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
lean_object* v_data_1429_; lean_object* v_expr_1430_; lean_object* v___x_1431_; lean_object* v_fst_1432_; lean_object* v_snd_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1451_; 
v_data_1429_ = lean_ctor_get(v_e_1280_, 0);
v_expr_1430_ = lean_ctor_get(v_e_1280_, 1);
lean_inc_ref(v_expr_1430_);
v___x_1431_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_expr_1430_, v_offset_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
v_fst_1432_ = lean_ctor_get(v___x_1431_, 0);
v_snd_1433_ = lean_ctor_get(v___x_1431_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1435_ = v___x_1431_;
v_isShared_1436_ = v_isSharedCheck_1451_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snd_1433_);
lean_inc(v_fst_1432_);
lean_dec(v___x_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1451_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_fst_1437_; lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1450_; 
v_fst_1437_ = lean_ctor_get(v_fst_1432_, 0);
v_snd_1438_ = lean_ctor_get(v_fst_1432_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_fst_1432_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1440_ = v_fst_1432_;
v_isShared_1441_ = v_isSharedCheck_1450_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_inc(v_fst_1437_);
lean_dec(v_fst_1432_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1450_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
uint8_t v___x_1442_; 
v___x_1442_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1430_, v_fst_1437_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_data_1429_);
lean_del_object(v___x_1440_);
lean_del_object(v___x_1435_);
lean_dec_ref(v_e_1280_);
v___x_1443_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_data_1429_, v_fst_1437_, v_snd_1438_, v_a_1283_, v_snd_1433_);
return v___x_1443_;
}
else
{
lean_object* v___x_1445_; 
lean_dec(v_fst_1437_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_e_1280_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_e_1280_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1438_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1445_);
v___x_1447_ = v___x_1435_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1433_);
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
case 11:
{
lean_object* v_typeName_1452_; lean_object* v_idx_1453_; lean_object* v_struct_1454_; lean_object* v___x_1455_; lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1475_; 
v_typeName_1452_ = lean_ctor_get(v_e_1280_, 0);
v_idx_1453_ = lean_ctor_get(v_e_1280_, 1);
v_struct_1454_ = lean_ctor_get(v_e_1280_, 2);
lean_inc_ref(v_struct_1454_);
v___x_1455_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1277_, v_varDeps_1278_, v_xs_1279_, v_struct_1454_, v_offset_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
v_fst_1456_ = lean_ctor_get(v___x_1455_, 0);
v_snd_1457_ = lean_ctor_get(v___x_1455_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1459_ = v___x_1455_;
v_isShared_1460_ = v_isSharedCheck_1475_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snd_1457_);
lean_inc(v_fst_1456_);
lean_dec(v___x_1455_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1475_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v_fst_1461_; lean_object* v_snd_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1474_; 
v_fst_1461_ = lean_ctor_get(v_fst_1456_, 0);
v_snd_1462_ = lean_ctor_get(v_fst_1456_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_fst_1456_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1464_ = v_fst_1456_;
v_isShared_1465_ = v_isSharedCheck_1474_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snd_1462_);
lean_inc(v_fst_1461_);
lean_dec(v_fst_1456_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1474_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint8_t v___x_1466_; 
v___x_1466_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1454_, v_fst_1461_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
lean_inc(v_idx_1453_);
lean_inc(v_typeName_1452_);
lean_del_object(v___x_1464_);
lean_del_object(v___x_1459_);
lean_dec_ref(v_e_1280_);
v___x_1467_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_typeName_1452_, v_idx_1453_, v_fst_1461_, v_snd_1462_, v_a_1283_, v_snd_1457_);
return v___x_1467_;
}
else
{
lean_object* v___x_1469_; 
lean_dec(v_fst_1461_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_e_1280_);
v___x_1469_ = v___x_1464_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_e_1280_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_snd_1462_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1469_);
v___x_1471_ = v___x_1459_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_snd_1457_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v_offset_1281_);
lean_dec_ref(v_e_1280_);
v___x_1476_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3);
v___x_1477_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v___x_1476_, v_a_1282_, v_a_1283_, v_a_1284_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object* v_n_1478_, lean_object* v_varDeps_1479_, lean_object* v_xs_1480_, lean_object* v_e_1481_, lean_object* v_offset_1482_, lean_object* v_a_1483_, uint8_t v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_key_1486_; lean_object* v_snd_1488_; lean_object* v___x_1501_; 
lean_inc(v_offset_1482_);
lean_inc_ref(v_e_1481_);
v_key_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1486_, 0, v_e_1481_);
lean_ctor_set(v_key_1486_, 1, v_offset_1482_);
v___x_1501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_a_1483_, v_key_1486_);
if (lean_obj_tag(v___x_1501_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v_key_1486_);
lean_dec(v_offset_1482_);
lean_dec_ref(v_e_1481_);
v_val_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_val_1502_);
lean_ctor_set(v___x_1503_, 1, v_a_1483_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v_a_1485_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
lean_dec(v___x_1501_);
v___x_1505_ = l_Lean_Expr_looseBVarRange(v_e_1481_);
v___x_1506_ = lean_nat_dec_le(v___x_1505_, v_offset_1482_);
lean_dec(v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Expr_getAppFn(v_e_1481_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_deBruijnIndex_1508_; uint8_t v___x_1509_; 
v_deBruijnIndex_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_deBruijnIndex_1508_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = lean_nat_dec_le(v_offset_1482_, v_deBruijnIndex_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec(v_deBruijnIndex_1508_);
lean_dec(v_offset_1482_);
v___x_1510_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_nat_add(v_offset_1482_, v_n_1478_);
v___x_1512_ = lean_nat_dec_lt(v_deBruijnIndex_1508_, v___x_1511_);
lean_dec(v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_fst_1515_; lean_object* v_snd_1516_; lean_object* v___x_1517_; 
lean_dec(v_offset_1482_);
lean_dec_ref(v_e_1481_);
v___x_1513_ = lean_nat_sub(v_deBruijnIndex_1508_, v_n_1478_);
lean_dec(v_deBruijnIndex_1508_);
v___x_1514_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1513_, v_a_1485_);
v_fst_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_fst_1515_);
v_snd_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_snd_1516_);
lean_dec_ref(v___x_1514_);
v___x_1517_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_fst_1515_, v_a_1483_, v_a_1484_, v_snd_1516_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_i_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_expectedNumArgs_1524_; lean_object* v_numArgs_1525_; uint8_t v___x_1526_; 
v___x_1518_ = lean_nat_sub(v_deBruijnIndex_1508_, v_offset_1482_);
lean_dec(v_deBruijnIndex_1508_);
v___x_1519_ = lean_nat_sub(v_n_1478_, v___x_1518_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_unsigned_to_nat(1u);
v_i_1521_ = lean_nat_sub(v___x_1519_, v___x_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1523_ = lean_array_get_borrowed(v___x_1522_, v_varDeps_1479_, v_i_1521_);
v_expectedNumArgs_1524_ = lean_array_get_size(v___x_1523_);
v_numArgs_1525_ = l_Lean_Expr_getAppNumArgs(v_e_1481_);
v___x_1526_ = lean_nat_dec_lt(v_expectedNumArgs_1524_, v_numArgs_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_nat_dec_eq(v_numArgs_1525_, v_expectedNumArgs_1524_);
lean_dec(v_numArgs_1525_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_fst_1530_; 
lean_dec(v_i_1521_);
v___x_1528_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1529_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1528_, v_a_1484_, v_a_1485_);
v_fst_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_fst_1530_);
if (lean_obj_tag(v_fst_1530_) == 1)
{
lean_object* v_snd_1531_; lean_object* v_val_1532_; lean_object* v___x_1533_; 
lean_dec(v_offset_1482_);
lean_dec_ref(v_e_1481_);
v_snd_1531_ = lean_ctor_get(v___x_1529_, 1);
lean_inc(v_snd_1531_);
lean_dec_ref(v___x_1529_);
v_val_1532_ = lean_ctor_get(v_fst_1530_, 0);
lean_inc(v_val_1532_);
lean_dec_ref(v_fst_1530_);
v___x_1533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_val_1532_, v_a_1483_, v_a_1484_, v_snd_1531_);
return v___x_1533_;
}
else
{
lean_object* v_snd_1534_; 
lean_dec(v_fst_1530_);
v_snd_1534_ = lean_ctor_get(v___x_1529_, 1);
lean_inc(v_snd_1534_);
lean_dec_ref(v___x_1529_);
v_snd_1488_ = v_snd_1534_;
goto v___jp_1487_;
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_offset_1482_);
lean_dec_ref(v_e_1481_);
v___x_1535_ = lean_array_fget_borrowed(v_xs_1480_, v_i_1521_);
lean_dec(v_i_1521_);
lean_inc(v___x_1535_);
v___x_1536_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v___x_1535_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1536_;
}
}
else
{
lean_dec(v_numArgs_1525_);
lean_dec(v_i_1521_);
v_snd_1488_ = v_a_1485_;
goto v___jp_1487_;
}
}
}
}
else
{
lean_dec_ref(v___x_1507_);
v_snd_1488_ = v_a_1485_;
goto v___jp_1487_;
}
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_offset_1482_);
v___x_1537_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1537_;
}
}
v___jp_1487_:
{
switch(lean_obj_tag(v_e_1481_))
{
case 9:
{
lean_object* v___x_1489_; 
lean_dec(v_offset_1482_);
v___x_1489_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_snd_1488_);
return v___x_1489_;
}
case 2:
{
lean_object* v___x_1490_; 
lean_dec(v_offset_1482_);
v___x_1490_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_snd_1488_);
return v___x_1490_;
}
case 0:
{
lean_object* v___x_1491_; 
lean_dec(v_offset_1482_);
v___x_1491_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_snd_1488_);
return v___x_1491_;
}
case 1:
{
lean_object* v___x_1492_; 
lean_dec(v_offset_1482_);
v___x_1492_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_snd_1488_);
return v___x_1492_;
}
case 4:
{
lean_object* v___x_1493_; 
lean_dec(v_offset_1482_);
v___x_1493_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_snd_1488_);
return v___x_1493_;
}
case 3:
{
lean_object* v___x_1494_; 
lean_dec(v_offset_1482_);
v___x_1494_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_e_1481_, v_a_1483_, v_a_1484_, v_snd_1488_);
return v___x_1494_;
}
default: 
{
lean_object* v___x_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v_fst_1498_; lean_object* v_snd_1499_; lean_object* v___x_1500_; 
v___x_1495_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1478_, v_varDeps_1479_, v_xs_1480_, v_e_1481_, v_offset_1482_, v_a_1483_, v_a_1484_, v_snd_1488_);
v_fst_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v___x_1495_, 1);
lean_inc(v_snd_1497_);
lean_dec_ref(v___x_1495_);
v_fst_1498_ = lean_ctor_get(v_fst_1496_, 0);
lean_inc(v_fst_1498_);
v_snd_1499_ = lean_ctor_get(v_fst_1496_, 1);
lean_inc(v_snd_1499_);
lean_dec(v_fst_1496_);
v___x_1500_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1486_, v_fst_1498_, v_snd_1499_, v_a_1484_, v_snd_1497_);
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object* v_n_1538_, lean_object* v_varDeps_1539_, lean_object* v_xs_1540_, lean_object* v_e_1541_, lean_object* v_offset_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
uint8_t v_a_boxed_1546_; lean_object* v_res_1547_; 
v_a_boxed_1546_ = lean_unbox(v_a_1544_);
v_res_1547_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1538_, v_varDeps_1539_, v_xs_1540_, v_e_1541_, v_offset_1542_, v_a_1543_, v_a_boxed_1546_, v_a_1545_);
lean_dec_ref(v_xs_1540_);
lean_dec_ref(v_varDeps_1539_);
lean_dec(v_n_1538_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_n_1548_, lean_object* v_varDeps_1549_, lean_object* v_xs_1550_, lean_object* v_e_1551_, lean_object* v_offset_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
uint8_t v_a_boxed_1556_; lean_object* v_res_1557_; 
v_a_boxed_1556_ = lean_unbox(v_a_1554_);
v_res_1557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1548_, v_varDeps_1549_, v_xs_1550_, v_e_1551_, v_offset_1552_, v_a_1553_, v_a_boxed_1556_, v_a_1555_);
lean_dec_ref(v_xs_1550_);
lean_dec_ref(v_varDeps_1549_);
lean_dec(v_n_1548_);
return v_res_1557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0(void){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_box(0));
return v___x_1558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_unsigned_to_nat(16u);
v___x_1561_ = lean_mk_array(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object* v_e_1565_, lean_object* v_xs_1566_, lean_object* v_varDeps_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v_share_1571_; lean_object* v_maxFVar_1572_; lean_object* v_proofInstInfo_1573_; lean_object* v_inferType_1574_; lean_object* v_getLevel_1575_; lean_object* v_congrInfo_1576_; lean_object* v_defEqI_1577_; lean_object* v_extensions_1578_; uint8_t v_debug_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1647_; 
v___x_1570_ = lean_st_ref_take(v_a_1568_);
v_share_1571_ = lean_ctor_get(v___x_1570_, 0);
v_maxFVar_1572_ = lean_ctor_get(v___x_1570_, 1);
v_proofInstInfo_1573_ = lean_ctor_get(v___x_1570_, 2);
v_inferType_1574_ = lean_ctor_get(v___x_1570_, 3);
v_getLevel_1575_ = lean_ctor_get(v___x_1570_, 4);
v_congrInfo_1576_ = lean_ctor_get(v___x_1570_, 5);
v_defEqI_1577_ = lean_ctor_get(v___x_1570_, 6);
v_extensions_1578_ = lean_ctor_get(v___x_1570_, 7);
v_debug_1579_ = lean_ctor_get_uint8(v___x_1570_, sizeof(void*)*8);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1581_ = v___x_1570_;
v_isShared_1582_ = v_isSharedCheck_1647_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_extensions_1578_);
lean_inc(v_defEqI_1577_);
lean_inc(v_congrInfo_1576_);
lean_inc(v_getLevel_1575_);
lean_inc(v_inferType_1574_);
lean_inc(v_proofInstInfo_1573_);
lean_inc(v_maxFVar_1572_);
lean_inc(v_share_1571_);
lean_dec(v___x_1570_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1647_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_maxFVar_1572_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_proofInstInfo_1573_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_inferType_1574_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_getLevel_1575_);
lean_ctor_set(v_reuseFailAlloc_1646_, 5, v_congrInfo_1576_);
lean_ctor_set(v_reuseFailAlloc_1646_, 6, v_defEqI_1577_);
lean_ctor_set(v_reuseFailAlloc_1646_, 7, v_extensions_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*8, v_debug_1579_);
v___x_1585_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; uint8_t v_debug_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1586_ = lean_st_ref_set(v_a_1568_, v___x_1585_);
v___x_1587_ = lean_st_ref_get(v_a_1568_);
v_debug_1610_ = lean_ctor_get_uint8(v___x_1587_, sizeof(void*)*8);
lean_dec(v___x_1587_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = l_Lean_Expr_looseBVarRange(v_e_1565_);
v___x_1613_ = lean_nat_dec_le(v___x_1612_, v___x_1611_);
lean_dec(v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v_n_1614_; lean_object* v_snd_1616_; lean_object* v___x_1622_; 
v_n_1614_ = lean_array_get_size(v_xs_1566_);
v___x_1622_ = l_Lean_Expr_getAppFn(v_e_1565_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_deBruijnIndex_1623_; uint8_t v___x_1624_; 
v_deBruijnIndex_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_deBruijnIndex_1623_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = lean_nat_dec_le(v___x_1611_, v_deBruijnIndex_1623_);
if (v___x_1624_ == 0)
{
lean_dec(v_deBruijnIndex_1623_);
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_share_1571_;
goto v___jp_1588_;
}
else
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_nat_dec_lt(v_deBruijnIndex_1623_, v_n_1614_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; 
lean_dec_ref(v_e_1565_);
v___x_1626_ = lean_nat_sub(v_deBruijnIndex_1623_, v_n_1614_);
lean_dec(v_deBruijnIndex_1623_);
v___x_1627_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1626_, v_share_1571_);
v_fst_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1627_);
v_fst_1589_ = v_fst_1628_;
v_snd_1590_ = v_snd_1629_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_i_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_expectedNumArgs_1635_; lean_object* v_numArgs_1636_; uint8_t v___x_1637_; 
v___x_1630_ = lean_nat_sub(v_n_1614_, v_deBruijnIndex_1623_);
lean_dec(v_deBruijnIndex_1623_);
v___x_1631_ = lean_unsigned_to_nat(1u);
v_i_1632_ = lean_nat_sub(v___x_1630_, v___x_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1634_ = lean_array_get_borrowed(v___x_1633_, v_varDeps_1567_, v_i_1632_);
v_expectedNumArgs_1635_ = lean_array_get_size(v___x_1634_);
v_numArgs_1636_ = l_Lean_Expr_getAppNumArgs(v_e_1565_);
v___x_1637_ = lean_nat_dec_lt(v_expectedNumArgs_1635_, v_numArgs_1636_);
if (v___x_1637_ == 0)
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_nat_dec_eq(v_numArgs_1636_, v_expectedNumArgs_1635_);
lean_dec(v_numArgs_1636_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_fst_1641_; 
lean_dec(v_i_1632_);
v___x_1639_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1640_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1639_, v_debug_1610_, v_share_1571_);
v_fst_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_fst_1641_);
if (lean_obj_tag(v_fst_1641_) == 1)
{
lean_object* v_snd_1642_; lean_object* v_val_1643_; 
lean_dec_ref(v_e_1565_);
v_snd_1642_ = lean_ctor_get(v___x_1640_, 1);
lean_inc(v_snd_1642_);
lean_dec_ref(v___x_1640_);
v_val_1643_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_val_1643_);
lean_dec_ref(v_fst_1641_);
v_fst_1589_ = v_val_1643_;
v_snd_1590_ = v_snd_1642_;
goto v___jp_1588_;
}
else
{
lean_object* v_snd_1644_; 
lean_dec(v_fst_1641_);
v_snd_1644_ = lean_ctor_get(v___x_1640_, 1);
lean_inc(v_snd_1644_);
lean_dec_ref(v___x_1640_);
v_snd_1616_ = v_snd_1644_;
goto v___jp_1615_;
}
}
else
{
lean_object* v___x_1645_; 
lean_dec_ref(v_e_1565_);
v___x_1645_ = lean_array_fget_borrowed(v_xs_1566_, v_i_1632_);
lean_dec(v_i_1632_);
lean_inc(v___x_1645_);
v_fst_1589_ = v___x_1645_;
v_snd_1590_ = v_share_1571_;
goto v___jp_1588_;
}
}
else
{
lean_dec(v_numArgs_1636_);
lean_dec(v_i_1632_);
v_snd_1616_ = v_share_1571_;
goto v___jp_1615_;
}
}
}
}
else
{
lean_dec_ref(v___x_1622_);
v_snd_1616_ = v_share_1571_;
goto v___jp_1615_;
}
v___jp_1615_:
{
switch(lean_obj_tag(v_e_1565_))
{
case 9:
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_snd_1616_;
goto v___jp_1588_;
}
case 2:
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_snd_1616_;
goto v___jp_1588_;
}
case 0:
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_snd_1616_;
goto v___jp_1588_;
}
case 1:
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_snd_1616_;
goto v___jp_1588_;
}
case 4:
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_snd_1616_;
goto v___jp_1588_;
}
case 3:
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_snd_1616_;
goto v___jp_1588_;
}
default: 
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_fst_1619_; lean_object* v_snd_1620_; lean_object* v_fst_1621_; 
v___x_1617_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2);
v___x_1618_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1614_, v_varDeps_1567_, v_xs_1566_, v_e_1565_, v___x_1611_, v___x_1617_, v_debug_1610_, v_snd_1616_);
v_fst_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_fst_1619_);
v_snd_1620_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_snd_1620_);
lean_dec_ref(v___x_1618_);
v_fst_1621_ = lean_ctor_get(v_fst_1619_, 0);
lean_inc(v_fst_1621_);
lean_dec(v_fst_1619_);
v_fst_1589_ = v_fst_1621_;
v_snd_1590_ = v_snd_1620_;
goto v___jp_1588_;
}
}
}
}
else
{
v_fst_1589_ = v_e_1565_;
v_snd_1590_ = v_share_1571_;
goto v___jp_1588_;
}
v___jp_1588_:
{
lean_object* v___x_1591_; lean_object* v_maxFVar_1592_; lean_object* v_proofInstInfo_1593_; lean_object* v_inferType_1594_; lean_object* v_getLevel_1595_; lean_object* v_congrInfo_1596_; lean_object* v_defEqI_1597_; lean_object* v_extensions_1598_; uint8_t v_debug_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1608_; 
v___x_1591_ = lean_st_ref_take(v_a_1568_);
v_maxFVar_1592_ = lean_ctor_get(v___x_1591_, 1);
v_proofInstInfo_1593_ = lean_ctor_get(v___x_1591_, 2);
v_inferType_1594_ = lean_ctor_get(v___x_1591_, 3);
v_getLevel_1595_ = lean_ctor_get(v___x_1591_, 4);
v_congrInfo_1596_ = lean_ctor_get(v___x_1591_, 5);
v_defEqI_1597_ = lean_ctor_get(v___x_1591_, 6);
v_extensions_1598_ = lean_ctor_get(v___x_1591_, 7);
v_debug_1599_ = lean_ctor_get_uint8(v___x_1591_, sizeof(void*)*8);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1591_, 0);
lean_dec(v_unused_1609_);
v___x_1601_ = v___x_1591_;
v_isShared_1602_ = v_isSharedCheck_1608_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_extensions_1598_);
lean_inc(v_defEqI_1597_);
lean_inc(v_congrInfo_1596_);
lean_inc(v_getLevel_1595_);
lean_inc(v_inferType_1594_);
lean_inc(v_proofInstInfo_1593_);
lean_inc(v_maxFVar_1592_);
lean_dec(v___x_1591_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1608_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_snd_1590_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_snd_1590_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_maxFVar_1592_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_proofInstInfo_1593_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_inferType_1594_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_getLevel_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v_congrInfo_1596_);
lean_ctor_set(v_reuseFailAlloc_1607_, 6, v_defEqI_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 7, v_extensions_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*8, v_debug_1599_);
v___x_1604_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_st_ref_set(v_a_1568_, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_fst_1589_);
return v___x_1606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object* v_e_1648_, lean_object* v_xs_1649_, lean_object* v_varDeps_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1648_, v_xs_1649_, v_varDeps_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_varDeps_1650_);
lean_dec_ref(v_xs_1649_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1654_, lean_object* v_xs_1655_, lean_object* v_varDeps_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1654_, v_xs_1655_, v_varDeps_1656_, v_a_1658_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1665_, lean_object* v_xs_1666_, lean_object* v_varDeps_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1665_, v_xs_1666_, v_varDeps_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec_ref(v_varDeps_1667_);
lean_dec_ref(v_xs_1666_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1676_, lean_object* v_m_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1677_, v_a_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1680_, lean_object* v_m_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(v_00_u03b2_1680_, v_m_1681_, v_a_1682_);
lean_dec_ref(v_a_1682_);
lean_dec_ref(v_m_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_1684_, lean_object* v_a_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1685_, v_x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1688_, lean_object* v_a_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(v_00_u03b2_1688_, v_a_1689_, v_x_1690_);
lean_dec(v_x_1690_);
lean_dec_ref(v_a_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1692_, lean_object* v_type_1693_, lean_object* v_val_1694_, lean_object* v_k_1695_, uint8_t v_nondep_1696_, uint8_t v_kind_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___f_1705_; lean_object* v___x_1706_; 
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1705_, 0, v_k_1695_);
lean_closure_set(v___f_1705_, 1, v___y_1698_);
lean_closure_set(v___f_1705_, 2, v___y_1699_);
v___x_1706_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1692_, v_type_1693_, v_val_1694_, v___f_1705_, v_nondep_1696_, v_kind_1697_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1706_) == 0)
{
return v___x_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1715_, lean_object* v_type_1716_, lean_object* v_val_1717_, lean_object* v_k_1718_, lean_object* v_nondep_1719_, lean_object* v_kind_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v_nondep_boxed_1728_; uint8_t v_kind_boxed_1729_; lean_object* v_res_1730_; 
v_nondep_boxed_1728_ = lean_unbox(v_nondep_1719_);
v_kind_boxed_1729_ = lean_unbox(v_kind_1720_);
v_res_1730_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1715_, v_type_1716_, v_val_1717_, v_k_1718_, v_nondep_boxed_1728_, v_kind_boxed_1729_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1731_, lean_object* v_name_1732_, lean_object* v_type_1733_, lean_object* v_val_1734_, lean_object* v_k_1735_, uint8_t v_nondep_1736_, uint8_t v_kind_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1732_, v_type_1733_, v_val_1734_, v_k_1735_, v_nondep_1736_, v_kind_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_name_1747_, lean_object* v_type_1748_, lean_object* v_val_1749_, lean_object* v_k_1750_, lean_object* v_nondep_1751_, lean_object* v_kind_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v_nondep_boxed_1760_; uint8_t v_kind_boxed_1761_; lean_object* v_res_1762_; 
v_nondep_boxed_1760_ = lean_unbox(v_nondep_1751_);
v_kind_boxed_1761_ = lean_unbox(v_kind_1752_);
v_res_1762_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_1746_, v_name_1747_, v_type_1748_, v_val_1749_, v_k_1750_, v_nondep_boxed_1760_, v_kind_boxed_1761_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1762_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object* v_msg_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_2402__overap_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0);
v___x_2402__overap_1773_ = lean_panic_fn(v___x_1772_, v_msg_1764_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
v___x_1774_ = lean_apply_7(v___x_2402__overap_1773_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, lean_box(0));
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v_msg_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_1784_, size_t v_sz_1785_, size_t v_i_1786_, lean_object* v_bs_1787_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_usize_dec_lt(v_i_1786_, v_sz_1785_);
if (v___x_1788_ == 0)
{
return v_bs_1787_;
}
else
{
lean_object* v_v_1789_; lean_object* v___x_1790_; lean_object* v_bs_x27_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; 
v_v_1789_ = lean_array_uget(v_bs_1787_, v_i_1786_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v_bs_x27_1791_ = lean_array_uset(v_bs_1787_, v_i_1786_, v___x_1790_);
v___x_1792_ = l_Lean_instInhabitedExpr;
v___x_1793_ = lean_array_get_borrowed(v___x_1792_, v_xs_1784_, v_v_1789_);
lean_dec(v_v_1789_);
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = lean_usize_add(v_i_1786_, v___x_1794_);
lean_inc(v___x_1793_);
v___x_1796_ = lean_array_uset(v_bs_x27_1791_, v_i_1786_, v___x_1793_);
v_i_1786_ = v___x_1795_;
v_bs_1787_ = v___x_1796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_1798_, lean_object* v_sz_1799_, lean_object* v_i_1800_, lean_object* v_bs_1801_){
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1799_);
lean_dec(v_sz_1799_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1800_);
lean_dec(v_i_1800_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1798_, v_sz_boxed_1802_, v_i_boxed_1803_, v_bs_1801_);
lean_dec_ref(v_xs_1798_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_1805_, lean_object* v_i_1806_, lean_object* v_varDeps_1807_, lean_object* v_args_1808_, lean_object* v_body_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_1805_, v_i_1806_, v_varDeps_1807_, v_args_1808_, v_body_1809_, v_x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v_i_1806_);
return v_res_1818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1821_ = lean_unsigned_to_nat(30u);
v___x_1822_ = lean_unsigned_to_nat(254u);
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_1824_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1825_ = l_mkPanicMessageWithDecl(v___x_1824_, v___x_1823_, v___x_1822_, v___x_1821_, v___x_1820_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_1826_, lean_object* v_args_1827_, lean_object* v_f_1828_, lean_object* v_xs_1829_, lean_object* v_i_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_array_get_size(v_args_1827_);
v___x_1839_ = lean_nat_dec_lt(v_i_1830_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v_a_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; 
lean_dec(v_i_1830_);
lean_dec_ref(v_args_1827_);
v___x_1840_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_f_1828_, v_xs_1829_, v_varDeps_1826_, v_a_1832_);
lean_dec_ref(v_varDeps_1826_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = 1;
v___x_1843_ = l_Lean_Meta_mkLetFVars(v_xs_1829_, v_a_1841_, v___x_1839_, v___x_1839_, v___x_1842_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec_ref(v_xs_1829_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_1844_, v_a_1832_);
return v___x_1845_;
}
else
{
return v___x_1843_;
}
}
else
{
if (lean_obj_tag(v_f_1828_) == 6)
{
lean_object* v_binderName_1846_; lean_object* v_binderType_1847_; lean_object* v_body_1848_; lean_object* v_varPos_1849_; size_t v_sz_1850_; size_t v___x_1851_; lean_object* v_ys_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_binderName_1846_ = lean_ctor_get(v_f_1828_, 0);
lean_inc(v_binderName_1846_);
v_binderType_1847_ = lean_ctor_get(v_f_1828_, 1);
lean_inc_ref(v_binderType_1847_);
v_body_1848_ = lean_ctor_get(v_f_1828_, 2);
lean_inc_ref(v_body_1848_);
lean_dec_ref(v_f_1828_);
v_varPos_1849_ = lean_array_fget(v_varDeps_1826_, v_i_1830_);
v_sz_1850_ = lean_array_size(v_varPos_1849_);
v___x_1851_ = ((size_t)0ULL);
lean_inc(v_varPos_1849_);
v_ys_1852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1829_, v_sz_1850_, v___x_1851_, v_varPos_1849_);
v___x_1853_ = lean_array_fget_borrowed(v_args_1827_, v_i_1830_);
v___x_1854_ = 0;
lean_inc(v___x_1853_);
v___x_1855_ = l_Lean_Expr_betaRev(v___x_1853_, v_ys_1852_, v___x_1854_, v___x_1854_);
lean_dec_ref(v_ys_1852_);
v___x_1856_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1855_, v_a_1832_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___f_1858_; lean_object* v___x_1859_; lean_object* v_type_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
v___f_1858_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1858_, 0, v_xs_1829_);
lean_closure_set(v___f_1858_, 1, v_i_1830_);
lean_closure_set(v___f_1858_, 2, v_varDeps_1826_);
lean_closure_set(v___f_1858_, 3, v_args_1827_);
lean_closure_set(v___f_1858_, 4, v_body_1848_);
v___x_1859_ = lean_array_get_size(v_varPos_1849_);
lean_dec(v_varPos_1849_);
v_type_1860_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_1847_, v___x_1859_);
v___x_1861_ = 0;
v___x_1862_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_1846_, v_type_1860_, v_a_1857_, v___f_1858_, v___x_1839_, v___x_1861_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
return v___x_1862_;
}
else
{
lean_dec(v_varPos_1849_);
lean_dec_ref(v_body_1848_);
lean_dec_ref(v_binderType_1847_);
lean_dec(v_binderName_1846_);
lean_dec(v_i_1830_);
lean_dec_ref(v_xs_1829_);
lean_dec_ref(v_args_1827_);
lean_dec_ref(v_varDeps_1826_);
return v___x_1856_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v_i_1830_);
lean_dec_ref(v_xs_1829_);
lean_dec_ref(v_f_1828_);
lean_dec_ref(v_args_1827_);
lean_dec_ref(v_varDeps_1826_);
v___x_1863_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_1864_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1863_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_1865_, lean_object* v_i_1866_, lean_object* v_varDeps_1867_, lean_object* v_args_1868_, lean_object* v_body_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_x_1870_, v___y_1872_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = lean_array_push(v_xs_1865_, v_a_1879_);
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_nat_add(v_i_1866_, v___x_1881_);
v___x_1883_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1867_, v_args_1868_, v_body_1869_, v___x_1880_, v___x_1882_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1883_;
}
else
{
lean_dec_ref(v_body_1869_);
lean_dec_ref(v_args_1868_);
lean_dec_ref(v_varDeps_1867_);
lean_dec_ref(v_xs_1865_);
return v___x_1878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_1884_, lean_object* v_args_1885_, lean_object* v_f_1886_, lean_object* v_xs_1887_, lean_object* v_i_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1884_, v_args_1885_, v_f_1886_, v_xs_1887_, v_i_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_1897_, lean_object* v_args_1898_, lean_object* v___h_1899_, lean_object* v_f_1900_, lean_object* v_xs_1901_, lean_object* v_i_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1897_, v_args_1898_, v_f_1900_, v_xs_1901_, v_i_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_1911_, lean_object* v_args_1912_, lean_object* v___h_1913_, lean_object* v_f_1914_, lean_object* v_xs_1915_, lean_object* v_i_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_1911_, v_args_1912_, v___h_1913_, v_f_1914_, v_xs_1915_, v_i_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
return v_res_1924_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1927_ = lean_unsigned_to_nat(40u);
v___x_1928_ = lean_unsigned_to_nat(251u);
v___x_1929_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1931_ = l_mkPanicMessageWithDecl(v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 5)
{
lean_object* v_fn_1943_; lean_object* v_arg_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_fn_1943_ = lean_ctor_get(v_x_1933_, 0);
lean_inc_ref(v_fn_1943_);
v_arg_1944_ = lean_ctor_get(v_x_1933_, 1);
lean_inc_ref(v_arg_1944_);
lean_dec_ref(v_x_1933_);
v___x_1945_ = lean_array_set(v_x_1934_, v_x_1935_, v_arg_1944_);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = lean_nat_sub(v_x_1935_, v___x_1946_);
lean_dec(v_x_1935_);
v_x_1933_ = v_fn_1943_;
v_x_1934_ = v___x_1945_;
v_x_1935_ = v___x_1947_;
goto _start;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
lean_dec(v_x_1935_);
v___x_1949_ = lean_array_get_size(v_x_1934_);
v___x_1950_ = lean_array_get_size(v_varDeps_1932_);
v___x_1951_ = lean_nat_dec_eq(v___x_1949_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec_ref(v_x_1934_);
lean_dec_ref(v_x_1933_);
lean_dec_ref(v_varDeps_1932_);
v___x_1952_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_1953_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1952_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_1956_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1932_, v_x_1934_, v_x_1933_, v___x_1955_, v___x_1954_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_1957_, v_x_1958_, v_x_1959_, v_x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_1969_; lean_object* v_dummy_1970_; 
v___x_1969_ = lean_box(0);
v_dummy_1970_ = l_Lean_Expr_sort___override(v___x_1969_);
return v_dummy_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_1971_, lean_object* v_varDeps_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_dummy_1980_; lean_object* v_nargs_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_dummy_1980_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_1981_ = l_Lean_Expr_getAppNumArgs(v_e_1971_);
lean_inc(v_nargs_1981_);
v___x_1982_ = lean_mk_array(v_nargs_1981_, v_dummy_1980_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_sub(v_nargs_1981_, v___x_1983_);
lean_dec(v_nargs_1981_);
v___x_1985_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_1972_, v_e_1971_, v___x_1982_, v___x_1984_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_1986_, lean_object* v_varDeps_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_1986_, v_varDeps_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_1996_, lean_object* v_b_1997_){
_start:
{
lean_object* v_snd_1999_; lean_object* v_fst_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2033_; 
v_snd_1999_ = lean_ctor_get(v_b_1997_, 1);
v_fst_2000_ = lean_ctor_get(v_b_1997_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_b_1997_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2002_ = v_b_1997_;
v_isShared_2003_ = v_isSharedCheck_2033_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_1999_);
lean_inc(v_fst_2000_);
lean_dec(v_b_1997_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2033_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2032_; 
v_fst_2004_ = lean_ctor_get(v_snd_1999_, 0);
v_snd_2005_ = lean_ctor_get(v_snd_1999_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_snd_1999_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2007_ = v_snd_1999_;
v_isShared_2008_ = v_isSharedCheck_2032_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_dec(v_snd_1999_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2032_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = lean_nat_dec_lt(v___x_2009_, v_fst_2004_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2012_; 
if (v_isShared_2008_ == 0)
{
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_fst_2004_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_snd_2005_);
v___x_2012_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2012_);
v___x_2014_ = v___x_2002_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_fst_2000_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_sub(v_fst_2004_, v___x_2018_);
lean_dec(v_fst_2004_);
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_array_get_borrowed(v___x_2020_, v_argUnivs_1996_, v___x_2019_);
lean_inc(v___x_2021_);
v___x_2022_ = l_Lean_mkLevelIMax_x27(v___x_2021_, v_fst_2000_);
v___x_2023_ = l_Lean_Level_normalize(v___x_2022_);
lean_dec(v___x_2022_);
lean_inc(v___x_2023_);
v___x_2024_ = lean_array_push(v_snd_2005_, v___x_2023_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2024_);
lean_ctor_set(v___x_2007_, 0, v___x_2019_);
v___x_2026_ = v___x_2007_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2026_);
lean_ctor_set(v___x_2002_, 0, v___x_2023_);
v___x_2028_ = v___x_2002_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
v_b_1997_ = v___x_2028_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2034_, v_b_2035_);
lean_dec_ref(v_argUnivs_2034_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2040_, lean_object* v_argUnivs_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
if (lean_obj_tag(v_type_2040_) == 7)
{
lean_object* v_binderType_2049_; lean_object* v_body_2050_; lean_object* v___x_2051_; 
v_binderType_2049_ = lean_ctor_get(v_type_2040_, 1);
lean_inc_ref(v_binderType_2049_);
v_body_2050_ = lean_ctor_get(v_type_2040_, 2);
lean_inc_ref(v_body_2050_);
lean_dec_ref(v_type_2040_);
v___x_2051_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2049_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = lean_array_push(v_argUnivs_2041_, v_a_2052_);
v_type_2040_ = v_body_2050_;
v_argUnivs_2041_ = v___x_2053_;
goto _start;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_body_2050_);
lean_dec_ref(v_argUnivs_2041_);
v_a_2055_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2051_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2051_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2040_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = lean_array_get_size(v_argUnivs_2041_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_a_2064_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2041_, v___x_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2088_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2088_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2088_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_snd_2074_; lean_object* v_snd_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2086_; 
v_snd_2074_ = lean_ctor_get(v_a_2070_, 1);
lean_inc(v_snd_2074_);
lean_dec(v_a_2070_);
v_snd_2075_ = lean_ctor_get(v_snd_2074_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_snd_2074_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_snd_2074_, 0);
lean_dec(v_unused_2087_);
v___x_2077_ = v_snd_2074_;
v_isShared_2078_ = v_isSharedCheck_2086_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_snd_2075_);
lean_dec(v_snd_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2086_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = l_Array_reverse___redArg(v_snd_2075_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v___x_2079_);
lean_ctor_set(v___x_2077_, 0, v_argUnivs_2041_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_argUnivs_2041_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2081_);
v___x_2083_ = v___x_2072_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_argUnivs_2041_);
v_a_2089_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2069_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2069_);
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
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_argUnivs_2041_);
v_a_2097_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2063_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2063_);
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
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2105_, lean_object* v_argUnivs_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2105_, v_argUnivs_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2115_, lean_object* v_b_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2115_, v_b_2116_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2125_, v_b_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec_ref(v_argUnivs_2125_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2144_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2135_, v___x_2143_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2154_, lean_object* v_argUnivs_2155_, lean_object* v_declName_2156_, lean_object* v_fType_2157_, lean_object* v_i_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v_00_u03b1_2161_; lean_object* v_00_u03b2_2162_; lean_object* v_u_2163_; lean_object* v_v_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2160_ = lean_box(0);
v_00_u03b1_2161_ = l_Lean_Expr_bindingDomain_x21(v_fType_2157_);
v_00_u03b2_2162_ = l_Lean_Expr_bindingBody_x21(v_fType_2157_);
v_u_2163_ = lean_array_get_borrowed(v___x_2160_, v_argUnivs_2155_, v_i_2158_);
v_v_2164_ = lean_array_get_borrowed(v___x_2160_, v_fnUnivs_2154_, v_i_2158_);
v___x_2165_ = lean_box(0);
lean_inc(v_v_2164_);
v___x_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2166_, 0, v_v_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
lean_inc(v_u_2163_);
v___x_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_u_2163_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = l_Lean_mkConst(v_declName_2156_, v___x_2167_);
v___x_2169_ = l_Lean_mkAppB(v___x_2168_, v_00_u03b1_2161_, v_00_u03b2_2162_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2171_, lean_object* v_argUnivs_2172_, lean_object* v_declName_2173_, lean_object* v_fType_2174_, lean_object* v_i_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2171_, v_argUnivs_2172_, v_declName_2173_, v_fType_2174_, v_i_2175_);
lean_dec(v_i_2175_);
lean_dec_ref(v_fType_2174_);
lean_dec_ref(v_argUnivs_2172_);
lean_dec_ref(v_fnUnivs_2171_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2178_, lean_object* v_argUnivs_2179_, lean_object* v_declName_2180_, lean_object* v_fType_2181_, lean_object* v_i_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2178_, v_argUnivs_2179_, v_declName_2180_, v_fType_2181_, v_i_2182_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2191_, lean_object* v_argUnivs_2192_, lean_object* v_declName_2193_, lean_object* v_fType_2194_, lean_object* v_i_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2191_, v_argUnivs_2192_, v_declName_2193_, v_fType_2194_, v_i_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_i_2195_);
lean_dec_ref(v_fType_2194_);
lean_dec_ref(v_argUnivs_2192_);
lean_dec_ref(v_fnUnivs_2191_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2204_, lean_object* v_a_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___y_2214_; lean_object* v___x_2217_; uint8_t v_debug_2218_; 
v___x_2217_ = lean_st_ref_get(v___y_2207_);
v_debug_2218_ = lean_ctor_get_uint8(v___x_2217_, sizeof(void*)*8);
lean_dec(v___x_2217_);
if (v_debug_2218_ == 0)
{
v___y_2214_ = v___y_2207_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2219_; 
lean_inc_ref(v_f_2204_);
v___x_2219_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2204_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref(v___x_2219_);
lean_inc_ref(v_a_2205_);
v___x_2220_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_dec_ref(v___x_2220_);
v___y_2214_ = v___y_2207_;
goto v___jp_2213_;
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_f_2204_);
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_f_2204_);
v_a_2229_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2219_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2219_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
v___jp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = l_Lean_Expr_app___override(v_f_2204_, v_a_2205_);
v___x_2216_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2215_, v___y_2214_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2237_, lean_object* v_a_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2237_, v_a_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2247_, lean_object* v_a_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2247_, v_a_2248_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2260_, lean_object* v_a_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2260_, v_a_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
return v_res_2272_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_15370__overap_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15370__overap_2286_ = lean_panic_fn(v___x_2285_, v_msg_2274_);
lean_inc(v___y_2283_);
lean_inc_ref(v___y_2282_);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
v___x_2287_ = lean_apply_10(v___x_15370__overap_2286_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, lean_box(0));
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
return v_res_2299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_2311_ = lean_unsigned_to_nat(11u);
v___x_2312_ = lean_unsigned_to_nat(346u);
v___x_2313_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2314_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_2315_ = l_mkPanicMessageWithDecl(v___x_2314_, v___x_2313_, v___x_2312_, v___x_2311_, v___x_2310_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2316_, lean_object* v_fnUnivs_2317_, lean_object* v_argUnivs_2318_, lean_object* v_simpBody_2319_, lean_object* v_e_2320_, lean_object* v_i_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
switch(lean_obj_tag(v_e_2320_))
{
case 5:
{
lean_object* v_fn_2332_; lean_object* v_arg_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_fn_2332_ = lean_ctor_get(v_e_2320_, 0);
lean_inc_ref(v_fn_2332_);
v_arg_2333_ = lean_ctor_get(v_e_2320_, 1);
lean_inc_ref(v_arg_2333_);
lean_dec_ref(v_e_2320_);
v___x_2334_ = lean_unsigned_to_nat(1u);
v___x_2335_ = lean_nat_sub(v_i_2321_, v___x_2334_);
lean_inc_ref(v_fn_2332_);
v___x_2336_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2316_, v_fnUnivs_2317_, v_argUnivs_2318_, v_simpBody_2319_, v_fn_2332_, v___x_2335_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2457_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2457_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2457_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_fst_2341_; lean_object* v_snd_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2456_; 
v_fst_2341_ = lean_ctor_get(v_a_2337_, 0);
v_snd_2342_ = lean_ctor_get(v_a_2337_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_a_2337_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2344_ = v_a_2337_;
v_isShared_2345_ = v_isSharedCheck_2456_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_snd_2342_);
lean_inc(v_fst_2341_);
lean_dec(v_a_2337_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2456_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_r_2347_; lean_object* v___x_2355_; 
lean_inc(v_a_2330_);
lean_inc_ref(v_a_2329_);
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
lean_inc(v_a_2324_);
lean_inc_ref(v_a_2323_);
lean_inc(v_a_2322_);
lean_inc_ref(v_arg_2333_);
v___x_2355_ = lean_sym_simp(v_arg_2333_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; uint8_t v___y_2358_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
if (lean_obj_tag(v_fst_2341_) == 0)
{
if (lean_obj_tag(v_a_2356_) == 0)
{
uint8_t v_contextDependent_2360_; 
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_fn_2332_);
v_contextDependent_2360_ = lean_ctor_get_uint8(v_fst_2341_, 1);
lean_dec_ref(v_fst_2341_);
if (v_contextDependent_2360_ == 0)
{
uint8_t v_contextDependent_2361_; 
v_contextDependent_2361_ = lean_ctor_get_uint8(v_a_2356_, 1);
lean_dec_ref(v_a_2356_);
v___y_2358_ = v_contextDependent_2361_;
goto v___jp_2357_;
}
else
{
lean_dec_ref(v_a_2356_);
v___y_2358_ = v_contextDependent_2360_;
goto v___jp_2357_;
}
}
else
{
uint8_t v_contextDependent_2362_; lean_object* v_e_x27_2363_; lean_object* v_proof_2364_; uint8_t v_contextDependent_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2389_; 
v_contextDependent_2362_ = lean_ctor_get_uint8(v_fst_2341_, 1);
lean_dec_ref(v_fst_2341_);
v_e_x27_2363_ = lean_ctor_get(v_a_2356_, 0);
v_proof_2364_ = lean_ctor_get(v_a_2356_, 1);
v_contextDependent_2365_ = lean_ctor_get_uint8(v_a_2356_, sizeof(void*)*2 + 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2356_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2367_ = v_a_2356_;
v_isShared_2368_ = v_isSharedCheck_2389_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_proof_2364_);
lean_inc(v_e_x27_2363_);
lean_dec(v_a_2356_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2389_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; 
lean_inc_ref(v_e_x27_2363_);
lean_inc_ref(v_fn_2332_);
v___x_2369_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2332_, v_e_x27_2363_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v_a_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; uint8_t v___y_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2372_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2317_, v_argUnivs_2318_, v___x_2371_, v_snd_2342_, v_i_2321_);
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = l_Lean_mkApp4(v_a_2373_, v_arg_2333_, v_e_x27_2363_, v_fn_2332_, v_proof_2364_);
v___x_2375_ = 0;
if (v_contextDependent_2362_ == 0)
{
v___y_2377_ = v_contextDependent_2365_;
goto v___jp_2376_;
}
else
{
v___y_2377_ = v_contextDependent_2362_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 1, v___x_2374_);
lean_ctor_set(v___x_2367_, 0, v_a_2370_);
v___x_2379_ = v___x_2367_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2370_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*2, v___x_2375_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*2 + 1, v___y_2377_);
v_r_2347_ = v___x_2379_;
goto v___jp_2346_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_del_object(v___x_2367_);
lean_dec_ref(v_proof_2364_);
lean_dec_ref(v_e_x27_2363_);
lean_del_object(v___x_2344_);
lean_dec(v_snd_2342_);
lean_del_object(v___x_2339_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_fn_2332_);
v_a_2381_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2369_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2369_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2356_) == 0)
{
lean_object* v_e_x27_2390_; lean_object* v_proof_2391_; uint8_t v_contextDependent_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2417_; 
v_e_x27_2390_ = lean_ctor_get(v_fst_2341_, 0);
v_proof_2391_ = lean_ctor_get(v_fst_2341_, 1);
v_contextDependent_2392_ = lean_ctor_get_uint8(v_fst_2341_, sizeof(void*)*2 + 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_fst_2341_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2394_ = v_fst_2341_;
v_isShared_2395_ = v_isSharedCheck_2417_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_proof_2391_);
lean_inc(v_e_x27_2390_);
lean_dec(v_fst_2341_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2417_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
uint8_t v_contextDependent_2396_; lean_object* v___x_2397_; 
v_contextDependent_2396_ = lean_ctor_get_uint8(v_a_2356_, 1);
lean_dec_ref(v_a_2356_);
lean_inc_ref(v_arg_2333_);
lean_inc_ref(v_e_x27_2390_);
v___x_2397_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2390_, v_arg_2333_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_a_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; uint8_t v___y_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2400_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2317_, v_argUnivs_2318_, v___x_2399_, v_snd_2342_, v_i_2321_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = l_Lean_mkApp4(v_a_2401_, v_fn_2332_, v_e_x27_2390_, v_proof_2391_, v_arg_2333_);
v___x_2403_ = 0;
if (v_contextDependent_2392_ == 0)
{
v___y_2405_ = v_contextDependent_2396_;
goto v___jp_2404_;
}
else
{
v___y_2405_ = v_contextDependent_2392_;
goto v___jp_2404_;
}
v___jp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v___x_2402_);
lean_ctor_set(v___x_2394_, 0, v_a_2398_);
v___x_2407_ = v___x_2394_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2398_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*2, v___x_2403_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*2 + 1, v___y_2405_);
v_r_2347_ = v___x_2407_;
goto v___jp_2346_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_del_object(v___x_2394_);
lean_dec_ref(v_proof_2391_);
lean_dec_ref(v_e_x27_2390_);
lean_del_object(v___x_2344_);
lean_dec(v_snd_2342_);
lean_del_object(v___x_2339_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_fn_2332_);
v_a_2409_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2397_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2397_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2418_; lean_object* v_proof_2419_; uint8_t v_contextDependent_2420_; lean_object* v_e_x27_2421_; lean_object* v_proof_2422_; uint8_t v_contextDependent_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2447_; 
v_e_x27_2418_ = lean_ctor_get(v_fst_2341_, 0);
lean_inc_ref(v_e_x27_2418_);
v_proof_2419_ = lean_ctor_get(v_fst_2341_, 1);
lean_inc_ref(v_proof_2419_);
v_contextDependent_2420_ = lean_ctor_get_uint8(v_fst_2341_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_2341_);
v_e_x27_2421_ = lean_ctor_get(v_a_2356_, 0);
v_proof_2422_ = lean_ctor_get(v_a_2356_, 1);
v_contextDependent_2423_ = lean_ctor_get_uint8(v_a_2356_, sizeof(void*)*2 + 1);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_a_2356_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2425_ = v_a_2356_;
v_isShared_2426_ = v_isSharedCheck_2447_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_proof_2422_);
lean_inc(v_e_x27_2421_);
lean_dec(v_a_2356_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2447_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; 
lean_inc_ref(v_e_x27_2421_);
lean_inc_ref(v_e_x27_2418_);
v___x_2427_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2418_, v_e_x27_2421_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v_a_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; uint8_t v___y_2435_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref(v___x_2427_);
v___x_2429_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2430_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2317_, v_argUnivs_2318_, v___x_2429_, v_snd_2342_, v_i_2321_);
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v___x_2430_);
v___x_2432_ = l_Lean_mkApp6(v_a_2431_, v_fn_2332_, v_e_x27_2418_, v_arg_2333_, v_e_x27_2421_, v_proof_2419_, v_proof_2422_);
v___x_2433_ = 0;
if (v_contextDependent_2420_ == 0)
{
v___y_2435_ = v_contextDependent_2423_;
goto v___jp_2434_;
}
else
{
v___y_2435_ = v_contextDependent_2420_;
goto v___jp_2434_;
}
v___jp_2434_:
{
lean_object* v___x_2437_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v___x_2432_);
lean_ctor_set(v___x_2425_, 0, v_a_2428_);
v___x_2437_ = v___x_2425_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2428_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*2, v___x_2433_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*2 + 1, v___y_2435_);
v_r_2347_ = v___x_2437_;
goto v___jp_2346_;
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_del_object(v___x_2425_);
lean_dec_ref(v_proof_2422_);
lean_dec_ref(v_e_x27_2421_);
lean_dec_ref(v_proof_2419_);
lean_dec_ref(v_e_x27_2418_);
lean_del_object(v___x_2344_);
lean_dec(v_snd_2342_);
lean_del_object(v___x_2339_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_fn_2332_);
v_a_2439_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2427_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2427_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
v___jp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2358_);
v_r_2347_ = v___x_2359_;
goto v___jp_2346_;
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_del_object(v___x_2344_);
lean_dec(v_snd_2342_);
lean_dec(v_fst_2341_);
lean_del_object(v___x_2339_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_fn_2332_);
v_a_2448_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2355_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2355_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = l_Lean_Expr_bindingBody_x21(v_snd_2342_);
lean_dec(v_snd_2342_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v___x_2348_);
lean_ctor_set(v___x_2344_, 0, v_r_2347_);
v___x_2350_ = v___x_2344_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_r_2347_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2350_);
v___x_2352_ = v___x_2339_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_fn_2332_);
return v___x_2336_;
}
}
case 6:
{
lean_object* v___x_2458_; 
lean_inc(v_a_2330_);
lean_inc_ref(v_a_2329_);
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
lean_inc(v_a_2324_);
lean_inc_ref(v_a_2323_);
lean_inc(v_a_2322_);
v___x_2458_ = lean_apply_11(v_simpBody_2319_, v_e_2320_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, lean_box(0));
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_a_2459_);
lean_ctor_set(v___x_2463_, 1, v_fType_2316_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2463_);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v_fType_2316_);
v_a_2468_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2458_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2458_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
default: 
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec_ref(v_e_2320_);
lean_dec_ref(v_simpBody_2319_);
lean_dec_ref(v_fType_2316_);
v___x_2476_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2477_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2476_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2478_, lean_object* v_fnUnivs_2479_, lean_object* v_argUnivs_2480_, lean_object* v_simpBody_2481_, lean_object* v_e_2482_, lean_object* v_i_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2478_, v_fnUnivs_2479_, v_argUnivs_2480_, v_simpBody_2481_, v_e_2482_, v_i_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec(v_i_2483_);
lean_dec_ref(v_argUnivs_2480_);
lean_dec_ref(v_fnUnivs_2479_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2495_, lean_object* v_fType_2496_, lean_object* v_fnUnivs_2497_, lean_object* v_argUnivs_2498_, lean_object* v_simpBody_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_numArgs_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_numArgs_2510_ = lean_array_get_size(v_argUnivs_2498_);
v___x_2511_ = lean_unsigned_to_nat(1u);
v___x_2512_ = lean_nat_sub(v_numArgs_2510_, v___x_2511_);
v___x_2513_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2496_, v_fnUnivs_2497_, v_argUnivs_2498_, v_simpBody_2499_, v_e_2495_, v___x_2512_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v___x_2512_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_fst_2518_; lean_object* v___x_2520_; 
v_fst_2518_ = lean_ctor_get(v_a_2514_, 0);
lean_inc(v_fst_2518_);
lean_dec(v_a_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v_fst_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_fst_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_a_2523_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2513_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2513_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2531_, lean_object* v_fType_2532_, lean_object* v_fnUnivs_2533_, lean_object* v_argUnivs_2534_, lean_object* v_simpBody_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2531_, v_fType_2532_, v_fnUnivs_2533_, v_argUnivs_2534_, v_simpBody_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_argUnivs_2534_);
lean_dec_ref(v_fnUnivs_2533_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2551_, lean_object* v_simpBody_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; 
lean_inc_ref(v_e_2551_);
v___x_2563_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2551_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v_00_u03b1_2565_; lean_object* v_u_2566_; lean_object* v_e_2567_; lean_object* v_h_2568_; lean_object* v_varDeps_2569_; lean_object* v_fType_2570_; lean_object* v___x_2571_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref(v___x_2563_);
v_00_u03b1_2565_ = lean_ctor_get(v_a_2564_, 0);
lean_inc_ref(v_00_u03b1_2565_);
v_u_2566_ = lean_ctor_get(v_a_2564_, 1);
lean_inc(v_u_2566_);
v_e_2567_ = lean_ctor_get(v_a_2564_, 2);
lean_inc_ref(v_e_2567_);
v_h_2568_ = lean_ctor_get(v_a_2564_, 3);
lean_inc_ref(v_h_2568_);
v_varDeps_2569_ = lean_ctor_get(v_a_2564_, 4);
lean_inc_ref(v_varDeps_2569_);
v_fType_2570_ = lean_ctor_get(v_a_2564_, 5);
lean_inc_ref(v_fType_2570_);
lean_dec(v_a_2564_);
lean_inc_ref(v_fType_2570_);
v___x_2571_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2570_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v_argUnivs_2573_; lean_object* v_fnUnivs_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2642_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v_argUnivs_2573_ = lean_ctor_get(v_a_2572_, 0);
v_fnUnivs_2574_ = lean_ctor_get(v_a_2572_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_a_2572_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2576_ = v_a_2572_;
v_isShared_2577_ = v_isSharedCheck_2642_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_fnUnivs_2574_);
lean_inc(v_argUnivs_2573_);
lean_dec(v_a_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2642_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; 
lean_inc_ref(v_e_2567_);
v___x_2578_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2567_, v_fType_2570_, v_fnUnivs_2574_, v_argUnivs_2573_, v_simpBody_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec_ref(v_argUnivs_2573_);
lean_dec_ref(v_fnUnivs_2574_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2633_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2633_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2633_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
if (lean_obj_tag(v_a_2579_) == 0)
{
uint8_t v_contextDependent_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_del_object(v___x_2576_);
lean_dec_ref(v_varDeps_2569_);
lean_dec_ref(v_h_2568_);
lean_dec_ref(v_e_2567_);
lean_dec_ref(v_e_2551_);
v_contextDependent_2583_ = lean_ctor_get_uint8(v_a_2579_, 1);
lean_dec_ref(v_a_2579_);
v___x_2584_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2583_);
v___x_2585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v_00_u03b1_2565_);
lean_ctor_set(v___x_2585_, 2, v_u_2566_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2585_);
v___x_2587_ = v___x_2581_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
else
{
lean_object* v_e_x27_2589_; lean_object* v_proof_2590_; uint8_t v_contextDependent_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2632_; 
lean_del_object(v___x_2581_);
v_e_x27_2589_ = lean_ctor_get(v_a_2579_, 0);
v_proof_2590_ = lean_ctor_get(v_a_2579_, 1);
v_contextDependent_2591_ = lean_ctor_get_uint8(v_a_2579_, sizeof(void*)*2 + 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2579_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2593_ = v_a_2579_;
v_isShared_2594_ = v_isSharedCheck_2632_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_proof_2590_);
lean_inc(v_e_x27_2589_);
lean_dec(v_a_2579_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2632_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2596_ = lean_box(0);
lean_inc(v_u_2566_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 1);
lean_ctor_set(v___x_2576_, 1, v___x_2596_);
lean_ctor_set(v___x_2576_, 0, v_u_2566_);
v___x_2598_ = v___x_2576_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_u_2566_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_inc_ref(v___x_2598_);
v___x_2599_ = l_Lean_mkConst(v___x_2595_, v___x_2598_);
lean_inc_ref(v_e_x27_2589_);
lean_inc_ref(v_e_2551_);
lean_inc_ref(v_00_u03b1_2565_);
lean_inc_ref(v___x_2599_);
v___x_2600_ = l_Lean_mkApp6(v___x_2599_, v_00_u03b1_2565_, v_e_2551_, v_e_2567_, v_e_x27_2589_, v_h_2568_, v_proof_2590_);
lean_inc_ref(v_e_x27_2589_);
v___x_2601_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2589_, v_varDeps_2569_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2622_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2616_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2598_);
v___x_2607_ = l_Lean_mkConst(v___x_2606_, v___x_2598_);
lean_inc(v_a_2602_);
lean_inc_ref(v_e_x27_2589_);
lean_inc_ref(v_00_u03b1_2565_);
v___x_2608_ = l_Lean_mkApp3(v___x_2607_, v_00_u03b1_2565_, v_e_x27_2589_, v_a_2602_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2610_ = l_Lean_mkConst(v___x_2609_, v___x_2598_);
lean_inc_ref(v_e_x27_2589_);
lean_inc_ref(v_00_u03b1_2565_);
v___x_2611_ = l_Lean_mkAppB(v___x_2610_, v_00_u03b1_2565_, v_e_x27_2589_);
v___x_2612_ = l_Lean_Meta_mkExpectedPropHint(v___x_2611_, v___x_2608_);
lean_inc(v_a_2602_);
lean_inc_ref(v_00_u03b1_2565_);
v___x_2613_ = l_Lean_mkApp6(v___x_2599_, v_00_u03b1_2565_, v_e_2551_, v_e_x27_2589_, v_a_2602_, v___x_2600_, v___x_2612_);
v___x_2614_ = 0;
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2613_);
lean_ctor_set(v___x_2593_, 0, v_a_2602_);
v___x_2616_ = v___x_2593_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2602_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___x_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2621_, sizeof(void*)*2 + 1, v_contextDependent_2591_);
v___x_2616_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*2, v___x_2614_);
v___x_2617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v_00_u03b1_2565_);
lean_ctor_set(v___x_2617_, 2, v_u_2566_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2617_);
v___x_2619_ = v___x_2604_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v___x_2600_);
lean_dec_ref(v___x_2599_);
lean_dec_ref(v___x_2598_);
lean_del_object(v___x_2593_);
lean_dec_ref(v_e_x27_2589_);
lean_dec(v_u_2566_);
lean_dec_ref(v_00_u03b1_2565_);
lean_dec_ref(v_e_2551_);
v_a_2623_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2601_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2601_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
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
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_del_object(v___x_2576_);
lean_dec_ref(v_varDeps_2569_);
lean_dec_ref(v_h_2568_);
lean_dec_ref(v_e_2567_);
lean_dec(v_u_2566_);
lean_dec_ref(v_00_u03b1_2565_);
lean_dec_ref(v_e_2551_);
v_a_2634_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2578_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2578_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_fType_2570_);
lean_dec_ref(v_varDeps_2569_);
lean_dec_ref(v_h_2568_);
lean_dec_ref(v_e_2567_);
lean_dec(v_u_2566_);
lean_dec_ref(v_00_u03b1_2565_);
lean_dec_ref(v_simpBody_2552_);
lean_dec_ref(v_e_2551_);
v_a_2643_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2571_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2571_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v_simpBody_2552_);
lean_dec_ref(v_e_2551_);
v_a_2651_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2563_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2563_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2659_, lean_object* v_simpBody_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2659_, v_simpBody_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2672_, lean_object* v_simpBody_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2672_, v_simpBody_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2693_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2693_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2693_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_result_2689_; lean_object* v___x_2691_; 
v_result_2689_ = lean_ctor_get(v_a_2685_, 0);
lean_inc_ref(v_result_2689_);
lean_dec(v_a_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v_result_2689_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_result_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2684_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2684_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2702_, lean_object* v_simpBody_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2702_, v_simpBody_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2715_, lean_object* v_simpBody_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2727_; 
lean_inc_ref(v_e_u2081_2715_);
v___x_2727_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2715_, v_simpBody_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v_result_2729_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref(v___x_2727_);
v_result_2729_ = lean_ctor_get(v_a_2728_, 0);
lean_inc_ref(v_result_2729_);
if (lean_obj_tag(v_result_2729_) == 0)
{
lean_object* v_00_u03b1_2730_; lean_object* v_u_2731_; uint8_t v_contextDependent_2732_; lean_object* v___x_2733_; 
v_00_u03b1_2730_ = lean_ctor_get(v_a_2728_, 1);
lean_inc_ref(v_00_u03b1_2730_);
v_u_2731_ = lean_ctor_get(v_a_2728_, 2);
lean_inc(v_u_2731_);
lean_dec(v_a_2728_);
v_contextDependent_2732_ = lean_ctor_get_uint8(v_result_2729_, 1);
lean_dec_ref(v_result_2729_);
lean_inc_ref(v_e_u2081_2715_);
v___x_2733_ = l_Lean_Meta_zetaUnused(v_e_u2081_2715_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2752_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2752_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2752_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
uint8_t v___x_2738_; 
v___x_2738_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_u2081_2715_, v_a_2734_);
lean_dec_ref(v_e_u2081_2715_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2740_ = lean_box(0);
v___x_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_u_2731_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_mkConst(v___x_2739_, v___x_2741_);
lean_inc(v_a_2734_);
v___x_2743_ = l_Lean_mkAppB(v___x_2742_, v_00_u03b1_2730_, v_a_2734_);
v___x_2744_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2744_, 0, v_a_2734_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*2, v___x_2738_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*2 + 1, v_contextDependent_2732_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2744_);
v___x_2746_ = v___x_2736_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
else
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
lean_dec(v_a_2734_);
lean_dec(v_u_2731_);
lean_dec_ref(v_00_u03b1_2730_);
v___x_2748_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2732_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2748_);
v___x_2750_ = v___x_2736_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_u_2731_);
lean_dec_ref(v_00_u03b1_2730_);
lean_dec_ref(v_e_u2081_2715_);
v_a_2753_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2733_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2733_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_00_u03b1_2761_; lean_object* v_u_2762_; lean_object* v_e_x27_2763_; lean_object* v_proof_2764_; uint8_t v_contextDependent_2765_; lean_object* v___x_2766_; 
v_00_u03b1_2761_ = lean_ctor_get(v_a_2728_, 1);
lean_inc_ref(v_00_u03b1_2761_);
v_u_2762_ = lean_ctor_get(v_a_2728_, 2);
lean_inc(v_u_2762_);
lean_dec(v_a_2728_);
v_e_x27_2763_ = lean_ctor_get(v_result_2729_, 0);
v_proof_2764_ = lean_ctor_get(v_result_2729_, 1);
v_contextDependent_2765_ = lean_ctor_get_uint8(v_result_2729_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_2763_);
v___x_2766_ = l_Lean_Meta_zetaUnused(v_e_x27_2763_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2795_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2795_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2795_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint8_t v___x_2771_; 
v___x_2771_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_2763_, v_a_2767_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2789_; 
lean_inc_ref(v_proof_2764_);
lean_inc_ref(v_e_x27_2763_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_result_2729_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; lean_object* v_unused_2791_; 
v_unused_2790_ = lean_ctor_get(v_result_2729_, 1);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_result_2729_, 0);
lean_dec(v_unused_2791_);
v___x_2773_ = v_result_2729_;
v_isShared_2774_ = v_isSharedCheck_2789_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_result_2729_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2789_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_u_2762_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
lean_inc_ref(v___x_2777_);
v___x_2778_ = l_Lean_mkConst(v___x_2775_, v___x_2777_);
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2780_ = l_Lean_mkConst(v___x_2779_, v___x_2777_);
lean_inc(v_a_2767_);
lean_inc_ref(v_00_u03b1_2761_);
v___x_2781_ = l_Lean_mkAppB(v___x_2780_, v_00_u03b1_2761_, v_a_2767_);
lean_inc(v_a_2767_);
v___x_2782_ = l_Lean_mkApp6(v___x_2778_, v_00_u03b1_2761_, v_e_u2081_2715_, v_e_x27_2763_, v_a_2767_, v_proof_2764_, v___x_2781_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2782_);
lean_ctor_set(v___x_2773_, 0, v_a_2767_);
v___x_2784_ = v___x_2773_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2767_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2782_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*2 + 1, v_contextDependent_2765_);
v___x_2784_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*2, v___x_2771_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2784_);
v___x_2786_ = v___x_2769_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
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
else
{
lean_object* v___x_2793_; 
lean_dec(v_a_2767_);
lean_dec(v_u_2762_);
lean_dec_ref(v_00_u03b1_2761_);
lean_dec_ref(v_e_u2081_2715_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v_result_2729_);
v___x_2793_ = v___x_2769_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_result_2729_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_u_2762_);
lean_dec_ref(v_00_u03b1_2761_);
lean_dec_ref(v_result_2729_);
lean_dec_ref(v_e_u2081_2715_);
v_a_2796_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2766_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2766_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v_e_u2081_2715_);
v_a_2804_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2727_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2727_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_2812_, lean_object* v_simpBody_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_2812_, v_simpBody_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_2825_, lean_object* v_e_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_Expr_letNondep_x21(v_e_2826_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec_ref(v_e_2826_);
lean_dec_ref(v_simpBody_2825_);
v___x_2838_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2838_, 0, v___x_2837_);
lean_ctor_set_uint8(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_2826_, v_simpBody_2825_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
return v___x_2840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_2841_, lean_object* v_e_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_2841_, v_e_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_2867_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_2866_, v_e_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
return v_res_2879_;
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
