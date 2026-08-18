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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2;
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__4;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Sym.Simp.Have"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.elimAuxApps"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: numArgs == expectedNumArgs\n            "};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_cellCount_158_; lean_object* v___x_159_; 
v_cellCount_158_ = lean_unsigned_to_nat(16u);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_158_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v_cellCount_160_; lean_object* v___x_161_; 
v_cellCount_160_ = lean_unsigned_to_nat(16u);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_160_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v___x_163_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__4(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3));
v___x_169_ = lean_box(1);
v___x_170_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_172_, lean_object* v_fvarIdToPos_173_){
_start:
{
lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___x_182_; lean_object* v___y_184_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_s_192_; lean_object* v_fvarIds_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3));
v___x_191_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__4, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__4);
v_s_192_ = l_Lean_collectFVars(v___x_191_, v_e_172_);
v_fvarIds_193_ = lean_ctor_get(v_s_192_, 2);
lean_inc_ref(v_fvarIds_193_);
lean_dec_ref(v_s_192_);
v___x_194_ = lean_array_get_size(v_fvarIds_193_);
v___x_195_ = lean_nat_dec_lt(v___x_182_, v___x_194_);
if (v___x_195_ == 0)
{
lean_dec_ref(v_fvarIds_193_);
v___y_184_ = v___x_190_;
goto v___jp_183_;
}
else
{
uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_le(v___x_194_, v___x_194_);
if (v___x_196_ == 0)
{
if (v___x_195_ == 0)
{
lean_dec_ref(v_fvarIds_193_);
v___y_184_ = v___x_190_;
goto v___jp_183_;
}
else
{
size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((size_t)0ULL);
v___x_198_ = lean_usize_of_nat(v___x_194_);
v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_173_, v_fvarIds_193_, v___x_197_, v___x_198_, v___x_190_);
lean_dec_ref(v_fvarIds_193_);
v___y_184_ = v___x_199_;
goto v___jp_183_;
}
}
else
{
size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((size_t)0ULL);
v___x_201_ = lean_usize_of_nat(v___x_194_);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_173_, v_fvarIds_193_, v___x_200_, v___x_201_, v___x_190_);
lean_dec_ref(v_fvarIds_193_);
v___y_184_ = v___x_202_;
goto v___jp_183_;
}
}
v___jp_174_:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_le(v___y_178_, v___y_177_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec(v___y_177_);
lean_inc(v___y_178_);
v___x_180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_173_, v___y_175_, v___y_176_, v___y_178_, v___y_178_);
lean_dec(v___y_178_);
lean_dec(v___y_175_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_173_, v___y_175_, v___y_176_, v___y_178_, v___y_177_);
lean_dec(v___y_177_);
lean_dec(v___y_175_);
return v___x_181_;
}
}
v___jp_183_:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_array_get_size(v___y_184_);
v___x_186_ = lean_nat_dec_eq(v___x_185_, v___x_182_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_sub(v___x_185_, v___x_187_);
v___x_189_ = lean_nat_dec_le(v___x_182_, v___x_188_);
if (v___x_189_ == 0)
{
lean_inc(v___x_188_);
v___y_175_ = v___x_185_;
v___y_176_ = v___y_184_;
v___y_177_ = v___x_188_;
v___y_178_ = v___x_188_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_185_;
v___y_176_ = v___y_184_;
v___y_177_ = v___x_188_;
v___y_178_ = v___x_182_;
goto v___jp_174_;
}
}
else
{
return v___y_184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(lean_object* v_e_203_, lean_object* v_fvarIdToPos_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_e_203_, v_fvarIdToPos_204_);
lean_dec(v_fvarIdToPos_204_);
return v_res_205_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_206_, lean_object* v_k_207_, lean_object* v_t_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_207_, v_t_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_210_, lean_object* v_k_211_, lean_object* v_t_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_210_, v_k_211_, v_t_212_);
lean_dec(v_t_212_);
lean_dec(v_k_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_215_, lean_object* v_n_216_, lean_object* v_as_217_, lean_object* v_lo_218_, lean_object* v_hi_219_, lean_object* v_w_220_, lean_object* v_hlo_221_, lean_object* v_hhi_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_215_, v_n_216_, v_as_217_, v_lo_218_, v_hi_219_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_224_, lean_object* v_n_225_, lean_object* v_as_226_, lean_object* v_lo_227_, lean_object* v_hi_228_, lean_object* v_w_229_, lean_object* v_hlo_230_, lean_object* v_hhi_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_224_, v_n_225_, v_as_226_, v_lo_227_, v_hi_228_, v_w_229_, v_hlo_230_, v_hhi_231_);
lean_dec(v_hi_228_);
lean_dec(v_n_225_);
lean_dec(v_fvarIdToPos_224_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(lean_object* v_fvarIdToPos_233_, lean_object* v_n_234_, lean_object* v_lo_235_, lean_object* v_hi_236_, lean_object* v_hhi_237_, lean_object* v_pivot_238_, lean_object* v_as_239_, lean_object* v_i_240_, lean_object* v_k_241_, lean_object* v_ilo_242_, lean_object* v_ik_243_, lean_object* v_w_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_233_, v_hi_236_, v_pivot_238_, v_as_239_, v_i_240_, v_k_241_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(lean_object* v_fvarIdToPos_246_, lean_object* v_n_247_, lean_object* v_lo_248_, lean_object* v_hi_249_, lean_object* v_hhi_250_, lean_object* v_pivot_251_, lean_object* v_as_252_, lean_object* v_i_253_, lean_object* v_k_254_, lean_object* v_ilo_255_, lean_object* v_ik_256_, lean_object* v_w_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(v_fvarIdToPos_246_, v_n_247_, v_lo_248_, v_hi_249_, v_hhi_250_, v_pivot_251_, v_as_252_, v_i_253_, v_k_254_, v_ilo_255_, v_ik_256_, v_w_257_);
lean_dec(v_pivot_251_);
lean_dec(v_hi_249_);
lean_dec(v_lo_248_);
lean_dec(v_n_247_);
lean_dec(v_fvarIdToPos_246_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_259_, uint8_t v_bi_260_, lean_object* v_t_261_, lean_object* v_b_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___y_271_; lean_object* v___x_274_; uint8_t v_debug_275_; 
v___x_274_ = lean_st_ref_get(v___y_264_);
v_debug_275_ = lean_ctor_get_uint8(v___x_274_, sizeof(void*)*11);
lean_dec(v___x_274_);
if (v_debug_275_ == 0)
{
v___y_271_ = v___y_264_;
goto v___jp_270_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_261_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; 
lean_dec_ref_known(v___x_276_, 1);
v___x_277_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_dec_ref_known(v___x_277_, 1);
v___y_271_ = v___y_264_;
goto v___jp_270_;
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_b_262_);
lean_dec_ref(v_t_261_);
lean_dec(v_x_259_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_b_262_);
lean_dec_ref(v_t_261_);
lean_dec(v_x_259_);
v_a_286_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_276_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = l_Lean_Expr_forallE___override(v_x_259_, v_t_261_, v_b_262_, v_bi_260_);
v___x_273_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_272_, v___y_271_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_294_, lean_object* v_bi_295_, lean_object* v_t_296_, lean_object* v_b_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
uint8_t v_bi_boxed_305_; lean_object* v_res_306_; 
v_bi_boxed_305_ = lean_unbox(v_bi_295_);
v_res_306_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_294_, v_bi_boxed_305_, v_t_296_, v_b_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_310_, lean_object* v_i_311_, lean_object* v_00_u03b2_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_zero_320_; uint8_t v_isZero_321_; 
v_zero_320_ = lean_unsigned_to_nat(0u);
v_isZero_321_ = lean_nat_dec_eq(v_i_311_, v_zero_320_);
if (v_isZero_321_ == 1)
{
lean_object* v___x_322_; 
lean_dec(v_i_311_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_00_u03b2_312_);
return v___x_322_;
}
else
{
lean_object* v_one_323_; lean_object* v_n_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_one_323_ = lean_unsigned_to_nat(1u);
v_n_324_ = lean_nat_sub(v_i_311_, v_one_323_);
lean_dec(v_i_311_);
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_326_ = 0;
v___x_327_ = lean_array_fget_borrowed(v_00_u03b1s_310_, v_n_324_);
lean_inc(v___x_327_);
v___x_328_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_325_, v___x_326_, v___x_327_, v_00_u03b2_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
v_i_311_ = v_n_324_;
v_00_u03b2_312_ = v_a_329_;
goto _start;
}
else
{
lean_dec(v_n_324_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_331_, lean_object* v_i_332_, lean_object* v_00_u03b2_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_331_, v_i_332_, v_00_u03b2_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec_ref(v_00_u03b1s_331_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_342_, lean_object* v_i_343_, lean_object* v_00_u03b2_344_, lean_object* v_h_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_342_, v_i_343_, v_00_u03b2_344_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_354_, lean_object* v_i_355_, lean_object* v_00_u03b2_356_, lean_object* v_h_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_354_, v_i_355_, v_00_u03b2_356_, v_h_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_00_u03b1s_354_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_366_, lean_object* v_00_u03b2_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_array_get_size(v_00_u03b1s_366_);
v___x_376_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_366_, v___x_375_, v_00_u03b2_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_377_, lean_object* v_00_u03b2_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_377_, v_00_u03b2_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec_ref(v_00_u03b1s_377_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_387_, lean_object* v_subst_388_, size_t v_sz_389_, size_t v_i_390_, lean_object* v_bs_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_lt(v_i_390_, v_sz_389_);
if (v___x_392_ == 0)
{
return v_bs_391_;
}
else
{
lean_object* v___x_393_; lean_object* v_v_394_; lean_object* v___x_395_; lean_object* v_bs_x27_396_; lean_object* v___x_397_; lean_object* v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_393_ = l_Lean_instInhabitedExpr;
v_v_394_ = lean_array_uget(v_bs_391_, v_i_390_);
v___x_395_ = lean_unsigned_to_nat(0u);
v_bs_x27_396_ = lean_array_uset(v_bs_391_, v_i_390_, v___x_395_);
v___x_397_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_387_, v_v_394_);
lean_dec(v_v_394_);
v___x_398_ = lean_array_get_borrowed(v___x_393_, v_subst_388_, v___x_397_);
lean_dec(v___x_397_);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_add(v_i_390_, v___x_399_);
lean_inc(v___x_398_);
v___x_401_ = lean_array_uset(v_bs_x27_396_, v_i_390_, v___x_398_);
v_i_390_ = v___x_400_;
v_bs_391_ = v___x_401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_403_, lean_object* v_subst_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_bs_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_403_, v_subst_404_, v_sz_boxed_408_, v_i_boxed_409_, v_bs_407_);
lean_dec_ref(v_subst_404_);
lean_dec(v_fvarIdToPos_403_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_411_, size_t v_i_412_, lean_object* v_bs_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_lt(v_i_412_, v_sz_411_);
if (v___x_414_ == 0)
{
return v_bs_413_;
}
else
{
lean_object* v_v_415_; lean_object* v___x_416_; lean_object* v_bs_x27_417_; lean_object* v___x_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v_v_415_ = lean_array_uget(v_bs_413_, v_i_412_);
v___x_416_ = lean_unsigned_to_nat(0u);
v_bs_x27_417_ = lean_array_uset(v_bs_413_, v_i_412_, v___x_416_);
v___x_418_ = l_Lean_mkFVar(v_v_415_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_412_, v___x_419_);
v___x_421_ = lean_array_uset(v_bs_x27_417_, v_i_412_, v___x_418_);
v_i_412_ = v___x_420_;
v_bs_413_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_bs_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_426_, v_i_boxed_427_, v_bs_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; 
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_438_ = lean_apply_8(v_k_429_, v_b_432_, v___y_430_, v___y_431_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, lean_box(0));
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_439_, v___y_440_, v___y_441_, v_b_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_449_, uint8_t v_bi_450_, lean_object* v_type_451_, lean_object* v_k_452_, uint8_t v_kind_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_462_; 
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_461_, 0, v_k_452_);
lean_closure_set(v___f_461_, 1, v___y_454_);
lean_closure_set(v___f_461_, 2, v___y_455_);
v___x_462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_449_, v_bi_450_, v_type_451_, v___f_461_, v_kind_453_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_462_) == 0)
{
return v___x_462_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_471_, lean_object* v_bi_472_, lean_object* v_type_473_, lean_object* v_k_474_, lean_object* v_kind_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
uint8_t v_bi_boxed_483_; uint8_t v_kind_boxed_484_; lean_object* v_res_485_; 
v_bi_boxed_483_ = lean_unbox(v_bi_472_);
v_kind_boxed_484_ = lean_unbox(v_kind_475_);
v_res_485_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_471_, v_bi_boxed_483_, v_type_473_, v_k_474_, v_kind_boxed_484_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_486_, lean_object* v_type_487_, lean_object* v_k_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
uint8_t v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = 0;
v___x_497_ = 0;
v___x_498_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_486_, v___x_496_, v_type_487_, v_k_488_, v___x_497_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_499_, lean_object* v_type_500_, lean_object* v_k_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_499_, v_type_500_, v_k_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_510_, lean_object* v_k_511_, lean_object* v_fallback_512_){
_start:
{
if (lean_obj_tag(v_t_510_) == 0)
{
lean_object* v_k_513_; lean_object* v_v_514_; lean_object* v_l_515_; lean_object* v_r_516_; uint8_t v___x_517_; 
v_k_513_ = lean_ctor_get(v_t_510_, 1);
v_v_514_ = lean_ctor_get(v_t_510_, 2);
v_l_515_ = lean_ctor_get(v_t_510_, 3);
v_r_516_ = lean_ctor_get(v_t_510_, 4);
v___x_517_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_511_, v_k_513_);
switch(v___x_517_)
{
case 0:
{
v_t_510_ = v_l_515_;
goto _start;
}
case 1:
{
lean_inc(v_v_514_);
return v_v_514_;
}
default: 
{
v_t_510_ = v_r_516_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_512_);
return v_fallback_512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_520_, lean_object* v_k_521_, lean_object* v_fallback_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_520_, v_k_521_, v_fallback_522_);
lean_dec(v_fallback_522_);
lean_dec(v_k_521_);
lean_dec(v_t_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_524_, size_t v_sz_525_, size_t v_i_526_, lean_object* v_bs_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_526_, v_sz_525_);
if (v___x_528_ == 0)
{
return v_bs_527_;
}
else
{
lean_object* v_v_529_; lean_object* v___x_530_; lean_object* v_bs_x27_531_; lean_object* v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_v_529_ = lean_array_uget(v_bs_527_, v_i_526_);
v___x_530_ = lean_unsigned_to_nat(0u);
v_bs_x27_531_ = lean_array_uset(v_bs_527_, v_i_526_, v___x_530_);
v___x_532_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_524_, v_v_529_, v___x_530_);
lean_dec(v_v_529_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_add(v_i_526_, v___x_533_);
v___x_535_ = lean_array_uset(v_bs_x27_531_, v_i_526_, v___x_532_);
v_i_526_ = v___x_534_;
v_bs_527_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_537_, lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_bs_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_542_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_537_, v_sz_boxed_541_, v_i_boxed_542_, v_bs_540_);
lean_dec(v_fvarIdToPos_537_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_553_ = _args[0];
lean_object* v_subst_554_ = _args[1];
lean_object* v_sz_555_ = _args[2];
lean_object* v___x_556_ = _args[3];
lean_object* v_fvarIds_557_ = _args[4];
lean_object* v_x_558_ = _args[5];
lean_object* v_xs_559_ = _args[6];
lean_object* v_xs_x27_560_ = _args[7];
lean_object* v_args_561_ = _args[8];
lean_object* v_a_562_ = _args[9];
lean_object* v_types_563_ = _args[10];
lean_object* v_a_564_ = _args[11];
lean_object* v_varDeps_565_ = _args[12];
lean_object* v_varPos_566_ = _args[13];
lean_object* v_haveExpr_567_ = _args[14];
lean_object* v_body_568_ = _args[15];
lean_object* v_x_x27_569_ = _args[16];
lean_object* v___y_570_ = _args[17];
lean_object* v___y_571_ = _args[18];
lean_object* v___y_572_ = _args[19];
lean_object* v___y_573_ = _args[20];
lean_object* v___y_574_ = _args[21];
lean_object* v___y_575_ = _args[22];
lean_object* v___y_576_ = _args[23];
_start:
{
size_t v_sz_boxed_577_; size_t v___x_6520__boxed_578_; lean_object* v_res_579_; 
v_sz_boxed_577_ = lean_unbox_usize(v_sz_555_);
lean_dec(v_sz_555_);
v___x_6520__boxed_578_ = lean_unbox_usize(v___x_556_);
lean_dec(v___x_556_);
v_res_579_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_553_, v_subst_554_, v_sz_boxed_577_, v___x_6520__boxed_578_, v_fvarIds_557_, v_x_558_, v_xs_559_, v_xs_x27_560_, v_args_561_, v_a_562_, v_types_563_, v_a_564_, v_varDeps_565_, v_varPos_566_, v_haveExpr_567_, v_body_568_, v_x_x27_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_v_580_, lean_object* v_fvarIdToPos_581_, uint8_t v_nondep_582_, lean_object* v_t_583_, lean_object* v_subst_584_, lean_object* v_xs_585_, lean_object* v_xs_x27_586_, lean_object* v_args_587_, lean_object* v_types_588_, lean_object* v_varDeps_589_, lean_object* v_haveExpr_590_, lean_object* v_body_591_, lean_object* v_declName_592_, lean_object* v_x_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_fvarIds_601_; size_t v_sz_602_; size_t v___x_603_; lean_object* v_varPos_604_; lean_object* v_ys_605_; uint8_t v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; 
lean_inc_ref(v_v_580_);
v_fvarIds_601_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_580_, v_fvarIdToPos_581_);
v_sz_602_ = lean_array_size(v_fvarIds_601_);
v___x_603_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_601_, 2);
v_varPos_604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_581_, v_sz_602_, v___x_603_, v_fvarIds_601_);
v_ys_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_602_, v___x_603_, v_fvarIds_601_);
v___x_606_ = 0;
v___x_607_ = 1;
v___x_608_ = l_Lean_Meta_mkLambdaFVars(v_ys_605_, v_v_580_, v___x_606_, v_nondep_582_, v___x_606_, v_nondep_582_, v___x_607_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = l_Lean_Meta_mkForallFVars(v_ys_605_, v_t_583_, v___x_606_, v_nondep_582_, v_nondep_582_, v___x_607_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec_ref(v_ys_605_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Meta_Sym_shareCommonInc(v_a_611_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_n(v_a_613_, 2);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = lean_box_usize(v_sz_602_);
v___x_615_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_616_, 0, v_fvarIdToPos_581_);
lean_closure_set(v___f_616_, 1, v_subst_584_);
lean_closure_set(v___f_616_, 2, v___x_614_);
lean_closure_set(v___f_616_, 3, v___x_615_);
lean_closure_set(v___f_616_, 4, v_fvarIds_601_);
lean_closure_set(v___f_616_, 5, v_x_593_);
lean_closure_set(v___f_616_, 6, v_xs_585_);
lean_closure_set(v___f_616_, 7, v_xs_x27_586_);
lean_closure_set(v___f_616_, 8, v_args_587_);
lean_closure_set(v___f_616_, 9, v_a_609_);
lean_closure_set(v___f_616_, 10, v_types_588_);
lean_closure_set(v___f_616_, 11, v_a_613_);
lean_closure_set(v___f_616_, 12, v_varDeps_589_);
lean_closure_set(v___f_616_, 13, v_varPos_604_);
lean_closure_set(v___f_616_, 14, v_haveExpr_590_);
lean_closure_set(v___f_616_, 15, v_body_591_);
v___x_617_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_592_, v_a_613_, v___f_616_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_617_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_a_609_);
lean_dec_ref(v_varPos_604_);
lean_dec_ref(v_fvarIds_601_);
lean_dec_ref(v_x_593_);
lean_dec(v_declName_592_);
lean_dec_ref(v_body_591_);
lean_dec_ref(v_haveExpr_590_);
lean_dec_ref(v_varDeps_589_);
lean_dec_ref(v_types_588_);
lean_dec_ref(v_args_587_);
lean_dec_ref(v_xs_x27_586_);
lean_dec_ref(v_xs_585_);
lean_dec_ref(v_subst_584_);
lean_dec(v_fvarIdToPos_581_);
v_a_618_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_612_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_612_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_a_609_);
lean_dec_ref(v_varPos_604_);
lean_dec_ref(v_fvarIds_601_);
lean_dec_ref(v_x_593_);
lean_dec(v_declName_592_);
lean_dec_ref(v_body_591_);
lean_dec_ref(v_haveExpr_590_);
lean_dec_ref(v_varDeps_589_);
lean_dec_ref(v_types_588_);
lean_dec_ref(v_args_587_);
lean_dec_ref(v_xs_x27_586_);
lean_dec_ref(v_xs_585_);
lean_dec_ref(v_subst_584_);
lean_dec(v_fvarIdToPos_581_);
v_a_626_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_610_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_610_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_ys_605_);
lean_dec_ref(v_varPos_604_);
lean_dec_ref(v_fvarIds_601_);
lean_dec_ref(v_x_593_);
lean_dec(v_declName_592_);
lean_dec_ref(v_body_591_);
lean_dec_ref(v_haveExpr_590_);
lean_dec_ref(v_varDeps_589_);
lean_dec_ref(v_types_588_);
lean_dec_ref(v_args_587_);
lean_dec_ref(v_xs_x27_586_);
lean_dec_ref(v_xs_585_);
lean_dec_ref(v_subst_584_);
lean_dec_ref(v_t_583_);
lean_dec(v_fvarIdToPos_581_);
v_a_634_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_608_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_608_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_v_642_ = _args[0];
lean_object* v_fvarIdToPos_643_ = _args[1];
lean_object* v_nondep_644_ = _args[2];
lean_object* v_t_645_ = _args[3];
lean_object* v_subst_646_ = _args[4];
lean_object* v_xs_647_ = _args[5];
lean_object* v_xs_x27_648_ = _args[6];
lean_object* v_args_649_ = _args[7];
lean_object* v_types_650_ = _args[8];
lean_object* v_varDeps_651_ = _args[9];
lean_object* v_haveExpr_652_ = _args[10];
lean_object* v_body_653_ = _args[11];
lean_object* v_declName_654_ = _args[12];
lean_object* v_x_655_ = _args[13];
lean_object* v___y_656_ = _args[14];
lean_object* v___y_657_ = _args[15];
lean_object* v___y_658_ = _args[16];
lean_object* v___y_659_ = _args[17];
lean_object* v___y_660_ = _args[18];
lean_object* v___y_661_ = _args[19];
lean_object* v___y_662_ = _args[20];
_start:
{
uint8_t v_nondep_6547__boxed_663_; lean_object* v_res_664_; 
v_nondep_6547__boxed_663_ = lean_unbox(v_nondep_644_);
v_res_664_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_v_642_, v_fvarIdToPos_643_, v_nondep_6547__boxed_663_, v_t_645_, v_subst_646_, v_xs_647_, v_xs_x27_648_, v_args_649_, v_types_650_, v_varDeps_651_, v_haveExpr_652_, v_body_653_, v_declName_654_, v_x_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_665_, lean_object* v_e_666_, lean_object* v_xs_667_, lean_object* v_xs_x27_668_, lean_object* v_args_669_, lean_object* v_subst_670_, lean_object* v_types_671_, lean_object* v_varDeps_672_, lean_object* v_fvarIdToPos_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; 
if (lean_obj_tag(v_e_666_) == 8)
{
uint8_t v_nondep_768_; 
v_nondep_768_ = lean_ctor_get_uint8(v_e_666_, sizeof(void*)*4 + 8);
if (v_nondep_768_ == 1)
{
lean_object* v_declName_769_; lean_object* v_type_770_; lean_object* v_value_771_; lean_object* v_body_772_; lean_object* v_t_773_; lean_object* v_v_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v_declName_769_ = lean_ctor_get(v_e_666_, 0);
lean_inc_n(v_declName_769_, 2);
v_type_770_ = lean_ctor_get(v_e_666_, 1);
lean_inc_ref(v_type_770_);
v_value_771_ = lean_ctor_get(v_e_666_, 2);
lean_inc_ref(v_value_771_);
v_body_772_ = lean_ctor_get(v_e_666_, 3);
lean_inc_ref(v_body_772_);
lean_dec_ref_known(v_e_666_, 4);
v_t_773_ = lean_expr_instantiate_rev(v_type_770_, v_xs_667_);
lean_dec_ref(v_type_770_);
v_v_774_ = lean_expr_instantiate_rev(v_value_771_, v_xs_667_);
lean_dec_ref(v_value_771_);
v___x_775_ = lean_box(v_nondep_768_);
lean_inc_ref(v_t_773_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 21, 13);
lean_closure_set(v___f_776_, 0, v_v_774_);
lean_closure_set(v___f_776_, 1, v_fvarIdToPos_673_);
lean_closure_set(v___f_776_, 2, v___x_775_);
lean_closure_set(v___f_776_, 3, v_t_773_);
lean_closure_set(v___f_776_, 4, v_subst_670_);
lean_closure_set(v___f_776_, 5, v_xs_667_);
lean_closure_set(v___f_776_, 6, v_xs_x27_668_);
lean_closure_set(v___f_776_, 7, v_args_669_);
lean_closure_set(v___f_776_, 8, v_types_671_);
lean_closure_set(v___f_776_, 9, v_varDeps_672_);
lean_closure_set(v___f_776_, 10, v_haveExpr_665_);
lean_closure_set(v___f_776_, 11, v_body_772_);
lean_closure_set(v___f_776_, 12, v_declName_769_);
v___x_777_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_769_, v_t_773_, v___f_776_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
return v___x_777_;
}
else
{
lean_dec(v_fvarIdToPos_673_);
lean_dec_ref(v_xs_667_);
v___y_682_ = v_a_674_;
v___y_683_ = v_a_675_;
v___y_684_ = v_a_676_;
v___y_685_ = v_a_677_;
v___y_686_ = v_a_678_;
v___y_687_ = v_a_679_;
goto v___jp_681_;
}
}
else
{
lean_dec(v_fvarIdToPos_673_);
lean_dec_ref(v_xs_667_);
v___y_682_ = v_a_674_;
v___y_683_ = v_a_675_;
v___y_684_ = v_a_676_;
v___y_685_ = v_a_677_;
v___y_686_ = v_a_678_;
v___y_687_ = v_a_679_;
goto v___jp_681_;
}
v___jp_681_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_subst_670_);
v___x_690_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_666_, v___x_688_, v___x_689_, v_subst_670_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_n(v_a_691_, 2);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_Sym_inferType(v_a_691_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_n(v_a_693_, 2);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_693_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
lean_inc(v_a_693_);
v___x_696_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_671_, v_a_693_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v_types_671_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_668_, v_a_691_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = l_Lean_mkAppN(v_a_699_, v_args_669_);
lean_dec_ref(v_args_669_);
v___x_701_ = l_Lean_Meta_Sym_shareCommonInc(v___x_700_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_719_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_719_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_719_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_719_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_707_ = lean_box(0);
lean_inc(v_a_695_);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v_a_695_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
lean_inc_ref(v___x_708_);
v___x_709_ = l_Lean_mkConst(v___x_706_, v___x_708_);
lean_inc(v_a_702_);
lean_inc_ref(v_haveExpr_665_);
lean_inc_n(v_a_693_, 2);
v___x_710_ = l_Lean_mkApp3(v___x_709_, v_a_693_, v_haveExpr_665_, v_a_702_);
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_712_ = l_Lean_mkConst(v___x_711_, v___x_708_);
v___x_713_ = l_Lean_mkAppB(v___x_712_, v_a_693_, v_haveExpr_665_);
v___x_714_ = l_Lean_Meta_mkExpectedPropHint(v___x_713_, v___x_710_);
v___x_715_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_715_, 0, v_a_693_);
lean_ctor_set(v___x_715_, 1, v_a_695_);
lean_ctor_set(v___x_715_, 2, v_a_702_);
lean_ctor_set(v___x_715_, 3, v___x_714_);
lean_ctor_set(v___x_715_, 4, v_varDeps_672_);
lean_ctor_set(v___x_715_, 5, v_a_697_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_715_);
v___x_717_ = v___x_704_;
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
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_a_697_);
lean_dec(v_a_695_);
lean_dec(v_a_693_);
lean_dec_ref(v_varDeps_672_);
lean_dec_ref(v_haveExpr_665_);
v_a_720_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_701_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_701_);
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
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_a_697_);
lean_dec(v_a_695_);
lean_dec(v_a_693_);
lean_dec_ref(v_varDeps_672_);
lean_dec_ref(v_args_669_);
lean_dec_ref(v_haveExpr_665_);
v_a_728_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_698_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_698_);
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
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_a_695_);
lean_dec(v_a_693_);
lean_dec(v_a_691_);
lean_dec_ref(v_varDeps_672_);
lean_dec_ref(v_args_669_);
lean_dec_ref(v_xs_x27_668_);
lean_dec_ref(v_haveExpr_665_);
v_a_736_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_696_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_696_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
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
lean_dec(v_a_693_);
lean_dec(v_a_691_);
lean_dec_ref(v_varDeps_672_);
lean_dec_ref(v_types_671_);
lean_dec_ref(v_args_669_);
lean_dec_ref(v_xs_x27_668_);
lean_dec_ref(v_haveExpr_665_);
v_a_744_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_694_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_694_);
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
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_691_);
lean_dec_ref(v_varDeps_672_);
lean_dec_ref(v_types_671_);
lean_dec_ref(v_args_669_);
lean_dec_ref(v_xs_x27_668_);
lean_dec_ref(v_haveExpr_665_);
v_a_752_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_692_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_692_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_varDeps_672_);
lean_dec_ref(v_types_671_);
lean_dec_ref(v_args_669_);
lean_dec_ref(v_xs_x27_668_);
lean_dec_ref(v_haveExpr_665_);
v_a_760_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_690_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_690_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_778_, lean_object* v_subst_779_, size_t v_sz_780_, size_t v___x_781_, lean_object* v_fvarIds_782_, lean_object* v_x_783_, lean_object* v_xs_784_, lean_object* v_xs_x27_785_, lean_object* v_args_786_, lean_object* v_a_787_, lean_object* v_types_788_, lean_object* v_a_789_, lean_object* v_varDeps_790_, lean_object* v_varPos_791_, lean_object* v_haveExpr_792_, lean_object* v_body_793_, lean_object* v_x_x27_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_778_, v_subst_779_, v_sz_780_, v___x_781_, v_fvarIds_782_);
lean_inc_ref(v_x_x27_794_);
v___x_803_ = l_Lean_mkAppN(v_x_x27_794_, v___x_802_);
lean_dec_ref(v___x_802_);
v___x_804_ = l_Lean_Meta_Sym_shareCommonInc(v___x_803_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v___x_806_ = l_Lean_Expr_fvarId_x21(v_x_783_);
v___x_807_ = lean_array_get_size(v_xs_784_);
v___x_808_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_806_, v___x_807_, v_fvarIdToPos_778_);
v___x_809_ = lean_array_push(v_xs_784_, v_x_783_);
v___x_810_ = lean_array_push(v_xs_x27_785_, v_x_x27_794_);
v___x_811_ = lean_array_push(v_args_786_, v_a_787_);
v___x_812_ = lean_array_push(v_subst_779_, v_a_805_);
v___x_813_ = lean_array_push(v_types_788_, v_a_789_);
v___x_814_ = lean_array_push(v_varDeps_790_, v_varPos_791_);
v___x_815_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_792_, v_body_793_, v___x_809_, v___x_810_, v___x_811_, v___x_812_, v___x_813_, v___x_814_, v___x_808_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_815_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_x_x27_794_);
lean_dec_ref(v_body_793_);
lean_dec_ref(v_haveExpr_792_);
lean_dec_ref(v_varPos_791_);
lean_dec_ref(v_varDeps_790_);
lean_dec_ref(v_a_789_);
lean_dec_ref(v_types_788_);
lean_dec_ref(v_a_787_);
lean_dec_ref(v_args_786_);
lean_dec_ref(v_xs_x27_785_);
lean_dec_ref(v_xs_784_);
lean_dec_ref(v_x_783_);
lean_dec_ref(v_subst_779_);
lean_dec(v_fvarIdToPos_778_);
v_a_816_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_804_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_804_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_824_, lean_object* v_e_825_, lean_object* v_xs_826_, lean_object* v_xs_x27_827_, lean_object* v_args_828_, lean_object* v_subst_829_, lean_object* v_types_830_, lean_object* v_varDeps_831_, lean_object* v_fvarIdToPos_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_824_, v_e_825_, v_xs_826_, v_xs_x27_827_, v_args_828_, v_subst_829_, v_types_830_, v_varDeps_831_, v_fvarIdToPos_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_841_, lean_object* v_t_842_, lean_object* v_k_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_842_, v_k_843_, v_fallback_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_846_, lean_object* v_t_847_, lean_object* v_k_848_, lean_object* v_fallback_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_846_, v_t_847_, v_k_848_, v_fallback_849_);
lean_dec(v_fallback_849_);
lean_dec(v_k_848_);
lean_dec(v_t_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_851_, lean_object* v_name_852_, uint8_t v_bi_853_, lean_object* v_type_854_, lean_object* v_k_855_, uint8_t v_kind_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_852_, v_bi_853_, v_type_854_, v_k_855_, v_kind_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_865_, lean_object* v_name_866_, lean_object* v_bi_867_, lean_object* v_type_868_, lean_object* v_k_869_, lean_object* v_kind_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v_bi_boxed_878_; uint8_t v_kind_boxed_879_; lean_object* v_res_880_; 
v_bi_boxed_878_ = lean_unbox(v_bi_867_);
v_kind_boxed_879_ = lean_unbox(v_kind_870_);
v_res_880_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_865_, v_name_866_, v_bi_boxed_878_, v_type_868_, v_k_869_, v_kind_boxed_879_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_881_, lean_object* v_name_882_, lean_object* v_type_883_, lean_object* v_k_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_882_, v_type_883_, v_k_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_893_, lean_object* v_name_894_, lean_object* v_type_895_, lean_object* v_k_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_893_, v_name_894_, v_type_895_, v_k_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_916_ = lean_box(1);
lean_inc_ref(v_haveExpr_907_);
v___x_917_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_907_, v_haveExpr_907_, v___x_915_, v___x_915_, v___x_915_, v___x_915_, v___x_915_, v___x_915_, v___x_916_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_927_, lean_object* v_n_928_){
_start:
{
lean_object* v_zero_929_; uint8_t v_isZero_930_; 
v_zero_929_ = lean_unsigned_to_nat(0u);
v_isZero_930_ = lean_nat_dec_eq(v_n_928_, v_zero_929_);
if (v_isZero_930_ == 1)
{
lean_dec(v_n_928_);
return v_type_927_;
}
else
{
lean_object* v_one_931_; lean_object* v_n_932_; lean_object* v___x_933_; 
v_one_931_ = lean_unsigned_to_nat(1u);
v_n_932_ = lean_nat_sub(v_n_928_, v_one_931_);
lean_dec(v_n_928_);
v___x_933_ = l_Lean_Expr_bindingBody_x21(v_type_927_);
lean_dec_ref(v_type_927_);
v_type_927_ = v___x_933_;
v_n_928_ = v_n_932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(lean_object* v_idx_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = l_Lean_Expr_bvar___override(v_idx_935_);
v___x_938_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_937_, v___y_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_idx_939_, uint8_t v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v_idx_939_, v___y_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___boxed(lean_object* v_idx_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
uint8_t v___y_25091__boxed_948_; lean_object* v_res_949_; 
v___y_25091__boxed_948_ = lean_unbox(v___y_945_);
v_res_949_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(v_idx_944_, v___y_25091__boxed_948_, v___y_946_, v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_msg_952_, uint8_t v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___f_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___x_1542__overap_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___f_956_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0));
v___f_957_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__1));
v___x_958_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_956_, v___f_957_);
v___f_959_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_959_, 0, v___x_958_);
v___f_960_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_960_, 0, v___f_959_);
v___f_961_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_961_, 0, v___f_960_);
v___x_1542__overap_962_ = lean_panic_fn_borrowed(v___f_961_, v_msg_952_);
lean_dec_ref(v___f_961_);
v___x_963_ = lean_box(v___y_953_);
lean_inc_ref(v___y_954_);
v___x_964_ = lean_apply_3(v___x_1542__overap_962_, v___x_963_, v___y_954_, v___y_955_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___y_25106__boxed_969_; lean_object* v_res_970_; 
v___y_25106__boxed_969_ = lean_unbox(v___y_966_);
v_res_970_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_msg_965_, v___y_25106__boxed_969_, v___y_967_, v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_970_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0(void){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_1995__overap_981_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0);
v___x_1995__overap_981_ = lean_panic_fn_borrowed(v___x_980_, v_msg_972_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
v___x_982_ = lean_apply_7(v___x_1995__overap_981_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object* v_x_992_, uint8_t v_bi_993_, lean_object* v_t_994_, lean_object* v_b_995_, lean_object* v___y_996_, uint8_t v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___y_1001_; lean_object* v___y_1002_; 
if (v___y_997_ == 0)
{
v___y_1001_ = v___y_996_;
v___y_1002_ = v___y_999_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_994_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 2);
v___x_1026_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_995_, v___y_997_, v___y_998_, v_a_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 2);
v___y_1001_ = v___y_996_;
v___y_1002_ = v_a_1027_;
goto v___jp_1000_;
}
else
{
lean_object* v_a_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___y_996_);
lean_dec_ref(v_b_995_);
lean_dec_ref(v_t_994_);
lean_dec(v_x_992_);
v_a_1028_ = lean_ctor_get(v___x_1026_, 0);
v_a_1029_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1026_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_inc(v_a_1028_);
lean_dec(v___x_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1028_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v___y_996_);
lean_dec_ref(v_b_995_);
lean_dec_ref(v_t_994_);
lean_dec(v_x_992_);
v_a_1037_ = lean_ctor_get(v___x_1024_, 0);
v_a_1038_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1024_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_inc(v_a_1037_);
lean_dec(v___x_1024_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1037_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
v___jp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = l_Lean_Expr_lam___override(v_x_992_, v_t_994_, v_b_995_, v_bi_993_);
v___x_1004_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1003_, v___y_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_a_1006_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v___x_1004_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_a_1005_);
lean_ctor_set(v___x_1010_, 1, v___y_1001_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_a_1006_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___y_1001_);
v_a_1015_ = lean_ctor_get(v___x_1004_, 0);
v_a_1016_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1004_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_inc(v_a_1015_);
lean_dec(v___x_1004_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1015_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object* v_x_1046_, lean_object* v_bi_1047_, lean_object* v_t_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v_bi_boxed_1054_; uint8_t v___y_25162__boxed_1055_; lean_object* v_res_1056_; 
v_bi_boxed_1054_ = lean_unbox(v_bi_1047_);
v___y_25162__boxed_1055_ = lean_unbox(v___y_1051_);
v_res_1056_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_x_1046_, v_bi_boxed_1054_, v_t_1048_, v_b_1049_, v___y_1050_, v___y_25162__boxed_1055_, v___y_1052_, v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object* v_x_1057_, lean_object* v_t_1058_, lean_object* v_v_1059_, lean_object* v_b_1060_, uint8_t v_nondep_1061_, lean_object* v___y_1062_, uint8_t v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___y_1067_; lean_object* v___y_1068_; 
if (v___y_1063_ == 0)
{
v___y_1067_ = v___y_1062_;
v___y_1068_ = v___y_1065_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1058_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 2);
v___x_1092_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1059_, v___y_1063_, v___y_1064_, v_a_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 2);
v___x_1094_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1060_, v___y_1063_, v___y_1064_, v_a_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 1);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 2);
v___y_1067_ = v___y_1062_;
v___y_1068_ = v_a_1095_;
goto v___jp_1066_;
}
else
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_v_1059_);
lean_dec_ref(v_t_1058_);
lean_dec(v_x_1057_);
v_a_1096_ = lean_ctor_get(v___x_1094_, 0);
v_a_1097_ = lean_ctor_get(v___x_1094_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1094_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_inc(v_a_1096_);
lean_dec(v___x_1094_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_v_1059_);
lean_dec_ref(v_t_1058_);
lean_dec(v_x_1057_);
v_a_1105_ = lean_ctor_get(v___x_1092_, 0);
v_a_1106_ = lean_ctor_get(v___x_1092_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1092_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_inc(v_a_1105_);
lean_dec(v___x_1092_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_v_1059_);
lean_dec_ref(v_t_1058_);
lean_dec(v_x_1057_);
v_a_1114_ = lean_ctor_get(v___x_1090_, 0);
v_a_1115_ = lean_ctor_get(v___x_1090_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1090_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_inc(v_a_1114_);
lean_dec(v___x_1090_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
v___jp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = l_Lean_Expr_letE___override(v_x_1057_, v_t_1058_, v_v_1059_, v_b_1060_, v_nondep_1061_);
v___x_1070_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1069_, v___y_1068_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_a_1072_ = lean_ctor_get(v___x_1070_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1074_ = v___x_1070_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1071_);
lean_ctor_set(v___x_1076_, 1, v___y_1067_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_a_1072_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v___y_1067_);
v_a_1081_ = lean_ctor_get(v___x_1070_, 0);
v_a_1082_ = lean_ctor_get(v___x_1070_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1070_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_inc(v_a_1081_);
lean_dec(v___x_1070_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object* v_x_1123_, lean_object* v_t_1124_, lean_object* v_v_1125_, lean_object* v_b_1126_, lean_object* v_nondep_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v_nondep_boxed_1132_; uint8_t v___y_25268__boxed_1133_; lean_object* v_res_1134_; 
v_nondep_boxed_1132_ = lean_unbox(v_nondep_1127_);
v___y_25268__boxed_1133_ = lean_unbox(v___y_1129_);
v_res_1134_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_x_1123_, v_t_1124_, v_v_1125_, v_b_1126_, v_nondep_boxed_1132_, v___y_1128_, v___y_25268__boxed_1133_, v___y_1130_, v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object* v_x_1135_, uint8_t v_bi_1136_, lean_object* v_t_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, uint8_t v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___y_1144_; lean_object* v___y_1145_; 
if (v___y_1140_ == 0)
{
v___y_1144_ = v___y_1139_;
v___y_1145_ = v___y_1142_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1137_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 2);
v___x_1169_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1138_, v___y_1140_, v___y_1141_, v_a_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 2);
v___y_1144_ = v___y_1139_;
v___y_1145_ = v_a_1170_;
goto v___jp_1143_;
}
else
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v___y_1139_);
lean_dec_ref(v_b_1138_);
lean_dec_ref(v_t_1137_);
lean_dec(v_x_1135_);
v_a_1171_ = lean_ctor_get(v___x_1169_, 0);
v_a_1172_ = lean_ctor_get(v___x_1169_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1169_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1171_);
lean_dec(v___x_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v___y_1139_);
lean_dec_ref(v_b_1138_);
lean_dec_ref(v_t_1137_);
lean_dec(v_x_1135_);
v_a_1180_ = lean_ctor_get(v___x_1167_, 0);
v_a_1181_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1167_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_inc(v_a_1180_);
lean_dec(v___x_1167_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1180_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
v___jp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l_Lean_Expr_forallE___override(v_x_1135_, v_t_1137_, v_b_1138_, v_bi_1136_);
v___x_1147_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1146_, v___y_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_a_1149_ = lean_ctor_get(v___x_1147_, 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1151_ = v___x_1147_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_a_1148_);
lean_ctor_set(v___x_1153_, 1, v___y_1144_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_a_1149_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v___y_1144_);
v_a_1158_ = lean_ctor_get(v___x_1147_, 0);
v_a_1159_ = lean_ctor_get(v___x_1147_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1147_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_inc(v_a_1158_);
lean_dec(v___x_1147_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1158_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object* v_x_1189_, lean_object* v_bi_1190_, lean_object* v_t_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v_bi_boxed_1197_; uint8_t v___y_25397__boxed_1198_; lean_object* v_res_1199_; 
v_bi_boxed_1197_ = lean_unbox(v_bi_1190_);
v___y_25397__boxed_1198_ = lean_unbox(v___y_1194_);
v_res_1199_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_x_1189_, v_bi_boxed_1197_, v_t_1191_, v_b_1192_, v___y_1193_, v___y_25397__boxed_1198_, v___y_1195_, v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object* v_f_1200_, lean_object* v_a_1201_, lean_object* v___y_1202_, uint8_t v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___y_1207_; lean_object* v___y_1208_; 
if (v___y_1203_ == 0)
{
v___y_1207_ = v___y_1202_;
v___y_1208_ = v___y_1205_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1200_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 2);
v___x_1232_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1201_, v___y_1203_, v___y_1204_, v_a_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 1);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 2);
v___y_1207_ = v___y_1202_;
v___y_1208_ = v_a_1233_;
goto v___jp_1206_;
}
else
{
lean_object* v_a_1234_; lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_a_1201_);
lean_dec_ref(v_f_1200_);
v_a_1234_ = lean_ctor_get(v___x_1232_, 0);
v_a_1235_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1232_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_inc(v_a_1234_);
lean_dec(v___x_1232_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1234_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_a_1201_);
lean_dec_ref(v_f_1200_);
v_a_1243_ = lean_ctor_get(v___x_1230_, 0);
v_a_1244_ = lean_ctor_get(v___x_1230_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1230_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_inc(v_a_1243_);
lean_dec(v___x_1230_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
v___jp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = l_Lean_Expr_app___override(v_f_1200_, v_a_1201_);
v___x_1210_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1209_, v___y_1208_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_a_1212_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_a_1211_);
lean_ctor_set(v___x_1216_, 1, v___y_1207_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1212_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v___y_1207_);
v_a_1221_ = lean_ctor_get(v___x_1210_, 0);
v_a_1222_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1210_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_inc(v_a_1221_);
lean_dec(v___x_1210_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1221_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object* v_f_1252_, lean_object* v_a_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___y_25503__boxed_1258_; lean_object* v_res_1259_; 
v___y_25503__boxed_1258_ = lean_unbox(v___y_1255_);
v_res_1259_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_f_1252_, v_a_1253_, v___y_1254_, v___y_25503__boxed_1258_, v___y_1256_, v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object* v_d_1260_, lean_object* v_e_1261_, lean_object* v___y_1262_, uint8_t v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___y_1267_; lean_object* v___y_1268_; 
if (v___y_1263_ == 0)
{
v___y_1267_ = v___y_1262_;
v___y_1268_ = v___y_1265_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1261_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 2);
v___y_1267_ = v___y_1262_;
v___y_1268_ = v_a_1291_;
goto v___jp_1266_;
}
else
{
lean_object* v_a_1292_; lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v___y_1262_);
lean_dec_ref(v_e_1261_);
lean_dec(v_d_1260_);
v_a_1292_ = lean_ctor_get(v___x_1290_, 0);
v_a_1293_ = lean_ctor_get(v___x_1290_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1290_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_inc(v_a_1292_);
lean_dec(v___x_1290_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1292_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
v___jp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Lean_Expr_mdata___override(v_d_1260_, v_e_1261_);
v___x_1270_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1269_, v___y_1268_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_a_1272_ = lean_ctor_get(v___x_1270_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1270_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1271_);
lean_ctor_set(v___x_1276_, 1, v___y_1267_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_a_1272_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v___y_1267_);
v_a_1281_ = lean_ctor_get(v___x_1270_, 0);
v_a_1282_ = lean_ctor_get(v___x_1270_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1270_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_inc(v_a_1281_);
lean_dec(v___x_1270_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1281_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object* v_d_1301_, lean_object* v_e_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v___y_25609__boxed_1307_; lean_object* v_res_1308_; 
v___y_25609__boxed_1307_ = lean_unbox(v___y_1304_);
v_res_1308_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_d_1301_, v_e_1302_, v___y_1303_, v___y_25609__boxed_1307_, v___y_1305_, v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object* v_structName_1309_, lean_object* v_idx_1310_, lean_object* v_struct_1311_, lean_object* v___y_1312_, uint8_t v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___y_1317_; lean_object* v___y_1318_; 
if (v___y_1313_ == 0)
{
v___y_1317_ = v___y_1312_;
v___y_1318_ = v___y_1315_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1311_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 2);
v___y_1317_ = v___y_1312_;
v___y_1318_ = v_a_1341_;
goto v___jp_1316_;
}
else
{
lean_object* v_a_1342_; lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v___y_1312_);
lean_dec_ref(v_struct_1311_);
lean_dec(v_idx_1310_);
lean_dec(v_structName_1309_);
v_a_1342_ = lean_ctor_get(v___x_1340_, 0);
v_a_1343_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1340_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_inc(v_a_1342_);
lean_dec(v___x_1340_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1342_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
v___jp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = l_Lean_Expr_proj___override(v_structName_1309_, v_idx_1310_, v_struct_1311_);
v___x_1320_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1319_, v___y_1318_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_a_1322_ = lean_ctor_get(v___x_1320_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1324_ = v___x_1320_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_a_1321_);
lean_ctor_set(v___x_1326_, 1, v___y_1317_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_a_1322_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v___y_1317_);
v_a_1331_ = lean_ctor_get(v___x_1320_, 0);
v_a_1332_ = lean_ctor_get(v___x_1320_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1320_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_inc(v_a_1331_);
lean_dec(v___x_1320_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1331_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object* v_structName_1351_, lean_object* v_idx_1352_, lean_object* v_struct_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___y_25692__boxed_1358_; lean_object* v_res_1359_; 
v___y_25692__boxed_1358_ = lean_unbox(v___y_1355_);
v_res_1359_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_structName_1351_, v_idx_1352_, v_struct_1353_, v___y_1354_, v___y_25692__boxed_1358_, v___y_1356_, v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(lean_object* v_msg_1367_, lean_object* v___y_1368_, uint8_t v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___f_1372_; lean_object* v___f_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___f_1384_; lean_object* v___f_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_24510__overap_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___f_1372_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0));
v___f_1373_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1));
v___f_1374_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2));
v___x_1375_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3));
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___f_1372_);
v___x_1377_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4));
v___x_1378_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5));
v___x_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1376_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
lean_ctor_set(v___x_1379_, 2, v___f_1373_);
lean_ctor_set(v___x_1379_, 3, v___f_1374_);
lean_ctor_set(v___x_1379_, 4, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6));
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_ReaderT_instMonad___redArg(v___x_1381_);
v___x_1383_ = l_ReaderT_instMonad___redArg(v___x_1382_);
lean_inc_ref_n(v___x_1383_, 6);
v___f_1384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1384_, 0, v___x_1383_);
v___f_1385_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1385_, 0, v___x_1383_);
v___f_1386_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1386_, 0, v___x_1383_);
v___f_1387_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1387_, 0, v___x_1383_);
v___x_1388_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1388_, 0, lean_box(0));
lean_closure_set(v___x_1388_, 1, lean_box(0));
lean_closure_set(v___x_1388_, 2, v___x_1383_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___f_1384_);
v___x_1390_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1390_, 0, lean_box(0));
lean_closure_set(v___x_1390_, 1, lean_box(0));
lean_closure_set(v___x_1390_, 2, v___x_1383_);
v___x_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_ctor_set(v___x_1391_, 2, v___f_1385_);
lean_ctor_set(v___x_1391_, 3, v___f_1386_);
lean_ctor_set(v___x_1391_, 4, v___f_1387_);
v___x_1392_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1392_, 0, lean_box(0));
lean_closure_set(v___x_1392_, 1, lean_box(0));
lean_closure_set(v___x_1392_, 2, v___x_1383_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_instInhabitedExpr;
v___x_1395_ = l_instInhabitedOfMonad___redArg(v___x_1393_, v___x_1394_);
v___x_24510__overap_1396_ = lean_panic_fn_borrowed(v___x_1395_, v_msg_1367_);
lean_dec(v___x_1395_);
v___x_1397_ = lean_box(v___y_1369_);
lean_inc_ref(v___y_1370_);
v___x_1398_ = lean_apply_4(v___x_24510__overap_1396_, v___y_1368_, v___x_1397_, v___y_1370_, v___y_1371_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___boxed(lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v___y_25789__boxed_1404_; lean_object* v_res_1405_; 
v___y_25789__boxed_1404_ = lean_unbox(v___y_1401_);
v_res_1405_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v_msg_1399_, v___y_1400_, v___y_25789__boxed_1404_, v___y_1402_, v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg(lean_object* v_m_1406_, lean_object* v_query_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v_zero_1411_; uint8_t v_isZero_1412_; 
v_zero_1411_ = lean_unsigned_to_nat(0u);
v_isZero_1412_ = lean_nat_dec_eq(v_x_1409_, v_zero_1411_);
if (v_isZero_1412_ == 1)
{
lean_dec(v_x_1410_);
lean_dec(v_x_1409_);
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_box(2);
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_val_1414_ = lean_ctor_get(v_x_1408_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_x_1408_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v_x_1408_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_val_1414_);
lean_dec(v_x_1408_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_val_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_keyArray_1422_; lean_object* v_valueArray_1423_; lean_object* v___x_1424_; uint8_t v_isSome_1425_; 
v_keyArray_1422_ = lean_ctor_get(v_m_1406_, 1);
v_valueArray_1423_ = lean_ctor_get(v_m_1406_, 2);
v___x_1424_ = lean_array_fget_borrowed(v_keyArray_1422_, v_x_1410_);
v_isSome_1425_ = lean_noption_is_some(v___x_1424_);
if (v_isSome_1425_ == 0)
{
lean_dec(v_x_1409_);
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_x_1410_);
return v___x_1426_;
}
else
{
lean_object* v_val_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_x_1410_);
v_val_1427_ = lean_ctor_get(v_x_1408_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1408_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v_x_1408_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_val_1427_);
lean_dec(v_x_1408_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_val_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_one_1435_; lean_object* v_n_1436_; lean_object* v___y_1438_; 
v_one_1435_ = lean_unsigned_to_nat(1u);
v_n_1436_ = lean_nat_sub(v_x_1409_, v_one_1435_);
lean_dec(v_x_1409_);
if (v_isSome_1425_ == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v___x_1446_; uint8_t v_isSome_1447_; 
v___x_1446_ = lean_array_fget_borrowed(v_valueArray_1423_, v_x_1410_);
v_isSome_1447_ = lean_noption_is_some(v___x_1446_);
if (v_isSome_1447_ == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v_val_1448_; lean_object* v_fst_1449_; lean_object* v_snd_1450_; lean_object* v_fst_1451_; lean_object* v_snd_1452_; lean_object* v_val_1453_; uint8_t v___y_1455_; size_t v___x_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
lean_inc(v___x_1424_);
v_val_1448_ = lean_noption_get(v___x_1424_);
v_fst_1449_ = lean_ctor_get(v_val_1448_, 0);
lean_inc(v_fst_1449_);
v_snd_1450_ = lean_ctor_get(v_val_1448_, 1);
lean_inc(v_snd_1450_);
v_fst_1451_ = lean_ctor_get(v_query_1407_, 0);
v_snd_1452_ = lean_ctor_get(v_query_1407_, 1);
lean_inc(v___x_1446_);
v_val_1453_ = lean_noption_get(v___x_1446_);
v___x_1462_ = lean_ptr_addr(v_fst_1449_);
lean_dec(v_fst_1449_);
v___x_1463_ = lean_ptr_addr(v_fst_1451_);
v___x_1464_ = lean_usize_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_snd_1450_);
v___y_1455_ = v___x_1464_;
goto v___jp_1454_;
}
else
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_nat_dec_eq(v_snd_1450_, v_snd_1452_);
lean_dec(v_snd_1450_);
v___y_1455_ = v___x_1465_;
goto v___jp_1454_;
}
v___jp_1454_:
{
if (v___y_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
lean_dec(v_val_1453_);
lean_dec(v_val_1448_);
v___x_1456_ = lean_array_get_size(v_keyArray_1422_);
v___x_1457_ = lean_nat_add(v_x_1410_, v_one_1435_);
lean_dec(v_x_1410_);
v___x_1458_ = lean_nat_dec_lt(v___x_1457_, v___x_1456_);
if (v___x_1458_ == 0)
{
lean_dec(v___x_1457_);
v_x_1409_ = v_n_1436_;
v_x_1410_ = v_zero_1411_;
goto _start;
}
else
{
v_x_1409_ = v_n_1436_;
v_x_1410_ = v___x_1457_;
goto _start;
}
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_n_1436_);
lean_dec(v_x_1408_);
v___x_1461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1461_, 0, v_x_1410_);
lean_ctor_set(v___x_1461_, 1, v_val_1448_);
lean_ctor_set(v___x_1461_, 2, v_val_1453_);
return v___x_1461_;
}
}
}
}
v___jp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_array_get_size(v_keyArray_1422_);
v___x_1440_ = lean_nat_add(v_x_1410_, v_one_1435_);
lean_dec(v_x_1410_);
v___x_1441_ = lean_nat_dec_lt(v___x_1440_, v___x_1439_);
if (v___x_1441_ == 0)
{
lean_dec(v___x_1440_);
v_x_1408_ = v___y_1438_;
v_x_1409_ = v_n_1436_;
v_x_1410_ = v_zero_1411_;
goto _start;
}
else
{
v_x_1408_ = v___y_1438_;
v_x_1409_ = v_n_1436_;
v_x_1410_ = v___x_1440_;
goto _start;
}
}
v___jp_1444_:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v___x_1445_; 
lean_inc(v_x_1410_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_x_1410_);
v___y_1438_ = v___x_1445_;
goto v___jp_1437_;
}
else
{
v___y_1438_ = v_x_1408_;
goto v___jp_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg___boxed(lean_object* v_m_1466_, lean_object* v_query_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg(v_m_1466_, v_query_1467_, v_x_1468_, v_x_1469_, v_x_1470_);
lean_dec_ref(v_query_1467_);
lean_dec_ref(v_m_1466_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg(lean_object* v_m_1472_, lean_object* v_query_1473_){
_start:
{
lean_object* v_keyArray_1474_; lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; uint64_t v___x_1481_; uint64_t v___x_1482_; uint64_t v___x_1483_; uint64_t v___x_1484_; uint64_t v___x_1485_; uint64_t v_fold_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_keyArray_1474_ = lean_ctor_get(v_m_1472_, 1);
v_fst_1475_ = lean_ctor_get(v_query_1473_, 0);
v_snd_1476_ = lean_ctor_get(v_query_1473_, 1);
v___x_1477_ = lean_array_get_size(v_keyArray_1474_);
v___x_1478_ = lean_ptr_addr(v_fst_1475_);
v___x_1479_ = ((size_t)3ULL);
v___x_1480_ = lean_usize_shift_right(v___x_1478_, v___x_1479_);
v___x_1481_ = lean_usize_to_uint64(v___x_1480_);
v___x_1482_ = lean_uint64_of_nat(v_snd_1476_);
v___x_1483_ = lean_uint64_mix_hash(v___x_1481_, v___x_1482_);
v___x_1484_ = 32ULL;
v___x_1485_ = lean_uint64_shift_right(v___x_1483_, v___x_1484_);
v_fold_1486_ = lean_uint64_xor(v___x_1483_, v___x_1485_);
v___x_1487_ = 16ULL;
v___x_1488_ = lean_uint64_shift_right(v_fold_1486_, v___x_1487_);
v___x_1489_ = lean_uint64_xor(v_fold_1486_, v___x_1488_);
v___x_1490_ = lean_uint64_to_usize(v___x_1489_);
v___x_1491_ = lean_usize_of_nat(v___x_1477_);
v___x_1492_ = ((size_t)1ULL);
v___x_1493_ = lean_usize_sub(v___x_1491_, v___x_1492_);
v___x_1494_ = lean_usize_land(v___x_1490_, v___x_1493_);
v___x_1495_ = lean_usize_to_nat(v___x_1494_);
v___x_1496_ = lean_box(0);
v___x_1497_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg(v_m_1472_, v_query_1473_, v___x_1496_, v___x_1477_, v___x_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg___boxed(lean_object* v_m_1498_, lean_object* v_query_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg(v_m_1498_, v_query_1499_);
lean_dec_ref(v_query_1499_);
lean_dec_ref(v_m_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_m_1501_, lean_object* v_query_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg(v_m_1501_, v_query_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_index_1504_; lean_object* v_key_1505_; lean_object* v_value_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_index_1504_ = lean_ctor_get(v___x_1503_, 0);
v_key_1505_ = lean_ctor_get(v___x_1503_, 1);
v_value_1506_ = lean_ctor_get(v___x_1503_, 2);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1503_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_value_1506_);
lean_inc(v_key_1505_);
lean_inc(v_index_1504_);
lean_dec(v___x_1503_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_index_1504_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_key_1505_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_value_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v___x_1514_; 
lean_dec(v___x_1503_);
v___x_1514_ = lean_box(1);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_m_1515_, lean_object* v_query_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_m_1515_, v_query_1516_);
lean_dec_ref(v_query_1516_);
lean_dec_ref(v_m_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(lean_object* v_m_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_m_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_value_1521_; lean_object* v___x_1522_; 
v_value_1521_ = lean_ctor_get(v___x_1520_, 2);
lean_inc(v_value_1521_);
lean_dec_ref_known(v___x_1520_, 3);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_value_1521_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1524_, v_a_1525_);
lean_dec_ref(v_a_1525_);
lean_dec_ref(v_m_1524_);
return v_res_1526_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Array_instInhabited(lean_box(0));
return v___x_1527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3));
v___x_1532_ = lean_unsigned_to_nat(12u);
v___x_1533_ = lean_unsigned_to_nat(234u);
v___x_1534_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2));
v___x_1535_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_1536_ = l_mkPanicMessageWithDecl(v___x_1535_, v___x_1534_, v___x_1533_, v___x_1532_, v___x_1531_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1541_ = lean_unsigned_to_nat(67u);
v___x_1542_ = lean_unsigned_to_nat(35u);
v___x_1543_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___x_1544_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___x_1545_ = l_mkPanicMessageWithDecl(v___x_1544_, v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_n_1546_, lean_object* v_varDeps_1547_, lean_object* v_xs_1548_, lean_object* v_e_1549_, lean_object* v_offset_1550_, lean_object* v_a_1551_, uint8_t v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
switch(lean_obj_tag(v_e_1549_))
{
case 5:
{
lean_object* v_fn_1555_; lean_object* v_arg_1556_; lean_object* v___x_1557_; 
v_fn_1555_ = lean_ctor_get(v_e_1549_, 0);
v_arg_1556_ = lean_ctor_get(v_e_1549_, 1);
lean_inc(v_offset_1550_);
lean_inc_ref(v_fn_1555_);
v___x_1557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_fn_1555_, v_offset_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v_a_1559_; lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v___x_1562_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
v_a_1559_ = lean_ctor_get(v___x_1557_, 1);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1557_, 2);
v_fst_1560_ = lean_ctor_get(v_a_1558_, 0);
lean_inc(v_fst_1560_);
v_snd_1561_ = lean_ctor_get(v_a_1558_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_a_1558_);
lean_inc_ref(v_arg_1556_);
v___x_1562_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_arg_1556_, v_offset_1550_, v_snd_1561_, v_a_1552_, v_a_1553_, v_a_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1589_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_a_1564_ = lean_ctor_get(v___x_1562_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1566_ = v___x_1562_;
v_isShared_1567_ = v_isSharedCheck_1589_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1589_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1588_; 
v_fst_1568_ = lean_ctor_get(v_a_1563_, 0);
v_snd_1569_ = lean_ctor_get(v_a_1563_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_a_1563_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1571_ = v_a_1563_;
v_isShared_1572_ = v_isSharedCheck_1588_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snd_1569_);
lean_inc(v_fst_1568_);
lean_dec(v_a_1563_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1588_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___y_1574_; size_t v___x_1582_; size_t v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = lean_ptr_addr(v_fn_1555_);
v___x_1583_ = lean_ptr_addr(v_fst_1560_);
v___x_1584_ = lean_usize_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
v___y_1574_ = v___x_1584_;
goto v___jp_1573_;
}
else
{
size_t v___x_1585_; size_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_ptr_addr(v_arg_1556_);
v___x_1586_ = lean_ptr_addr(v_fst_1568_);
v___x_1587_ = lean_usize_dec_eq(v___x_1585_, v___x_1586_);
v___y_1574_ = v___x_1587_;
goto v___jp_1573_;
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_del_object(v___x_1571_);
lean_del_object(v___x_1566_);
lean_dec_ref_known(v_e_1549_, 2);
v___x_1575_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1560_, v_fst_1568_, v_snd_1569_, v_a_1552_, v_a_1553_, v_a_1564_);
return v___x_1575_;
}
else
{
lean_object* v___x_1577_; 
lean_dec(v_fst_1568_);
lean_dec(v_fst_1560_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_e_1549_);
v___x_1577_ = v___x_1571_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_e_1549_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_snd_1569_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1577_);
v___x_1579_ = v___x_1566_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_a_1564_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1560_);
lean_dec_ref_known(v_e_1549_, 2);
return v___x_1562_;
}
}
else
{
lean_dec_ref_known(v_e_1549_, 2);
lean_dec(v_offset_1550_);
return v___x_1557_;
}
}
case 6:
{
lean_object* v_binderName_1590_; lean_object* v_binderType_1591_; lean_object* v_body_1592_; uint8_t v_binderInfo_1593_; lean_object* v___x_1594_; 
v_binderName_1590_ = lean_ctor_get(v_e_1549_, 0);
v_binderType_1591_ = lean_ctor_get(v_e_1549_, 1);
v_body_1592_ = lean_ctor_get(v_e_1549_, 2);
v_binderInfo_1593_ = lean_ctor_get_uint8(v_e_1549_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1550_);
lean_inc_ref(v_binderType_1591_);
v___x_1594_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_binderType_1591_, v_offset_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v_a_1596_; lean_object* v_fst_1597_; lean_object* v_snd_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
v_a_1596_ = lean_ctor_get(v___x_1594_, 1);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1594_, 2);
v_fst_1597_ = lean_ctor_get(v_a_1595_, 0);
lean_inc(v_fst_1597_);
v_snd_1598_ = lean_ctor_get(v_a_1595_, 1);
lean_inc(v_snd_1598_);
lean_dec(v_a_1595_);
v___x_1599_ = lean_unsigned_to_nat(1u);
v___x_1600_ = lean_nat_add(v_offset_1550_, v___x_1599_);
lean_dec(v_offset_1550_);
lean_inc_ref(v_body_1592_);
v___x_1601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_body_1592_, v___x_1600_, v_snd_1598_, v_a_1552_, v_a_1553_, v_a_1596_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1628_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_a_1603_ = lean_ctor_get(v___x_1601_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1605_ = v___x_1601_;
v_isShared_1606_ = v_isSharedCheck_1628_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1628_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_fst_1607_; lean_object* v_snd_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1627_; 
v_fst_1607_ = lean_ctor_get(v_a_1602_, 0);
v_snd_1608_ = lean_ctor_get(v_a_1602_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1610_ = v_a_1602_;
v_isShared_1611_ = v_isSharedCheck_1627_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_snd_1608_);
lean_inc(v_fst_1607_);
lean_dec(v_a_1602_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1627_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
uint8_t v___y_1613_; size_t v___x_1621_; size_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1621_ = lean_ptr_addr(v_binderType_1591_);
v___x_1622_ = lean_ptr_addr(v_fst_1597_);
v___x_1623_ = lean_usize_dec_eq(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
v___y_1613_ = v___x_1623_;
goto v___jp_1612_;
}
else
{
size_t v___x_1624_; size_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1624_ = lean_ptr_addr(v_body_1592_);
v___x_1625_ = lean_ptr_addr(v_fst_1607_);
v___x_1626_ = lean_usize_dec_eq(v___x_1624_, v___x_1625_);
v___y_1613_ = v___x_1626_;
goto v___jp_1612_;
}
v___jp_1612_:
{
if (v___y_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc(v_binderName_1590_);
lean_del_object(v___x_1610_);
lean_del_object(v___x_1605_);
lean_dec_ref_known(v_e_1549_, 3);
v___x_1614_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1590_, v_binderInfo_1593_, v_fst_1597_, v_fst_1607_, v_snd_1608_, v_a_1552_, v_a_1553_, v_a_1603_);
return v___x_1614_;
}
else
{
lean_object* v___x_1616_; 
lean_dec(v_fst_1607_);
lean_dec(v_fst_1597_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_e_1549_);
v___x_1616_ = v___x_1610_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_e_1549_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_snd_1608_);
v___x_1616_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1616_);
v___x_1618_ = v___x_1605_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_a_1603_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1597_);
lean_dec_ref_known(v_e_1549_, 3);
return v___x_1601_;
}
}
else
{
lean_dec_ref_known(v_e_1549_, 3);
lean_dec(v_offset_1550_);
return v___x_1594_;
}
}
case 7:
{
lean_object* v_binderName_1629_; lean_object* v_binderType_1630_; lean_object* v_body_1631_; uint8_t v_binderInfo_1632_; lean_object* v___x_1633_; 
v_binderName_1629_ = lean_ctor_get(v_e_1549_, 0);
v_binderType_1630_ = lean_ctor_get(v_e_1549_, 1);
v_body_1631_ = lean_ctor_get(v_e_1549_, 2);
v_binderInfo_1632_ = lean_ctor_get_uint8(v_e_1549_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1550_);
lean_inc_ref(v_binderType_1630_);
v___x_1633_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_binderType_1630_, v_offset_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v_a_1635_; lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
v_a_1635_ = lean_ctor_get(v___x_1633_, 1);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1633_, 2);
v_fst_1636_ = lean_ctor_get(v_a_1634_, 0);
lean_inc(v_fst_1636_);
v_snd_1637_ = lean_ctor_get(v_a_1634_, 1);
lean_inc(v_snd_1637_);
lean_dec(v_a_1634_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_offset_1550_, v___x_1638_);
lean_dec(v_offset_1550_);
lean_inc_ref(v_body_1631_);
v___x_1640_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_body_1631_, v___x_1639_, v_snd_1637_, v_a_1552_, v_a_1553_, v_a_1635_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1667_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_a_1642_ = lean_ctor_get(v___x_1640_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1644_ = v___x_1640_;
v_isShared_1645_ = v_isSharedCheck_1667_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1667_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_fst_1646_; lean_object* v_snd_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1666_; 
v_fst_1646_ = lean_ctor_get(v_a_1641_, 0);
v_snd_1647_ = lean_ctor_get(v_a_1641_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_a_1641_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1649_ = v_a_1641_;
v_isShared_1650_ = v_isSharedCheck_1666_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_snd_1647_);
lean_inc(v_fst_1646_);
lean_dec(v_a_1641_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1666_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
uint8_t v___y_1652_; size_t v___x_1660_; size_t v___x_1661_; uint8_t v___x_1662_; 
v___x_1660_ = lean_ptr_addr(v_binderType_1630_);
v___x_1661_ = lean_ptr_addr(v_fst_1636_);
v___x_1662_ = lean_usize_dec_eq(v___x_1660_, v___x_1661_);
if (v___x_1662_ == 0)
{
v___y_1652_ = v___x_1662_;
goto v___jp_1651_;
}
else
{
size_t v___x_1663_; size_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_ptr_addr(v_body_1631_);
v___x_1664_ = lean_ptr_addr(v_fst_1646_);
v___x_1665_ = lean_usize_dec_eq(v___x_1663_, v___x_1664_);
v___y_1652_ = v___x_1665_;
goto v___jp_1651_;
}
v___jp_1651_:
{
if (v___y_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_inc(v_binderName_1629_);
lean_del_object(v___x_1649_);
lean_del_object(v___x_1644_);
lean_dec_ref_known(v_e_1549_, 3);
v___x_1653_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1629_, v_binderInfo_1632_, v_fst_1636_, v_fst_1646_, v_snd_1647_, v_a_1552_, v_a_1553_, v_a_1642_);
return v___x_1653_;
}
else
{
lean_object* v___x_1655_; 
lean_dec(v_fst_1646_);
lean_dec(v_fst_1636_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_e_1549_);
v___x_1655_ = v___x_1649_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_e_1549_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1647_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1655_);
v___x_1657_ = v___x_1644_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_a_1642_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1636_);
lean_dec_ref_known(v_e_1549_, 3);
return v___x_1640_;
}
}
else
{
lean_dec_ref_known(v_e_1549_, 3);
lean_dec(v_offset_1550_);
return v___x_1633_;
}
}
case 8:
{
lean_object* v_declName_1668_; lean_object* v_type_1669_; lean_object* v_value_1670_; lean_object* v_body_1671_; uint8_t v_nondep_1672_; lean_object* v___x_1673_; 
v_declName_1668_ = lean_ctor_get(v_e_1549_, 0);
v_type_1669_ = lean_ctor_get(v_e_1549_, 1);
v_value_1670_ = lean_ctor_get(v_e_1549_, 2);
v_body_1671_ = lean_ctor_get(v_e_1549_, 3);
v_nondep_1672_ = lean_ctor_get_uint8(v_e_1549_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1550_);
lean_inc_ref(v_type_1669_);
v___x_1673_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_type_1669_, v_offset_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_a_1675_; lean_object* v_fst_1676_; lean_object* v_snd_1677_; lean_object* v___x_1678_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
v_a_1675_ = lean_ctor_get(v___x_1673_, 1);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1673_, 2);
v_fst_1676_ = lean_ctor_get(v_a_1674_, 0);
lean_inc(v_fst_1676_);
v_snd_1677_ = lean_ctor_get(v_a_1674_, 1);
lean_inc(v_snd_1677_);
lean_dec(v_a_1674_);
lean_inc(v_offset_1550_);
lean_inc_ref(v_value_1670_);
v___x_1678_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_value_1670_, v_offset_1550_, v_snd_1677_, v_a_1552_, v_a_1553_, v_a_1675_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v_a_1680_; lean_object* v_fst_1681_; lean_object* v_snd_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
v_a_1680_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1678_, 2);
v_fst_1681_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_fst_1681_);
v_snd_1682_ = lean_ctor_get(v_a_1679_, 1);
lean_inc(v_snd_1682_);
lean_dec(v_a_1679_);
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v_offset_1550_, v___x_1683_);
lean_dec(v_offset_1550_);
lean_inc_ref(v_body_1671_);
v___x_1685_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_body_1671_, v___x_1684_, v_snd_1682_, v_a_1552_, v_a_1553_, v_a_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1716_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_a_1687_ = lean_ctor_get(v___x_1685_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1689_ = v___x_1685_;
v_isShared_1690_ = v_isSharedCheck_1716_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1716_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_fst_1691_; lean_object* v_snd_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1715_; 
v_fst_1691_ = lean_ctor_get(v_a_1686_, 0);
v_snd_1692_ = lean_ctor_get(v_a_1686_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_a_1686_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1694_ = v_a_1686_;
v_isShared_1695_ = v_isSharedCheck_1715_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_snd_1692_);
lean_inc(v_fst_1691_);
lean_dec(v_a_1686_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1715_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v___y_1697_; size_t v___x_1709_; size_t v___x_1710_; uint8_t v___x_1711_; 
v___x_1709_ = lean_ptr_addr(v_type_1669_);
v___x_1710_ = lean_ptr_addr(v_fst_1676_);
v___x_1711_ = lean_usize_dec_eq(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
v___y_1697_ = v___x_1711_;
goto v___jp_1696_;
}
else
{
size_t v___x_1712_; size_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = lean_ptr_addr(v_value_1670_);
v___x_1713_ = lean_ptr_addr(v_fst_1681_);
v___x_1714_ = lean_usize_dec_eq(v___x_1712_, v___x_1713_);
v___y_1697_ = v___x_1714_;
goto v___jp_1696_;
}
v___jp_1696_:
{
if (v___y_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_inc(v_declName_1668_);
lean_del_object(v___x_1694_);
lean_del_object(v___x_1689_);
lean_dec_ref_known(v_e_1549_, 4);
v___x_1698_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1668_, v_fst_1676_, v_fst_1681_, v_fst_1691_, v_nondep_1672_, v_snd_1692_, v_a_1552_, v_a_1553_, v_a_1687_);
return v___x_1698_;
}
else
{
size_t v___x_1699_; size_t v___x_1700_; uint8_t v___x_1701_; 
v___x_1699_ = lean_ptr_addr(v_body_1671_);
v___x_1700_ = lean_ptr_addr(v_fst_1691_);
v___x_1701_ = lean_usize_dec_eq(v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
lean_inc(v_declName_1668_);
lean_del_object(v___x_1694_);
lean_del_object(v___x_1689_);
lean_dec_ref_known(v_e_1549_, 4);
v___x_1702_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1668_, v_fst_1676_, v_fst_1681_, v_fst_1691_, v_nondep_1672_, v_snd_1692_, v_a_1552_, v_a_1553_, v_a_1687_);
return v___x_1702_;
}
else
{
lean_object* v___x_1704_; 
lean_dec(v_fst_1691_);
lean_dec(v_fst_1681_);
lean_dec(v_fst_1676_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v_e_1549_);
v___x_1704_ = v___x_1694_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_e_1549_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_snd_1692_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1704_);
v___x_1706_ = v___x_1689_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1687_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
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
lean_dec(v_fst_1681_);
lean_dec(v_fst_1676_);
lean_dec_ref_known(v_e_1549_, 4);
return v___x_1685_;
}
}
else
{
lean_dec(v_fst_1676_);
lean_dec_ref_known(v_e_1549_, 4);
lean_dec(v_offset_1550_);
return v___x_1678_;
}
}
else
{
lean_dec_ref_known(v_e_1549_, 4);
lean_dec(v_offset_1550_);
return v___x_1673_;
}
}
case 10:
{
lean_object* v_data_1717_; lean_object* v_expr_1718_; lean_object* v___x_1719_; 
v_data_1717_ = lean_ctor_get(v_e_1549_, 0);
v_expr_1718_ = lean_ctor_get(v_e_1549_, 1);
lean_inc_ref(v_expr_1718_);
v___x_1719_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_expr_1718_, v_offset_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1741_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_a_1721_ = lean_ctor_get(v___x_1719_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1723_ = v___x_1719_;
v_isShared_1724_ = v_isSharedCheck_1741_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1741_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1740_; 
v_fst_1725_ = lean_ctor_get(v_a_1720_, 0);
v_snd_1726_ = lean_ctor_get(v_a_1720_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_a_1720_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1728_ = v_a_1720_;
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snd_1726_);
lean_inc(v_fst_1725_);
lean_dec(v_a_1720_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
size_t v___x_1730_; size_t v___x_1731_; uint8_t v___x_1732_; 
v___x_1730_ = lean_ptr_addr(v_expr_1718_);
v___x_1731_ = lean_ptr_addr(v_fst_1725_);
v___x_1732_ = lean_usize_dec_eq(v___x_1730_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
lean_inc(v_data_1717_);
lean_del_object(v___x_1728_);
lean_del_object(v___x_1723_);
lean_dec_ref_known(v_e_1549_, 2);
v___x_1733_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_data_1717_, v_fst_1725_, v_snd_1726_, v_a_1552_, v_a_1553_, v_a_1721_);
return v___x_1733_;
}
else
{
lean_object* v___x_1735_; 
lean_dec(v_fst_1725_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_e_1549_);
v___x_1735_ = v___x_1728_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_e_1549_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_snd_1726_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1735_);
v___x_1737_ = v___x_1723_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_a_1721_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1549_, 2);
return v___x_1719_;
}
}
case 11:
{
lean_object* v_typeName_1742_; lean_object* v_idx_1743_; lean_object* v_struct_1744_; lean_object* v___x_1745_; 
v_typeName_1742_ = lean_ctor_get(v_e_1549_, 0);
v_idx_1743_ = lean_ctor_get(v_e_1549_, 1);
v_struct_1744_ = lean_ctor_get(v_e_1549_, 2);
lean_inc_ref(v_struct_1744_);
v___x_1745_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1546_, v_varDeps_1547_, v_xs_1548_, v_struct_1744_, v_offset_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1767_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_a_1747_ = lean_ctor_get(v___x_1745_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1749_ = v___x_1745_;
v_isShared_1750_ = v_isSharedCheck_1767_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1767_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1766_; 
v_fst_1751_ = lean_ctor_get(v_a_1746_, 0);
v_snd_1752_ = lean_ctor_get(v_a_1746_, 1);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_a_1746_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1754_ = v_a_1746_;
v_isShared_1755_ = v_isSharedCheck_1766_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snd_1752_);
lean_inc(v_fst_1751_);
lean_dec(v_a_1746_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1766_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
size_t v___x_1756_; size_t v___x_1757_; uint8_t v___x_1758_; 
v___x_1756_ = lean_ptr_addr(v_struct_1744_);
v___x_1757_ = lean_ptr_addr(v_fst_1751_);
v___x_1758_ = lean_usize_dec_eq(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_inc(v_idx_1743_);
lean_inc(v_typeName_1742_);
lean_del_object(v___x_1754_);
lean_del_object(v___x_1749_);
lean_dec_ref_known(v_e_1549_, 3);
v___x_1759_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_typeName_1742_, v_idx_1743_, v_fst_1751_, v_snd_1752_, v_a_1552_, v_a_1553_, v_a_1747_);
return v___x_1759_;
}
else
{
lean_object* v___x_1761_; 
lean_dec(v_fst_1751_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v_e_1549_);
v___x_1761_ = v___x_1754_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_e_1549_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_snd_1752_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1761_);
v___x_1763_ = v___x_1749_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_a_1747_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1549_, 3);
return v___x_1745_;
}
}
default: 
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v_offset_1550_);
lean_dec_ref(v_e_1549_);
v___x_1768_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3);
v___x_1769_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v___x_1768_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(lean_object* v_n_1770_, lean_object* v_varDeps_1771_, lean_object* v_xs_1772_, lean_object* v_e_1773_, lean_object* v_offset_1774_, lean_object* v_a_1775_, uint8_t v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_key_1779_; lean_object* v_a_1781_; lean_object* v___x_1794_; 
lean_inc(v_offset_1774_);
lean_inc_ref(v_e_1773_);
v_key_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1779_, 0, v_e_1773_);
lean_ctor_set(v_key_1779_, 1, v_offset_1774_);
v___x_1794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_a_1775_, v_key_1779_);
if (lean_obj_tag(v___x_1794_) == 1)
{
lean_object* v_val_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref_known(v_key_1779_, 2);
lean_dec(v_offset_1774_);
lean_dec_ref(v_e_1773_);
v_val_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_val_1795_);
lean_ctor_set(v___x_1796_, 1, v_a_1775_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_a_1778_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_dec(v___x_1794_);
v___x_1798_ = l_Lean_Expr_looseBVarRange(v_e_1773_);
v___x_1799_ = lean_nat_dec_le(v___x_1798_, v_offset_1774_);
lean_dec(v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Expr_getAppFn(v_e_1773_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_deBruijnIndex_1801_; uint8_t v___x_1802_; 
v_deBruijnIndex_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_deBruijnIndex_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_nat_dec_le(v_offset_1774_, v_deBruijnIndex_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_dec(v_deBruijnIndex_1801_);
lean_dec(v_offset_1774_);
v___x_1803_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = lean_nat_add(v_offset_1774_, v_n_1770_);
v___x_1805_ = lean_nat_dec_lt(v_deBruijnIndex_1801_, v___x_1804_);
lean_dec(v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec(v_offset_1774_);
lean_dec_ref(v_e_1773_);
v___x_1806_ = lean_nat_sub(v_deBruijnIndex_1801_, v_n_1770_);
lean_dec(v_deBruijnIndex_1801_);
v___x_1807_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1806_, v_a_1778_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
v_a_1809_ = lean_ctor_get(v___x_1807_, 1);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1807_, 2);
v___x_1810_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_a_1808_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1809_);
return v___x_1810_;
}
else
{
lean_object* v_a_1811_; lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref_known(v_key_1779_, 2);
lean_dec_ref(v_a_1775_);
v_a_1811_ = lean_ctor_get(v___x_1807_, 0);
v_a_1812_ = lean_ctor_get(v___x_1807_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1807_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_inc(v_a_1811_);
lean_dec(v___x_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1811_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_i_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_expectedNumArgs_1826_; lean_object* v_numArgs_1827_; uint8_t v___x_1828_; 
v___x_1820_ = lean_nat_sub(v_deBruijnIndex_1801_, v_offset_1774_);
lean_dec(v_deBruijnIndex_1801_);
v___x_1821_ = lean_nat_sub(v_n_1770_, v___x_1820_);
lean_dec(v___x_1820_);
v___x_1822_ = lean_unsigned_to_nat(1u);
v_i_1823_ = lean_nat_sub(v___x_1821_, v___x_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1825_ = lean_array_get_borrowed(v___x_1824_, v_varDeps_1771_, v_i_1823_);
v_expectedNumArgs_1826_ = lean_array_get_size(v___x_1825_);
v_numArgs_1827_ = l_Lean_Expr_getAppNumArgs(v_e_1773_);
v___x_1828_ = lean_nat_dec_lt(v_expectedNumArgs_1826_, v_numArgs_1827_);
if (v___x_1828_ == 0)
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_nat_dec_eq(v_numArgs_1827_, v_expectedNumArgs_1826_);
lean_dec(v_numArgs_1827_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec(v_i_1823_);
v___x_1830_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1831_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1830_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
if (lean_obj_tag(v_a_1832_) == 1)
{
lean_object* v_a_1833_; lean_object* v_val_1834_; lean_object* v___x_1835_; 
lean_dec(v_offset_1774_);
lean_dec_ref(v_e_1773_);
v_a_1833_ = lean_ctor_get(v___x_1831_, 1);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1831_, 2);
v_val_1834_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_val_1834_);
lean_dec_ref_known(v_a_1832_, 1);
v___x_1835_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_val_1834_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1833_);
return v___x_1835_;
}
else
{
lean_object* v_a_1836_; 
lean_dec(v_a_1832_);
v_a_1836_ = lean_ctor_get(v___x_1831_, 1);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1831_, 2);
v_a_1781_ = v_a_1836_;
goto v___jp_1780_;
}
}
else
{
lean_object* v_a_1837_; lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref_known(v_key_1779_, 2);
lean_dec_ref(v_a_1775_);
lean_dec(v_offset_1774_);
lean_dec_ref(v_e_1773_);
v_a_1837_ = lean_ctor_get(v___x_1831_, 0);
v_a_1838_ = lean_ctor_get(v___x_1831_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1831_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_inc(v_a_1837_);
lean_dec(v___x_1831_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1837_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec(v_offset_1774_);
lean_dec_ref(v_e_1773_);
v___x_1846_ = lean_array_fget_borrowed(v_xs_1772_, v_i_1823_);
lean_dec(v_i_1823_);
lean_inc(v___x_1846_);
v___x_1847_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v___x_1846_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
return v___x_1847_;
}
}
else
{
lean_dec(v_numArgs_1827_);
lean_dec(v_i_1823_);
v_a_1781_ = v_a_1778_;
goto v___jp_1780_;
}
}
}
}
else
{
lean_dec_ref(v___x_1800_);
v_a_1781_ = v_a_1778_;
goto v___jp_1780_;
}
}
else
{
lean_object* v___x_1848_; 
lean_dec(v_offset_1774_);
v___x_1848_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
return v___x_1848_;
}
}
v___jp_1780_:
{
switch(lean_obj_tag(v_e_1773_))
{
case 9:
{
lean_object* v___x_1782_; 
lean_dec(v_offset_1774_);
v___x_1782_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
return v___x_1782_;
}
case 2:
{
lean_object* v___x_1783_; 
lean_dec(v_offset_1774_);
v___x_1783_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
return v___x_1783_;
}
case 0:
{
lean_object* v___x_1784_; 
lean_dec(v_offset_1774_);
v___x_1784_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
return v___x_1784_;
}
case 1:
{
lean_object* v___x_1785_; 
lean_dec(v_offset_1774_);
v___x_1785_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
return v___x_1785_;
}
case 4:
{
lean_object* v___x_1786_; 
lean_dec(v_offset_1774_);
v___x_1786_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
return v___x_1786_;
}
case 3:
{
lean_object* v___x_1787_; 
lean_dec(v_offset_1774_);
v___x_1787_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_e_1773_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
return v___x_1787_;
}
default: 
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1770_, v_varDeps_1771_, v_xs_1772_, v_e_1773_, v_offset_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1781_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v_a_1790_; lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v___x_1793_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
v_a_1790_ = lean_ctor_get(v___x_1788_, 1);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1788_, 2);
v_fst_1791_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_fst_1791_);
v_snd_1792_ = lean_ctor_get(v_a_1789_, 1);
lean_inc(v_snd_1792_);
lean_dec(v_a_1789_);
v___x_1793_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1779_, v_fst_1791_, v_snd_1792_, v_a_1776_, v_a_1777_, v_a_1790_);
return v___x_1793_;
}
else
{
lean_dec_ref_known(v_key_1779_, 2);
return v___x_1788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___boxed(lean_object* v_n_1849_, lean_object* v_varDeps_1850_, lean_object* v_xs_1851_, lean_object* v_e_1852_, lean_object* v_offset_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
uint8_t v_a_boxed_1858_; lean_object* v_res_1859_; 
v_a_boxed_1858_ = lean_unbox(v_a_1855_);
v_res_1859_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1849_, v_varDeps_1850_, v_xs_1851_, v_e_1852_, v_offset_1853_, v_a_1854_, v_a_boxed_1858_, v_a_1856_, v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec_ref(v_xs_1851_);
lean_dec_ref(v_varDeps_1850_);
lean_dec(v_n_1849_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_n_1860_, lean_object* v_varDeps_1861_, lean_object* v_xs_1862_, lean_object* v_e_1863_, lean_object* v_offset_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
uint8_t v_a_boxed_1869_; lean_object* v_res_1870_; 
v_a_boxed_1869_ = lean_unbox(v_a_1866_);
v_res_1870_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1860_, v_varDeps_1861_, v_xs_1862_, v_e_1863_, v_offset_1864_, v_a_1865_, v_a_boxed_1869_, v_a_1867_, v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec_ref(v_xs_1862_);
lean_dec_ref(v_varDeps_1861_);
lean_dec(v_n_1860_);
return v_res_1870_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0(void){
_start:
{
lean_object* v_cellCount_1871_; lean_object* v___x_1872_; 
v_cellCount_1871_ = lean_unsigned_to_nat(16u);
v___x_1872_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_1873_; lean_object* v___x_1874_; 
v_cellCount_1873_ = lean_unsigned_to_nat(16u);
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1);
v___x_1876_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1876_);
lean_ctor_set(v___x_1878_, 2, v___x_1875_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object* v_e_1879_, lean_object* v_n_1880_, lean_object* v_varDeps_1881_, lean_object* v_xs_1882_, uint8_t v_debug_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1886_; lean_object* v_a_1888_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1916_ = l_Lean_Expr_looseBVarRange(v_e_1879_);
v___x_1917_ = lean_nat_dec_le(v___x_1916_, v___x_1886_);
lean_dec(v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_Expr_getAppFn(v_e_1879_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_deBruijnIndex_1919_; uint8_t v___x_1920_; 
v_deBruijnIndex_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_deBruijnIndex_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1920_ = lean_nat_dec_le(v___x_1886_, v_deBruijnIndex_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_dec(v_deBruijnIndex_1919_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_e_1879_);
lean_ctor_set(v___x_1921_, 1, v___y_1885_);
return v___x_1921_;
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_nat_dec_lt(v_deBruijnIndex_1919_, v_n_1880_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec_ref(v_e_1879_);
v___x_1923_ = lean_nat_sub(v_deBruijnIndex_1919_, v_n_1880_);
lean_dec(v_deBruijnIndex_1919_);
v___x_1924_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1923_, v___y_1885_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_i_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v_expectedNumArgs_1930_; lean_object* v_numArgs_1931_; uint8_t v___x_1932_; 
v___x_1925_ = lean_nat_sub(v_n_1880_, v_deBruijnIndex_1919_);
lean_dec(v_deBruijnIndex_1919_);
v___x_1926_ = lean_unsigned_to_nat(1u);
v_i_1927_ = lean_nat_sub(v___x_1925_, v___x_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1929_ = lean_array_get_borrowed(v___x_1928_, v_varDeps_1881_, v_i_1927_);
v_expectedNumArgs_1930_ = lean_array_get_size(v___x_1929_);
v_numArgs_1931_ = l_Lean_Expr_getAppNumArgs(v_e_1879_);
v___x_1932_ = lean_nat_dec_lt(v_expectedNumArgs_1930_, v_numArgs_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_nat_dec_eq(v_numArgs_1931_, v_expectedNumArgs_1930_);
lean_dec(v_numArgs_1931_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec(v_i_1927_);
v___x_1934_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1935_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1934_, v_debug_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
if (lean_obj_tag(v_a_1936_) == 1)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_e_1879_);
v_a_1937_ = lean_ctor_get(v___x_1935_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1935_, 0);
lean_dec(v_unused_1946_);
v___x_1939_ = v___x_1935_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1935_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_val_1941_; lean_object* v___x_1943_; 
v_val_1941_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_a_1936_, 1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_val_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_val_1941_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_a_1937_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
lean_object* v_a_1947_; 
lean_dec(v_a_1936_);
v_a_1947_ = lean_ctor_get(v___x_1935_, 1);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1935_, 2);
v_a_1888_ = v_a_1947_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_e_1879_);
v_a_1948_ = lean_ctor_get(v___x_1935_, 0);
v_a_1949_ = lean_ctor_get(v___x_1935_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1935_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_inc(v_a_1948_);
lean_dec(v___x_1935_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1948_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec_ref(v_e_1879_);
v___x_1957_ = lean_array_fget_borrowed(v_xs_1882_, v_i_1927_);
lean_dec(v_i_1927_);
lean_inc(v___x_1957_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v___y_1885_);
return v___x_1958_;
}
}
else
{
lean_dec(v_numArgs_1931_);
lean_dec(v_i_1927_);
v_a_1888_ = v___y_1885_;
goto v___jp_1887_;
}
}
}
}
else
{
lean_dec_ref(v___x_1918_);
v_a_1888_ = v___y_1885_;
goto v___jp_1887_;
}
}
else
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_e_1879_);
lean_ctor_set(v___x_1959_, 1, v___y_1885_);
return v___x_1959_;
}
v___jp_1887_:
{
switch(lean_obj_tag(v_e_1879_))
{
case 9:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_e_1879_);
lean_ctor_set(v___x_1889_, 1, v_a_1888_);
return v___x_1889_;
}
case 2:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_e_1879_);
lean_ctor_set(v___x_1890_, 1, v_a_1888_);
return v___x_1890_;
}
case 0:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_e_1879_);
lean_ctor_set(v___x_1891_, 1, v_a_1888_);
return v___x_1891_;
}
case 1:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v_e_1879_);
lean_ctor_set(v___x_1892_, 1, v_a_1888_);
return v___x_1892_;
}
case 4:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_e_1879_);
lean_ctor_set(v___x_1893_, 1, v_a_1888_);
return v___x_1893_;
}
case 3:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_e_1879_);
lean_ctor_set(v___x_1894_, 1, v_a_1888_);
return v___x_1894_;
}
default: 
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__2);
v___x_1896_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1880_, v_varDeps_1881_, v_xs_1882_, v_e_1879_, v___x_1886_, v___x_1895_, v_debug_1883_, v___y_1884_, v_a_1888_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_a_1898_ = lean_ctor_get(v___x_1896_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v___x_1896_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_fst_1902_; lean_object* v___x_1904_; 
v_fst_1902_ = lean_ctor_get(v_a_1897_, 0);
lean_inc(v_fst_1902_);
lean_dec(v_a_1897_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v_fst_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_fst_1902_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_a_1898_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1907_ = lean_ctor_get(v___x_1896_, 0);
v_a_1908_ = lean_ctor_get(v___x_1896_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1896_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_inc(v_a_1907_);
lean_dec(v___x_1896_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1907_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object* v_e_1960_, lean_object* v_n_1961_, lean_object* v_varDeps_1962_, lean_object* v_xs_1963_, lean_object* v_debug_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v_debug_boxed_1967_; lean_object* v_res_1968_; 
v_debug_boxed_1967_ = lean_unbox(v_debug_1964_);
v_res_1968_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(v_e_1960_, v_n_1961_, v_varDeps_1962_, v_xs_1963_, v_debug_boxed_1967_, v___y_1965_, v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_xs_1963_);
lean_dec_ref(v_varDeps_1962_);
lean_dec(v_n_1961_);
return v_res_1968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1972_ = lean_unsigned_to_nat(16u);
v___x_1973_ = lean_unsigned_to_nat(62u);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1));
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0));
v___x_1976_ = l_mkPanicMessageWithDecl(v___x_1975_, v___x_1974_, v___x_1973_, v___x_1972_, v___x_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1977_, lean_object* v_xs_1978_, lean_object* v_varDeps_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v_debug_1989_; lean_object* v_env_1990_; lean_object* v_n_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1987_ = lean_st_ref_get(v_a_1981_);
v___x_1988_ = lean_st_ref_get(v_a_1985_);
v_debug_1989_ = lean_ctor_get_uint8(v___x_1987_, sizeof(void*)*11);
lean_dec(v___x_1987_);
v_env_1990_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_env_1990_);
lean_dec(v___x_1988_);
v_n_1991_ = lean_array_get_size(v_xs_1978_);
v___x_1992_ = lean_box(v_debug_1989_);
v___f_1993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1993_, 0, v_e_1977_);
lean_closure_set(v___f_1993_, 1, v_n_1991_);
lean_closure_set(v___f_1993_, 2, v_varDeps_1979_);
lean_closure_set(v___f_1993_, 3, v_xs_1978_);
lean_closure_set(v___f_1993_, 4, v___x_1992_);
v___x_1994_ = 0;
v___x_1995_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1995_, 0, v_env_1990_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1, v___x_1994_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1 + 1, v___x_1994_);
v___x_1996_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1993_, v___x_1995_, v_a_1981_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2007_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
if (lean_obj_tag(v_a_1997_) == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref_known(v_a_1997_, 1);
lean_del_object(v___x_1999_);
v___x_2001_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2);
v___x_2002_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2001_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
return v___x_2002_;
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; 
v_a_2003_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v_a_1997_, 1);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v_a_2003_);
v___x_2005_ = v___x_1999_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_a_2008_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1996_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1996_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_2016_, lean_object* v_xs_2017_, lean_object* v_varDeps_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_2016_, v_xs_2017_, v_varDeps_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_2027_, lean_object* v_m_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_2028_, v_a_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2031_, lean_object* v_m_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(v_00_u03b2_2031_, v_m_2032_, v_a_2033_);
lean_dec_ref(v_a_2033_);
lean_dec_ref(v_m_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_2035_, lean_object* v_m_2036_, lean_object* v_query_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_m_2036_, v_query_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_2039_, lean_object* v_m_2040_, lean_object* v_query_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_2039_, v_m_2040_, v_query_2041_);
lean_dec_ref(v_query_2041_);
lean_dec_ref(v_m_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13(lean_object* v_00_u03b2_2043_, lean_object* v_m_2044_, lean_object* v_query_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___redArg(v_m_2044_, v_query_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13___boxed(lean_object* v_00_u03b2_2047_, lean_object* v_m_2048_, lean_object* v_query_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13(v_00_u03b2_2047_, v_m_2048_, v_query_2049_);
lean_dec_ref(v_query_2049_);
lean_dec_ref(v_m_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_2051_, lean_object* v_m_2052_, lean_object* v_query_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___redArg(v_m_2052_, v_query_2053_, v_x_2054_, v_x_2055_, v_x_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_m_2060_, lean_object* v_query_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12_spec__13_spec__14(v_00_u03b2_2059_, v_m_2060_, v_query_2061_, v_x_2062_, v_x_2063_, v_x_2064_, v_x_2065_);
lean_dec_ref(v_query_2061_);
lean_dec_ref(v_m_2060_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_2067_, lean_object* v_type_2068_, lean_object* v_val_2069_, lean_object* v_k_2070_, uint8_t v_nondep_2071_, uint8_t v_kind_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___f_2080_; lean_object* v___x_2081_; 
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2080_, 0, v_k_2070_);
lean_closure_set(v___f_2080_, 1, v___y_2073_);
lean_closure_set(v___f_2080_, 2, v___y_2074_);
v___x_2081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2067_, v_type_2068_, v_val_2069_, v___f_2080_, v_nondep_2071_, v_kind_2072_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2081_) == 0)
{
return v___x_2081_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_2090_, lean_object* v_type_2091_, lean_object* v_val_2092_, lean_object* v_k_2093_, lean_object* v_nondep_2094_, lean_object* v_kind_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v_nondep_boxed_2103_; uint8_t v_kind_boxed_2104_; lean_object* v_res_2105_; 
v_nondep_boxed_2103_ = lean_unbox(v_nondep_2094_);
v_kind_boxed_2104_ = lean_unbox(v_kind_2095_);
v_res_2105_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_2090_, v_type_2091_, v_val_2092_, v_k_2093_, v_nondep_boxed_2103_, v_kind_boxed_2104_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_2106_, lean_object* v_name_2107_, lean_object* v_type_2108_, lean_object* v_val_2109_, lean_object* v_k_2110_, uint8_t v_nondep_2111_, uint8_t v_kind_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_2107_, v_type_2108_, v_val_2109_, v_k_2110_, v_nondep_2111_, v_kind_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_name_2122_, lean_object* v_type_2123_, lean_object* v_val_2124_, lean_object* v_k_2125_, lean_object* v_nondep_2126_, lean_object* v_kind_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v_nondep_boxed_2135_; uint8_t v_kind_boxed_2136_; lean_object* v_res_2137_; 
v_nondep_boxed_2135_ = lean_unbox(v_nondep_2126_);
v_kind_boxed_2136_ = lean_unbox(v_kind_2127_);
v_res_2137_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_2121_, v_name_2122_, v_type_2123_, v_val_2124_, v_k_2125_, v_nondep_boxed_2135_, v_kind_boxed_2136_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_2138_, size_t v_sz_2139_, size_t v_i_2140_, lean_object* v_bs_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_lt(v_i_2140_, v_sz_2139_);
if (v___x_2142_ == 0)
{
return v_bs_2141_;
}
else
{
lean_object* v_v_2143_; lean_object* v___x_2144_; lean_object* v_bs_x27_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v_v_2143_ = lean_array_uget(v_bs_2141_, v_i_2140_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v_bs_x27_2145_ = lean_array_uset(v_bs_2141_, v_i_2140_, v___x_2144_);
v___x_2146_ = l_Lean_instInhabitedExpr;
v___x_2147_ = lean_array_get_borrowed(v___x_2146_, v_xs_2138_, v_v_2143_);
lean_dec(v_v_2143_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2140_, v___x_2148_);
lean_inc(v___x_2147_);
v___x_2150_ = lean_array_uset(v_bs_x27_2145_, v_i_2140_, v___x_2147_);
v_i_2140_ = v___x_2149_;
v_bs_2141_ = v___x_2150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_2152_, lean_object* v_sz_2153_, lean_object* v_i_2154_, lean_object* v_bs_2155_){
_start:
{
size_t v_sz_boxed_2156_; size_t v_i_boxed_2157_; lean_object* v_res_2158_; 
v_sz_boxed_2156_ = lean_unbox_usize(v_sz_2153_);
lean_dec(v_sz_2153_);
v_i_boxed_2157_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2152_, v_sz_boxed_2156_, v_i_boxed_2157_, v_bs_2155_);
lean_dec_ref(v_xs_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_2159_, lean_object* v_i_2160_, lean_object* v_varDeps_2161_, lean_object* v_args_2162_, lean_object* v_body_2163_, lean_object* v_x_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_2159_, v_i_2160_, v_varDeps_2161_, v_args_2162_, v_body_2163_, v_x_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_i_2160_);
return v_res_2172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2175_ = lean_unsigned_to_nat(30u);
v___x_2176_ = lean_unsigned_to_nat(254u);
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_2178_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2179_ = l_mkPanicMessageWithDecl(v___x_2178_, v___x_2177_, v___x_2176_, v___x_2175_, v___x_2174_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_2180_, lean_object* v_args_2181_, lean_object* v_f_2182_, lean_object* v_xs_2183_, lean_object* v_i_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = lean_array_get_size(v_args_2181_);
v___x_2193_ = lean_nat_dec_lt(v_i_2184_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v_i_2184_);
lean_dec_ref(v_args_2181_);
lean_inc_ref(v_xs_2183_);
v___x_2194_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_f_2182_, v_xs_2183_, v_varDeps_2180_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = 1;
v___x_2197_ = l_Lean_Meta_mkLetFVars(v_xs_2183_, v_a_2195_, v___x_2193_, v___x_2193_, v___x_2196_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec_ref(v_xs_2183_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2199_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v___x_2199_ = l_Lean_Meta_Sym_shareCommonInc(v_a_2198_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2199_;
}
else
{
return v___x_2197_;
}
}
else
{
lean_dec_ref(v_xs_2183_);
return v___x_2194_;
}
}
else
{
if (lean_obj_tag(v_f_2182_) == 6)
{
lean_object* v_binderName_2200_; lean_object* v_binderType_2201_; lean_object* v_body_2202_; lean_object* v_varPos_2203_; size_t v_sz_2204_; size_t v___x_2205_; lean_object* v_ys_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_binderName_2200_ = lean_ctor_get(v_f_2182_, 0);
lean_inc(v_binderName_2200_);
v_binderType_2201_ = lean_ctor_get(v_f_2182_, 1);
lean_inc_ref(v_binderType_2201_);
v_body_2202_ = lean_ctor_get(v_f_2182_, 2);
lean_inc_ref(v_body_2202_);
lean_dec_ref_known(v_f_2182_, 3);
v_varPos_2203_ = lean_array_fget(v_varDeps_2180_, v_i_2184_);
v_sz_2204_ = lean_array_size(v_varPos_2203_);
v___x_2205_ = ((size_t)0ULL);
lean_inc(v_varPos_2203_);
v_ys_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2183_, v_sz_2204_, v___x_2205_, v_varPos_2203_);
v___x_2207_ = lean_array_fget_borrowed(v_args_2181_, v_i_2184_);
v___x_2208_ = 0;
lean_inc(v___x_2207_);
v___x_2209_ = l_Lean_Expr_betaRev(v___x_2207_, v_ys_2206_, v___x_2208_, v___x_2208_);
lean_dec_ref(v_ys_2206_);
v___x_2210_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2209_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v_type_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v___f_2212_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2212_, 0, v_xs_2183_);
lean_closure_set(v___f_2212_, 1, v_i_2184_);
lean_closure_set(v___f_2212_, 2, v_varDeps_2180_);
lean_closure_set(v___f_2212_, 3, v_args_2181_);
lean_closure_set(v___f_2212_, 4, v_body_2202_);
v___x_2213_ = lean_array_get_size(v_varPos_2203_);
lean_dec(v_varPos_2203_);
v_type_2214_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_2201_, v___x_2213_);
v___x_2215_ = 0;
v___x_2216_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_2200_, v_type_2214_, v_a_2211_, v___f_2212_, v___x_2193_, v___x_2215_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2216_;
}
else
{
lean_dec(v_varPos_2203_);
lean_dec_ref(v_body_2202_);
lean_dec_ref(v_binderType_2201_);
lean_dec(v_binderName_2200_);
lean_dec(v_i_2184_);
lean_dec_ref(v_xs_2183_);
lean_dec_ref(v_args_2181_);
lean_dec_ref(v_varDeps_2180_);
return v___x_2210_;
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_i_2184_);
lean_dec_ref(v_xs_2183_);
lean_dec_ref(v_f_2182_);
lean_dec_ref(v_args_2181_);
lean_dec_ref(v_varDeps_2180_);
v___x_2217_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_2218_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2217_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_2219_, lean_object* v_i_2220_, lean_object* v_varDeps_2221_, lean_object* v_args_2222_, lean_object* v_body_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Meta_Sym_shareCommonInc(v_x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2234_ = lean_array_push(v_xs_2219_, v_a_2233_);
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_nat_add(v_i_2220_, v___x_2235_);
v___x_2237_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2221_, v_args_2222_, v_body_2223_, v___x_2234_, v___x_2236_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2237_;
}
else
{
lean_dec_ref(v_body_2223_);
lean_dec_ref(v_args_2222_);
lean_dec_ref(v_varDeps_2221_);
lean_dec_ref(v_xs_2219_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_2238_, lean_object* v_args_2239_, lean_object* v_f_2240_, lean_object* v_xs_2241_, lean_object* v_i_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2238_, v_args_2239_, v_f_2240_, v_xs_2241_, v_i_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_2251_, lean_object* v_args_2252_, lean_object* v___h_2253_, lean_object* v_f_2254_, lean_object* v_xs_2255_, lean_object* v_i_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2251_, v_args_2252_, v_f_2254_, v_xs_2255_, v_i_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_2265_, lean_object* v_args_2266_, lean_object* v___h_2267_, lean_object* v_f_2268_, lean_object* v_xs_2269_, lean_object* v_i_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2265_, v_args_2266_, v___h_2267_, v_f_2268_, v_xs_2269_, v_i_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
return v_res_2278_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2281_ = lean_unsigned_to_nat(40u);
v___x_2282_ = lean_unsigned_to_nat(251u);
v___x_2283_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2285_ = l_mkPanicMessageWithDecl(v___x_2284_, v___x_2283_, v___x_2282_, v___x_2281_, v___x_2280_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
if (lean_obj_tag(v_x_2287_) == 5)
{
lean_object* v_fn_2297_; lean_object* v_arg_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_fn_2297_ = lean_ctor_get(v_x_2287_, 0);
lean_inc_ref(v_fn_2297_);
v_arg_2298_ = lean_ctor_get(v_x_2287_, 1);
lean_inc_ref(v_arg_2298_);
lean_dec_ref_known(v_x_2287_, 2);
v___x_2299_ = lean_array_set(v_x_2288_, v_x_2289_, v_arg_2298_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_nat_sub(v_x_2289_, v___x_2300_);
lean_dec(v_x_2289_);
v_x_2287_ = v_fn_2297_;
v_x_2288_ = v___x_2299_;
v_x_2289_ = v___x_2301_;
goto _start;
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
lean_dec(v_x_2289_);
v___x_2303_ = lean_array_get_size(v_x_2288_);
v___x_2304_ = lean_array_get_size(v_varDeps_2286_);
v___x_2305_ = lean_nat_dec_eq(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_x_2288_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_varDeps_2286_);
v___x_2306_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2307_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2306_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2307_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2310_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2286_, v_x_2288_, v_x_2287_, v___x_2309_, v___x_2308_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2311_, v_x_2312_, v_x_2313_, v_x_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2323_; lean_object* v_dummy_2324_; 
v___x_2323_ = lean_box(0);
v_dummy_2324_ = l_Lean_Expr_sort___override(v___x_2323_);
return v_dummy_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2325_, lean_object* v_varDeps_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_dummy_2334_; lean_object* v_nargs_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_dummy_2334_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2335_ = l_Lean_Expr_getAppNumArgs(v_e_2325_);
lean_inc(v_nargs_2335_);
v___x_2336_ = lean_mk_array(v_nargs_2335_, v_dummy_2334_);
v___x_2337_ = lean_unsigned_to_nat(1u);
v___x_2338_ = lean_nat_sub(v_nargs_2335_, v___x_2337_);
lean_dec(v_nargs_2335_);
v___x_2339_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2326_, v_e_2325_, v___x_2336_, v___x_2338_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2340_, lean_object* v_varDeps_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2340_, v_varDeps_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_snd_2353_; lean_object* v_fst_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2387_; 
v_snd_2353_ = lean_ctor_get(v_a_2351_, 1);
v_fst_2354_ = lean_ctor_get(v_a_2351_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_a_2351_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2356_ = v_a_2351_;
v_isShared_2357_ = v_isSharedCheck_2387_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snd_2353_);
lean_inc(v_fst_2354_);
lean_dec(v_a_2351_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2387_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_fst_2358_; lean_object* v_snd_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2386_; 
v_fst_2358_ = lean_ctor_get(v_snd_2353_, 0);
v_snd_2359_ = lean_ctor_get(v_snd_2353_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_snd_2353_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2361_ = v_snd_2353_;
v_isShared_2362_ = v_isSharedCheck_2386_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_snd_2359_);
lean_inc(v_fst_2358_);
lean_dec(v_snd_2353_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2386_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = lean_nat_dec_lt(v___x_2363_, v_fst_2358_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2366_; 
if (v_isShared_2362_ == 0)
{
v___x_2366_ = v___x_2361_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_fst_2358_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_snd_2359_);
v___x_2366_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 1, v___x_2366_);
v___x_2368_ = v___x_2356_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_fst_2354_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_nat_sub(v_fst_2358_, v___x_2372_);
lean_dec(v_fst_2358_);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_array_get_borrowed(v___x_2374_, v_argUnivs_2350_, v___x_2373_);
lean_inc(v___x_2375_);
v___x_2376_ = l_Lean_mkLevelIMax_x27(v___x_2375_, v_fst_2354_);
v___x_2377_ = l_Lean_Level_normalize(v___x_2376_);
lean_dec(v___x_2376_);
lean_inc(v___x_2377_);
v___x_2378_ = lean_array_push(v_snd_2359_, v___x_2377_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 1, v___x_2378_);
lean_ctor_set(v___x_2361_, 0, v___x_2373_);
v___x_2380_ = v___x_2361_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2382_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 1, v___x_2380_);
lean_ctor_set(v___x_2356_, 0, v___x_2377_);
v___x_2382_ = v___x_2356_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
v_a_2351_ = v___x_2382_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2388_, lean_object* v_a_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2388_, v_a_2389_);
lean_dec_ref(v_argUnivs_2388_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2394_, lean_object* v_argUnivs_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
if (lean_obj_tag(v_type_2394_) == 7)
{
lean_object* v_binderType_2403_; lean_object* v_body_2404_; lean_object* v___x_2405_; 
v_binderType_2403_ = lean_ctor_get(v_type_2394_, 1);
lean_inc_ref(v_binderType_2403_);
v_body_2404_ = lean_ctor_get(v_type_2394_, 2);
lean_inc_ref(v_body_2404_);
lean_dec_ref_known(v_type_2394_, 3);
v___x_2405_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2403_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = lean_array_push(v_argUnivs_2395_, v_a_2406_);
v_type_2394_ = v_body_2404_;
v_argUnivs_2395_ = v___x_2407_;
goto _start;
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v_body_2404_);
lean_dec_ref(v_argUnivs_2395_);
v_a_2409_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2405_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2405_);
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
else
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2394_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = lean_array_get_size(v_argUnivs_2395_);
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_a_2418_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2395_, v___x_2422_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2442_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2442_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2442_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_snd_2428_; lean_object* v_snd_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2440_; 
v_snd_2428_ = lean_ctor_get(v_a_2424_, 1);
lean_inc(v_snd_2428_);
lean_dec(v_a_2424_);
v_snd_2429_ = lean_ctor_get(v_snd_2428_, 1);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_snd_2428_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v_snd_2428_, 0);
lean_dec(v_unused_2441_);
v___x_2431_ = v_snd_2428_;
v_isShared_2432_ = v_isSharedCheck_2440_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snd_2429_);
lean_dec(v_snd_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2440_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = l_Array_reverse___redArg(v_snd_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___x_2433_);
lean_ctor_set(v___x_2431_, 0, v_argUnivs_2395_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_argUnivs_2395_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2437_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2435_);
v___x_2437_ = v___x_2426_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_argUnivs_2395_);
v_a_2443_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2423_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2423_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_argUnivs_2395_);
v_a_2451_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2417_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2417_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2459_, lean_object* v_argUnivs_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2459_, v_argUnivs_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2469_, lean_object* v_inst_2470_, lean_object* v_a_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2469_, v_a_2471_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2480_, lean_object* v_inst_2481_, lean_object* v_a_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2480_, v_inst_2481_, v_a_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_argUnivs_2480_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2500_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2491_, v___x_2499_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2510_, lean_object* v_argUnivs_2511_, lean_object* v_declName_2512_, lean_object* v_fType_2513_, lean_object* v_i_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v_00_u03b1_2517_; lean_object* v_00_u03b2_2518_; lean_object* v_u_2519_; lean_object* v_v_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2516_ = lean_box(0);
v_00_u03b1_2517_ = l_Lean_Expr_bindingDomain_x21(v_fType_2513_);
v_00_u03b2_2518_ = l_Lean_Expr_bindingBody_x21(v_fType_2513_);
v_u_2519_ = lean_array_get_borrowed(v___x_2516_, v_argUnivs_2511_, v_i_2514_);
v_v_2520_ = lean_array_get_borrowed(v___x_2516_, v_fnUnivs_2510_, v_i_2514_);
v___x_2521_ = lean_box(0);
lean_inc(v_v_2520_);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_v_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
lean_inc(v_u_2519_);
v___x_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_u_2519_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_mkConst(v_declName_2512_, v___x_2523_);
v___x_2525_ = l_Lean_mkAppB(v___x_2524_, v_00_u03b1_2517_, v_00_u03b2_2518_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2527_, lean_object* v_argUnivs_2528_, lean_object* v_declName_2529_, lean_object* v_fType_2530_, lean_object* v_i_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2527_, v_argUnivs_2528_, v_declName_2529_, v_fType_2530_, v_i_2531_);
lean_dec(v_i_2531_);
lean_dec_ref(v_fType_2530_);
lean_dec_ref(v_argUnivs_2528_);
lean_dec_ref(v_fnUnivs_2527_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2534_, lean_object* v_argUnivs_2535_, lean_object* v_declName_2536_, lean_object* v_fType_2537_, lean_object* v_i_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2534_, v_argUnivs_2535_, v_declName_2536_, v_fType_2537_, v_i_2538_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2547_, lean_object* v_argUnivs_2548_, lean_object* v_declName_2549_, lean_object* v_fType_2550_, lean_object* v_i_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2547_, v_argUnivs_2548_, v_declName_2549_, v_fType_2550_, v_i_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_i_2551_);
lean_dec_ref(v_fType_2550_);
lean_dec_ref(v_argUnivs_2548_);
lean_dec_ref(v_fnUnivs_2547_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2560_, lean_object* v_a_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___y_2570_; lean_object* v___x_2573_; uint8_t v_debug_2574_; 
v___x_2573_ = lean_st_ref_get(v___y_2563_);
v_debug_2574_ = lean_ctor_get_uint8(v___x_2573_, sizeof(void*)*11);
lean_dec(v___x_2573_);
if (v_debug_2574_ == 0)
{
v___y_2570_ = v___y_2563_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2560_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; 
lean_dec_ref_known(v___x_2575_, 1);
v___x_2576_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_dec_ref_known(v___x_2576_, 1);
v___y_2570_ = v___y_2563_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_a_2561_);
lean_dec_ref(v_f_2560_);
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v_a_2561_);
lean_dec_ref(v_f_2560_);
v_a_2585_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2575_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2575_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = l_Lean_Expr_app___override(v_f_2560_, v_a_2561_);
v___x_2572_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2571_, v___y_2570_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2593_, lean_object* v_a_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2593_, v_a_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2603_, lean_object* v_a_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2603_, v_a_2604_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2616_, lean_object* v_a_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2616_, v_a_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
return v_res_2628_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_15370__overap_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15370__overap_2642_ = lean_panic_fn_borrowed(v___x_2641_, v_msg_2630_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2632_);
lean_inc(v___y_2631_);
v___x_2643_ = lean_apply_10(v___x_15370__overap_2642_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, lean_box(0));
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
return v_res_2655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2667_ = lean_unsigned_to_nat(11u);
v___x_2668_ = lean_unsigned_to_nat(346u);
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2670_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2671_ = l_mkPanicMessageWithDecl(v___x_2670_, v___x_2669_, v___x_2668_, v___x_2667_, v___x_2666_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2672_, lean_object* v_fnUnivs_2673_, lean_object* v_argUnivs_2674_, lean_object* v_simpBody_2675_, lean_object* v_e_2676_, lean_object* v_i_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
switch(lean_obj_tag(v_e_2676_))
{
case 5:
{
lean_object* v_fn_2688_; lean_object* v_arg_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_fn_2688_ = lean_ctor_get(v_e_2676_, 0);
lean_inc_ref_n(v_fn_2688_, 2);
v_arg_2689_ = lean_ctor_get(v_e_2676_, 1);
lean_inc_ref(v_arg_2689_);
lean_dec_ref_known(v_e_2676_, 2);
v___x_2690_ = lean_unsigned_to_nat(1u);
v___x_2691_ = lean_nat_sub(v_i_2677_, v___x_2690_);
v___x_2692_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2672_, v_fnUnivs_2673_, v_argUnivs_2674_, v_simpBody_2675_, v_fn_2688_, v___x_2691_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v___x_2691_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2813_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2813_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2813_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_fst_2697_; lean_object* v_snd_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2812_; 
v_fst_2697_ = lean_ctor_get(v_a_2693_, 0);
v_snd_2698_ = lean_ctor_get(v_a_2693_, 1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_a_2693_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2700_ = v_a_2693_;
v_isShared_2701_ = v_isSharedCheck_2812_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_snd_2698_);
lean_inc(v_fst_2697_);
lean_dec(v_a_2693_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2812_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_r_2703_; lean_object* v___x_2711_; 
lean_inc(v_a_2686_);
lean_inc_ref(v_a_2685_);
lean_inc(v_a_2684_);
lean_inc_ref(v_a_2683_);
lean_inc(v_a_2682_);
lean_inc_ref(v_a_2681_);
lean_inc(v_a_2680_);
lean_inc_ref(v_a_2679_);
lean_inc(v_a_2678_);
lean_inc_ref(v_arg_2689_);
v___x_2711_ = lean_sym_simp(v_arg_2689_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; uint8_t v___y_2714_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
if (lean_obj_tag(v_fst_2697_) == 0)
{
if (lean_obj_tag(v_a_2712_) == 0)
{
uint8_t v_contextDependent_2716_; 
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_fn_2688_);
v_contextDependent_2716_ = lean_ctor_get_uint8(v_fst_2697_, 1);
lean_dec_ref_known(v_fst_2697_, 0);
if (v_contextDependent_2716_ == 0)
{
uint8_t v_contextDependent_2717_; 
v_contextDependent_2717_ = lean_ctor_get_uint8(v_a_2712_, 1);
lean_dec_ref_known(v_a_2712_, 0);
v___y_2714_ = v_contextDependent_2717_;
goto v___jp_2713_;
}
else
{
lean_dec_ref_known(v_a_2712_, 0);
v___y_2714_ = v_contextDependent_2716_;
goto v___jp_2713_;
}
}
else
{
uint8_t v_contextDependent_2718_; lean_object* v_e_x27_2719_; lean_object* v_proof_2720_; uint8_t v_contextDependent_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2745_; 
v_contextDependent_2718_ = lean_ctor_get_uint8(v_fst_2697_, 1);
lean_dec_ref_known(v_fst_2697_, 0);
v_e_x27_2719_ = lean_ctor_get(v_a_2712_, 0);
v_proof_2720_ = lean_ctor_get(v_a_2712_, 1);
v_contextDependent_2721_ = lean_ctor_get_uint8(v_a_2712_, sizeof(void*)*2 + 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2712_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2723_ = v_a_2712_;
v_isShared_2724_ = v_isSharedCheck_2745_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_proof_2720_);
lean_inc(v_e_x27_2719_);
lean_dec(v_a_2712_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2745_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; 
lean_inc_ref(v_e_x27_2719_);
lean_inc_ref(v_fn_2688_);
v___x_2725_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2688_, v_e_x27_2719_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_a_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; uint8_t v___y_2733_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2728_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2673_, v_argUnivs_2674_, v___x_2727_, v_snd_2698_, v_i_2677_);
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref(v___x_2728_);
v___x_2730_ = l_Lean_mkApp4(v_a_2729_, v_arg_2689_, v_e_x27_2719_, v_fn_2688_, v_proof_2720_);
v___x_2731_ = 0;
if (v_contextDependent_2718_ == 0)
{
v___y_2733_ = v_contextDependent_2721_;
goto v___jp_2732_;
}
else
{
v___y_2733_ = v_contextDependent_2718_;
goto v___jp_2732_;
}
v___jp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 1, v___x_2730_);
lean_ctor_set(v___x_2723_, 0, v_a_2726_);
v___x_2735_ = v___x_2723_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2726_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*2, v___x_2731_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*2 + 1, v___y_2733_);
v_r_2703_ = v___x_2735_;
goto v___jp_2702_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_del_object(v___x_2723_);
lean_dec_ref(v_proof_2720_);
lean_dec_ref(v_e_x27_2719_);
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_del_object(v___x_2695_);
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_fn_2688_);
v_a_2737_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2725_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2725_);
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
else
{
if (lean_obj_tag(v_a_2712_) == 0)
{
lean_object* v_e_x27_2746_; lean_object* v_proof_2747_; uint8_t v_contextDependent_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2773_; 
v_e_x27_2746_ = lean_ctor_get(v_fst_2697_, 0);
v_proof_2747_ = lean_ctor_get(v_fst_2697_, 1);
v_contextDependent_2748_ = lean_ctor_get_uint8(v_fst_2697_, sizeof(void*)*2 + 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_fst_2697_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2750_ = v_fst_2697_;
v_isShared_2751_ = v_isSharedCheck_2773_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_proof_2747_);
lean_inc(v_e_x27_2746_);
lean_dec(v_fst_2697_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2773_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
uint8_t v_contextDependent_2752_; lean_object* v___x_2753_; 
v_contextDependent_2752_ = lean_ctor_get_uint8(v_a_2712_, 1);
lean_dec_ref_known(v_a_2712_, 0);
lean_inc_ref(v_arg_2689_);
lean_inc_ref(v_e_x27_2746_);
v___x_2753_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2746_, v_arg_2689_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v_a_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; uint8_t v___y_2761_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2756_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2673_, v_argUnivs_2674_, v___x_2755_, v_snd_2698_, v_i_2677_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = l_Lean_mkApp4(v_a_2757_, v_fn_2688_, v_e_x27_2746_, v_proof_2747_, v_arg_2689_);
v___x_2759_ = 0;
if (v_contextDependent_2748_ == 0)
{
v___y_2761_ = v_contextDependent_2752_;
goto v___jp_2760_;
}
else
{
v___y_2761_ = v_contextDependent_2748_;
goto v___jp_2760_;
}
v___jp_2760_:
{
lean_object* v___x_2763_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 1, v___x_2758_);
lean_ctor_set(v___x_2750_, 0, v_a_2754_);
v___x_2763_ = v___x_2750_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2754_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_ctor_set_uint8(v___x_2763_, sizeof(void*)*2, v___x_2759_);
lean_ctor_set_uint8(v___x_2763_, sizeof(void*)*2 + 1, v___y_2761_);
v_r_2703_ = v___x_2763_;
goto v___jp_2702_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_del_object(v___x_2750_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_del_object(v___x_2695_);
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_fn_2688_);
v_a_2765_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2753_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2753_);
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
else
{
lean_object* v_e_x27_2774_; lean_object* v_proof_2775_; uint8_t v_contextDependent_2776_; lean_object* v_e_x27_2777_; lean_object* v_proof_2778_; uint8_t v_contextDependent_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2803_; 
v_e_x27_2774_ = lean_ctor_get(v_fst_2697_, 0);
lean_inc_ref(v_e_x27_2774_);
v_proof_2775_ = lean_ctor_get(v_fst_2697_, 1);
lean_inc_ref(v_proof_2775_);
v_contextDependent_2776_ = lean_ctor_get_uint8(v_fst_2697_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2697_, 2);
v_e_x27_2777_ = lean_ctor_get(v_a_2712_, 0);
v_proof_2778_ = lean_ctor_get(v_a_2712_, 1);
v_contextDependent_2779_ = lean_ctor_get_uint8(v_a_2712_, sizeof(void*)*2 + 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_a_2712_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2781_ = v_a_2712_;
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_proof_2778_);
lean_inc(v_e_x27_2777_);
lean_dec(v_a_2712_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; 
lean_inc_ref(v_e_x27_2777_);
lean_inc_ref(v_e_x27_2774_);
v___x_2783_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2774_, v_e_x27_2777_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v_a_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; uint8_t v___y_2791_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2786_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2673_, v_argUnivs_2674_, v___x_2785_, v_snd_2698_, v_i_2677_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = l_Lean_mkApp6(v_a_2787_, v_fn_2688_, v_e_x27_2774_, v_arg_2689_, v_e_x27_2777_, v_proof_2775_, v_proof_2778_);
v___x_2789_ = 0;
if (v_contextDependent_2776_ == 0)
{
v___y_2791_ = v_contextDependent_2779_;
goto v___jp_2790_;
}
else
{
v___y_2791_ = v_contextDependent_2776_;
goto v___jp_2790_;
}
v___jp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 1, v___x_2788_);
lean_ctor_set(v___x_2781_, 0, v_a_2784_);
v___x_2793_ = v___x_2781_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2784_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___x_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*2, v___x_2789_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*2 + 1, v___y_2791_);
v_r_2703_ = v___x_2793_;
goto v___jp_2702_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_del_object(v___x_2781_);
lean_dec_ref(v_proof_2778_);
lean_dec_ref(v_e_x27_2777_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v_e_x27_2774_);
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_del_object(v___x_2695_);
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_fn_2688_);
v_a_2795_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2783_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2783_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
v___jp_2713_:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2714_);
v_r_2703_ = v___x_2715_;
goto v___jp_2702_;
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_dec(v_fst_2697_);
lean_del_object(v___x_2695_);
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_fn_2688_);
v_a_2804_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2711_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2711_);
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
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2704_ = l_Lean_Expr_bindingBody_x21(v_snd_2698_);
lean_dec(v_snd_2698_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2704_);
lean_ctor_set(v___x_2700_, 0, v_r_2703_);
v___x_2706_ = v___x_2700_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_r_2703_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2706_);
v___x_2708_ = v___x_2695_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2689_);
lean_dec_ref(v_fn_2688_);
return v___x_2692_;
}
}
case 6:
{
lean_object* v___x_2814_; 
lean_inc(v_a_2686_);
lean_inc_ref(v_a_2685_);
lean_inc(v_a_2684_);
lean_inc_ref(v_a_2683_);
lean_inc(v_a_2682_);
lean_inc_ref(v_a_2681_);
lean_inc(v_a_2680_);
lean_inc_ref(v_a_2679_);
lean_inc(v_a_2678_);
v___x_2814_ = lean_apply_11(v_simpBody_2675_, v_e_2676_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, lean_box(0));
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2823_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_a_2815_);
lean_ctor_set(v___x_2819_, 1, v_fType_2672_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref(v_fType_2672_);
v_a_2824_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2814_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2814_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
default: 
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref(v_e_2676_);
lean_dec_ref(v_simpBody_2675_);
lean_dec_ref(v_fType_2672_);
v___x_2832_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2833_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2832_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2834_, lean_object* v_fnUnivs_2835_, lean_object* v_argUnivs_2836_, lean_object* v_simpBody_2837_, lean_object* v_e_2838_, lean_object* v_i_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2834_, v_fnUnivs_2835_, v_argUnivs_2836_, v_simpBody_2837_, v_e_2838_, v_i_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec(v_i_2839_);
lean_dec_ref(v_argUnivs_2836_);
lean_dec_ref(v_fnUnivs_2835_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2851_, lean_object* v_fType_2852_, lean_object* v_fnUnivs_2853_, lean_object* v_argUnivs_2854_, lean_object* v_simpBody_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_numArgs_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_numArgs_2866_ = lean_array_get_size(v_argUnivs_2854_);
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_sub(v_numArgs_2866_, v___x_2867_);
v___x_2869_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2852_, v_fnUnivs_2853_, v_argUnivs_2854_, v_simpBody_2855_, v_e_2851_, v___x_2868_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
lean_dec(v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2878_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_fst_2874_; lean_object* v___x_2876_; 
v_fst_2874_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_fst_2874_);
lean_dec(v_a_2870_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v_fst_2874_);
v___x_2876_ = v___x_2872_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_fst_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_a_2879_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2869_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2869_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2887_, lean_object* v_fType_2888_, lean_object* v_fnUnivs_2889_, lean_object* v_argUnivs_2890_, lean_object* v_simpBody_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2887_, v_fType_2888_, v_fnUnivs_2889_, v_argUnivs_2890_, v_simpBody_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_argUnivs_2890_);
lean_dec_ref(v_fnUnivs_2889_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2907_, lean_object* v_simpBody_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2919_; 
lean_inc_ref(v_e_2907_);
v___x_2919_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2907_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v_00_u03b1_2921_; lean_object* v_u_2922_; lean_object* v_e_2923_; lean_object* v_h_2924_; lean_object* v_varDeps_2925_; lean_object* v_fType_2926_; lean_object* v___x_2927_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v_00_u03b1_2921_ = lean_ctor_get(v_a_2920_, 0);
lean_inc_ref(v_00_u03b1_2921_);
v_u_2922_ = lean_ctor_get(v_a_2920_, 1);
lean_inc(v_u_2922_);
v_e_2923_ = lean_ctor_get(v_a_2920_, 2);
lean_inc_ref(v_e_2923_);
v_h_2924_ = lean_ctor_get(v_a_2920_, 3);
lean_inc_ref(v_h_2924_);
v_varDeps_2925_ = lean_ctor_get(v_a_2920_, 4);
lean_inc_ref(v_varDeps_2925_);
v_fType_2926_ = lean_ctor_get(v_a_2920_, 5);
lean_inc_ref_n(v_fType_2926_, 2);
lean_dec(v_a_2920_);
v___x_2927_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2926_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v_argUnivs_2929_; lean_object* v_fnUnivs_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2998_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v_argUnivs_2929_ = lean_ctor_get(v_a_2928_, 0);
v_fnUnivs_2930_ = lean_ctor_get(v_a_2928_, 1);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_a_2928_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2932_ = v_a_2928_;
v_isShared_2933_ = v_isSharedCheck_2998_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_fnUnivs_2930_);
lean_inc(v_argUnivs_2929_);
lean_dec(v_a_2928_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2998_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; 
lean_inc_ref(v_e_2923_);
v___x_2934_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2923_, v_fType_2926_, v_fnUnivs_2930_, v_argUnivs_2929_, v_simpBody_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
lean_dec_ref(v_argUnivs_2929_);
lean_dec_ref(v_fnUnivs_2930_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2989_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2989_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2989_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
if (lean_obj_tag(v_a_2935_) == 0)
{
uint8_t v_contextDependent_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
lean_del_object(v___x_2932_);
lean_dec_ref(v_varDeps_2925_);
lean_dec_ref(v_h_2924_);
lean_dec_ref(v_e_2923_);
lean_dec_ref(v_e_2907_);
v_contextDependent_2939_ = lean_ctor_get_uint8(v_a_2935_, 1);
lean_dec_ref_known(v_a_2935_, 0);
v___x_2940_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2939_);
v___x_2941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_00_u03b1_2921_);
lean_ctor_set(v___x_2941_, 2, v_u_2922_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2941_);
v___x_2943_ = v___x_2937_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
else
{
lean_object* v_e_x27_2945_; lean_object* v_proof_2946_; uint8_t v_contextDependent_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2988_; 
lean_del_object(v___x_2937_);
v_e_x27_2945_ = lean_ctor_get(v_a_2935_, 0);
v_proof_2946_ = lean_ctor_get(v_a_2935_, 1);
v_contextDependent_2947_ = lean_ctor_get_uint8(v_a_2935_, sizeof(void*)*2 + 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_a_2935_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2949_ = v_a_2935_;
v_isShared_2950_ = v_isSharedCheck_2988_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_proof_2946_);
lean_inc(v_e_x27_2945_);
lean_dec(v_a_2935_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2988_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2952_ = lean_box(0);
lean_inc(v_u_2922_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set_tag(v___x_2932_, 1);
lean_ctor_set(v___x_2932_, 1, v___x_2952_);
lean_ctor_set(v___x_2932_, 0, v_u_2922_);
v___x_2954_ = v___x_2932_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_u_2922_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_inc_ref(v___x_2954_);
v___x_2955_ = l_Lean_mkConst(v___x_2951_, v___x_2954_);
lean_inc_ref_n(v_e_x27_2945_, 2);
lean_inc_ref(v_e_2907_);
lean_inc_ref(v_00_u03b1_2921_);
lean_inc_ref(v___x_2955_);
v___x_2956_ = l_Lean_mkApp6(v___x_2955_, v_00_u03b1_2921_, v_e_2907_, v_e_2923_, v_e_x27_2945_, v_h_2924_, v_proof_2946_);
v___x_2957_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2945_, v_varDeps_2925_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2978_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2978_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2978_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2972_; 
v___x_2962_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2954_);
v___x_2963_ = l_Lean_mkConst(v___x_2962_, v___x_2954_);
lean_inc_n(v_a_2958_, 2);
lean_inc_ref_n(v_e_x27_2945_, 2);
lean_inc_ref_n(v_00_u03b1_2921_, 3);
v___x_2964_ = l_Lean_mkApp3(v___x_2963_, v_00_u03b1_2921_, v_e_x27_2945_, v_a_2958_);
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2966_ = l_Lean_mkConst(v___x_2965_, v___x_2954_);
v___x_2967_ = l_Lean_mkAppB(v___x_2966_, v_00_u03b1_2921_, v_e_x27_2945_);
v___x_2968_ = l_Lean_Meta_mkExpectedPropHint(v___x_2967_, v___x_2964_);
v___x_2969_ = l_Lean_mkApp6(v___x_2955_, v_00_u03b1_2921_, v_e_2907_, v_e_x27_2945_, v_a_2958_, v___x_2956_, v___x_2968_);
v___x_2970_ = 0;
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_2969_);
lean_ctor_set(v___x_2949_, 0, v_a_2958_);
v___x_2972_ = v___x_2949_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2958_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*2 + 1, v_contextDependent_2947_);
v___x_2972_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*2, v___x_2970_);
v___x_2973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_00_u03b1_2921_);
lean_ctor_set(v___x_2973_, 2, v_u_2922_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2973_);
v___x_2975_ = v___x_2960_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec_ref(v___x_2956_);
lean_dec_ref(v___x_2955_);
lean_dec_ref(v___x_2954_);
lean_del_object(v___x_2949_);
lean_dec_ref(v_e_x27_2945_);
lean_dec(v_u_2922_);
lean_dec_ref(v_00_u03b1_2921_);
lean_dec_ref(v_e_2907_);
v_a_2979_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2957_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2957_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
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
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_del_object(v___x_2932_);
lean_dec_ref(v_varDeps_2925_);
lean_dec_ref(v_h_2924_);
lean_dec_ref(v_e_2923_);
lean_dec(v_u_2922_);
lean_dec_ref(v_00_u03b1_2921_);
lean_dec_ref(v_e_2907_);
v_a_2990_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2934_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2934_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_fType_2926_);
lean_dec_ref(v_varDeps_2925_);
lean_dec_ref(v_h_2924_);
lean_dec_ref(v_e_2923_);
lean_dec(v_u_2922_);
lean_dec_ref(v_00_u03b1_2921_);
lean_dec_ref(v_simpBody_2908_);
lean_dec_ref(v_e_2907_);
v_a_2999_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2927_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2927_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_simpBody_2908_);
lean_dec_ref(v_e_2907_);
v_a_3007_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2919_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2919_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_3015_, lean_object* v_simpBody_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_3015_, v_simpBody_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_3028_, lean_object* v_simpBody_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_3028_, v_simpBody_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_result_3045_; lean_object* v___x_3047_; 
v_result_3045_ = lean_ctor_get(v_a_3041_, 0);
lean_inc_ref(v_result_3045_);
lean_dec(v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_result_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_result_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_a_3050_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3040_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_3058_, lean_object* v_simpBody_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_3058_, v_simpBody_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_3071_, lean_object* v_simpBody_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; 
lean_inc_ref(v_e_u2081_3071_);
v___x_3083_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_3071_, v_simpBody_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_result_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v_result_3085_ = lean_ctor_get(v_a_3084_, 0);
lean_inc_ref(v_result_3085_);
if (lean_obj_tag(v_result_3085_) == 0)
{
lean_object* v_00_u03b1_3086_; lean_object* v_u_3087_; uint8_t v_contextDependent_3088_; lean_object* v___x_3089_; 
v_00_u03b1_3086_ = lean_ctor_get(v_a_3084_, 1);
lean_inc_ref(v_00_u03b1_3086_);
v_u_3087_ = lean_ctor_get(v_a_3084_, 2);
lean_inc(v_u_3087_);
lean_dec(v_a_3084_);
v_contextDependent_3088_ = lean_ctor_get_uint8(v_result_3085_, 1);
lean_dec_ref_known(v_result_3085_, 0);
lean_inc_ref(v_e_u2081_3071_);
v___x_3089_ = l_Lean_Meta_zetaUnused(v_e_u2081_3071_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3110_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3110_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3110_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
size_t v___x_3094_; size_t v___x_3095_; uint8_t v___x_3096_; 
v___x_3094_ = lean_ptr_addr(v_e_u2081_3071_);
lean_dec_ref(v_e_u2081_3071_);
v___x_3095_ = lean_ptr_addr(v_a_3090_);
v___x_3096_ = lean_usize_dec_eq(v___x_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3097_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3099_, 0, v_u_3087_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_mkConst(v___x_3097_, v___x_3099_);
lean_inc(v_a_3090_);
v___x_3101_ = l_Lean_mkAppB(v___x_3100_, v_00_u03b1_3086_, v_a_3090_);
v___x_3102_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3102_, 0, v_a_3090_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*2, v___x_3096_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*2 + 1, v_contextDependent_3088_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3102_);
v___x_3104_ = v___x_3092_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_dec(v_a_3090_);
lean_dec(v_u_3087_);
lean_dec_ref(v_00_u03b1_3086_);
v___x_3106_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_3088_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3106_);
v___x_3108_ = v___x_3092_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_u_3087_);
lean_dec_ref(v_00_u03b1_3086_);
lean_dec_ref(v_e_u2081_3071_);
v_a_3111_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3089_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3089_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_00_u03b1_3119_; lean_object* v_u_3120_; lean_object* v_e_x27_3121_; lean_object* v_proof_3122_; uint8_t v_contextDependent_3123_; lean_object* v___x_3124_; 
v_00_u03b1_3119_ = lean_ctor_get(v_a_3084_, 1);
lean_inc_ref(v_00_u03b1_3119_);
v_u_3120_ = lean_ctor_get(v_a_3084_, 2);
lean_inc(v_u_3120_);
lean_dec(v_a_3084_);
v_e_x27_3121_ = lean_ctor_get(v_result_3085_, 0);
v_proof_3122_ = lean_ctor_get(v_result_3085_, 1);
v_contextDependent_3123_ = lean_ctor_get_uint8(v_result_3085_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_3121_);
v___x_3124_ = l_Lean_Meta_zetaUnused(v_e_x27_3121_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3155_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3155_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3155_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
size_t v___x_3129_; size_t v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = lean_ptr_addr(v_e_x27_3121_);
v___x_3130_ = lean_ptr_addr(v_a_3125_);
v___x_3131_ = lean_usize_dec_eq(v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3149_; 
lean_inc_ref(v_proof_3122_);
lean_inc_ref(v_e_x27_3121_);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_result_3085_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; lean_object* v_unused_3151_; 
v_unused_3150_ = lean_ctor_get(v_result_3085_, 1);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_result_3085_, 0);
lean_dec(v_unused_3151_);
v___x_3133_ = v_result_3085_;
v_isShared_3134_ = v_isSharedCheck_3149_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v_result_3085_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3149_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3135_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v_u_3120_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
lean_inc_ref(v___x_3137_);
v___x_3138_ = l_Lean_mkConst(v___x_3135_, v___x_3137_);
v___x_3139_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3140_ = l_Lean_mkConst(v___x_3139_, v___x_3137_);
lean_inc_n(v_a_3125_, 2);
lean_inc_ref(v_00_u03b1_3119_);
v___x_3141_ = l_Lean_mkAppB(v___x_3140_, v_00_u03b1_3119_, v_a_3125_);
v___x_3142_ = l_Lean_mkApp6(v___x_3138_, v_00_u03b1_3119_, v_e_u2081_3071_, v_e_x27_3121_, v_a_3125_, v_proof_3122_, v___x_3141_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 1, v___x_3142_);
lean_ctor_set(v___x_3133_, 0, v_a_3125_);
v___x_3144_ = v___x_3133_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3125_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v___x_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*2 + 1, v_contextDependent_3123_);
v___x_3144_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3146_; 
lean_ctor_set_uint8(v___x_3144_, sizeof(void*)*2, v___x_3131_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3144_);
v___x_3146_ = v___x_3127_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3153_; 
lean_dec(v_a_3125_);
lean_dec(v_u_3120_);
lean_dec_ref(v_00_u03b1_3119_);
lean_dec_ref(v_e_u2081_3071_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v_result_3085_);
v___x_3153_ = v___x_3127_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_result_3085_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_u_3120_);
lean_dec_ref(v_00_u03b1_3119_);
lean_dec_ref_known(v_result_3085_, 2);
lean_dec_ref(v_e_u2081_3071_);
v_a_3156_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3124_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3124_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v_e_u2081_3071_);
v_a_3164_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3083_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3083_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_3172_, lean_object* v_simpBody_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_3172_, v_simpBody_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_3185_, lean_object* v_e_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
uint8_t v___x_3197_; 
v___x_3197_ = l_Lean_Expr_letNondep_x21(v_e_3186_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_dec_ref(v_e_3186_);
lean_dec_ref(v_simpBody_3185_);
v___x_3198_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3198_, 0, v___x_3197_);
lean_ctor_set_uint8(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_3186_, v_simpBody_3185_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_3201_, lean_object* v_e_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_3201_, v_e_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_3227_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_3226_, v_e_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
return v_res_3239_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
