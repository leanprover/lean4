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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_171_, v___y_173_, v___y_174_, v___y_176_, v___y_176_);
lean_dec(v___y_176_);
lean_dec(v___y_173_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_171_, v___y_173_, v___y_174_, v___y_176_, v___y_175_);
lean_dec(v___y_175_);
lean_dec(v___y_173_);
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
v___y_173_ = v___x_183_;
v___y_174_ = v___y_182_;
v___y_175_ = v___x_186_;
v___y_176_ = v___x_186_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___x_183_;
v___y_174_ = v___y_182_;
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
v_debug_273_ = lean_ctor_get_uint8(v___x_272_, sizeof(void*)*11);
lean_dec(v___x_272_);
if (v_debug_273_ == 0)
{
v___y_269_ = v___y_262_;
goto v___jp_268_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; 
lean_dec_ref_known(v___x_274_, 1);
v___x_275_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref_known(v___x_275_, 1);
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
lean_dec_ref_known(v___x_326_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_385_, lean_object* v_subst_386_, size_t v_sz_387_, size_t v_i_388_, lean_object* v_bs_389_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = lean_usize_dec_lt(v_i_388_, v_sz_387_);
if (v___x_390_ == 0)
{
return v_bs_389_;
}
else
{
lean_object* v___x_391_; lean_object* v_v_392_; lean_object* v___x_393_; lean_object* v_bs_x27_394_; lean_object* v___x_395_; lean_object* v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_391_ = l_Lean_instInhabitedExpr;
v_v_392_ = lean_array_uget(v_bs_389_, v_i_388_);
v___x_393_ = lean_unsigned_to_nat(0u);
v_bs_x27_394_ = lean_array_uset(v_bs_389_, v_i_388_, v___x_393_);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_385_, v_v_392_);
lean_dec(v_v_392_);
v___x_396_ = lean_array_get_borrowed(v___x_391_, v_subst_386_, v___x_395_);
lean_dec(v___x_395_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_388_, v___x_397_);
lean_inc(v___x_396_);
v___x_399_ = lean_array_uset(v_bs_x27_394_, v_i_388_, v___x_396_);
v_i_388_ = v___x_398_;
v_bs_389_ = v___x_399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_401_, lean_object* v_subst_402_, lean_object* v_sz_403_, lean_object* v_i_404_, lean_object* v_bs_405_){
_start:
{
size_t v_sz_boxed_406_; size_t v_i_boxed_407_; lean_object* v_res_408_; 
v_sz_boxed_406_ = lean_unbox_usize(v_sz_403_);
lean_dec(v_sz_403_);
v_i_boxed_407_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_401_, v_subst_402_, v_sz_boxed_406_, v_i_boxed_407_, v_bs_405_);
lean_dec_ref(v_subst_402_);
lean_dec(v_fvarIdToPos_401_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_409_, size_t v_i_410_, lean_object* v_bs_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_lt(v_i_410_, v_sz_409_);
if (v___x_412_ == 0)
{
return v_bs_411_;
}
else
{
lean_object* v_v_413_; lean_object* v___x_414_; lean_object* v_bs_x27_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v_v_413_ = lean_array_uget(v_bs_411_, v_i_410_);
v___x_414_ = lean_unsigned_to_nat(0u);
v_bs_x27_415_ = lean_array_uset(v_bs_411_, v_i_410_, v___x_414_);
v___x_416_ = l_Lean_mkFVar(v_v_413_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_410_, v___x_417_);
v___x_419_ = lean_array_uset(v_bs_x27_415_, v_i_410_, v___x_416_);
v_i_410_ = v___x_418_;
v_bs_411_ = v___x_419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_421_, lean_object* v_i_422_, lean_object* v_bs_423_){
_start:
{
size_t v_sz_boxed_424_; size_t v_i_boxed_425_; lean_object* v_res_426_; 
v_sz_boxed_424_ = lean_unbox_usize(v_sz_421_);
lean_dec(v_sz_421_);
v_i_boxed_425_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_424_, v_i_boxed_425_, v_bs_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
v___x_436_ = lean_apply_8(v_k_427_, v_b_430_, v___y_428_, v___y_429_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, lean_box(0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_437_, v___y_438_, v___y_439_, v_b_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_447_, uint8_t v_bi_448_, lean_object* v_type_449_, lean_object* v_k_450_, uint8_t v_kind_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_459_, 0, v_k_450_);
lean_closure_set(v___f_459_, 1, v___y_452_);
lean_closure_set(v___f_459_, 2, v___y_453_);
v___x_460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_447_, v_bi_448_, v_type_449_, v___f_459_, v_kind_451_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
return v___x_460_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_469_, lean_object* v_bi_470_, lean_object* v_type_471_, lean_object* v_k_472_, lean_object* v_kind_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
uint8_t v_bi_boxed_481_; uint8_t v_kind_boxed_482_; lean_object* v_res_483_; 
v_bi_boxed_481_ = lean_unbox(v_bi_470_);
v_kind_boxed_482_ = lean_unbox(v_kind_473_);
v_res_483_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_469_, v_bi_boxed_481_, v_type_471_, v_k_472_, v_kind_boxed_482_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_484_, lean_object* v_type_485_, lean_object* v_k_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = 0;
v___x_495_ = 0;
v___x_496_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_484_, v___x_494_, v_type_485_, v_k_486_, v___x_495_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_497_, lean_object* v_type_498_, lean_object* v_k_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_497_, v_type_498_, v_k_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_508_, lean_object* v_k_509_, lean_object* v_fallback_510_){
_start:
{
if (lean_obj_tag(v_t_508_) == 0)
{
lean_object* v_k_511_; lean_object* v_v_512_; lean_object* v_l_513_; lean_object* v_r_514_; uint8_t v___x_515_; 
v_k_511_ = lean_ctor_get(v_t_508_, 1);
v_v_512_ = lean_ctor_get(v_t_508_, 2);
v_l_513_ = lean_ctor_get(v_t_508_, 3);
v_r_514_ = lean_ctor_get(v_t_508_, 4);
v___x_515_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_509_, v_k_511_);
switch(v___x_515_)
{
case 0:
{
v_t_508_ = v_l_513_;
goto _start;
}
case 1:
{
lean_inc(v_v_512_);
return v_v_512_;
}
default: 
{
v_t_508_ = v_r_514_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_510_);
return v_fallback_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_518_, lean_object* v_k_519_, lean_object* v_fallback_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_518_, v_k_519_, v_fallback_520_);
lean_dec(v_fallback_520_);
lean_dec(v_k_519_);
lean_dec(v_t_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_522_, size_t v_sz_523_, size_t v_i_524_, lean_object* v_bs_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = lean_usize_dec_lt(v_i_524_, v_sz_523_);
if (v___x_526_ == 0)
{
return v_bs_525_;
}
else
{
lean_object* v_v_527_; lean_object* v___x_528_; lean_object* v_bs_x27_529_; lean_object* v___x_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v_v_527_ = lean_array_uget(v_bs_525_, v_i_524_);
v___x_528_ = lean_unsigned_to_nat(0u);
v_bs_x27_529_ = lean_array_uset(v_bs_525_, v_i_524_, v___x_528_);
v___x_530_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_522_, v_v_527_, v___x_528_);
lean_dec(v_v_527_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_524_, v___x_531_);
v___x_533_ = lean_array_uset(v_bs_x27_529_, v_i_524_, v___x_530_);
v_i_524_ = v___x_532_;
v_bs_525_ = v___x_533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_535_, v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
lean_dec(v_fvarIdToPos_535_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_551_ = _args[0];
lean_object* v_subst_552_ = _args[1];
lean_object* v_sz_553_ = _args[2];
lean_object* v___x_554_ = _args[3];
lean_object* v_fvarIds_555_ = _args[4];
lean_object* v_x_556_ = _args[5];
lean_object* v_xs_557_ = _args[6];
lean_object* v_xs_x27_558_ = _args[7];
lean_object* v_args_559_ = _args[8];
lean_object* v_a_560_ = _args[9];
lean_object* v_types_561_ = _args[10];
lean_object* v_a_562_ = _args[11];
lean_object* v_varDeps_563_ = _args[12];
lean_object* v_varPos_564_ = _args[13];
lean_object* v_haveExpr_565_ = _args[14];
lean_object* v_body_566_ = _args[15];
lean_object* v_x_x27_567_ = _args[16];
lean_object* v___y_568_ = _args[17];
lean_object* v___y_569_ = _args[18];
lean_object* v___y_570_ = _args[19];
lean_object* v___y_571_ = _args[20];
lean_object* v___y_572_ = _args[21];
lean_object* v___y_573_ = _args[22];
lean_object* v___y_574_ = _args[23];
_start:
{
size_t v_sz_boxed_575_; size_t v___x_6520__boxed_576_; lean_object* v_res_577_; 
v_sz_boxed_575_ = lean_unbox_usize(v_sz_553_);
lean_dec(v_sz_553_);
v___x_6520__boxed_576_ = lean_unbox_usize(v___x_554_);
lean_dec(v___x_554_);
v_res_577_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_551_, v_subst_552_, v_sz_boxed_575_, v___x_6520__boxed_576_, v_fvarIds_555_, v_x_556_, v_xs_557_, v_xs_x27_558_, v_args_559_, v_a_560_, v_types_561_, v_a_562_, v_varDeps_563_, v_varPos_564_, v_haveExpr_565_, v_body_566_, v_x_x27_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_v_578_, lean_object* v_fvarIdToPos_579_, uint8_t v_nondep_580_, lean_object* v_t_581_, lean_object* v_subst_582_, lean_object* v_xs_583_, lean_object* v_xs_x27_584_, lean_object* v_args_585_, lean_object* v_types_586_, lean_object* v_varDeps_587_, lean_object* v_haveExpr_588_, lean_object* v_body_589_, lean_object* v_declName_590_, lean_object* v_x_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_fvarIds_599_; size_t v_sz_600_; size_t v___x_601_; lean_object* v_varPos_602_; lean_object* v_ys_603_; uint8_t v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
lean_inc_ref(v_v_578_);
v_fvarIds_599_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_578_, v_fvarIdToPos_579_);
v_sz_600_ = lean_array_size(v_fvarIds_599_);
v___x_601_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_599_, 2);
v_varPos_602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_579_, v_sz_600_, v___x_601_, v_fvarIds_599_);
v_ys_603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_600_, v___x_601_, v_fvarIds_599_);
v___x_604_ = 0;
v___x_605_ = 1;
v___x_606_ = l_Lean_Meta_mkLambdaFVars(v_ys_603_, v_v_578_, v___x_604_, v_nondep_580_, v___x_604_, v_nondep_580_, v___x_605_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = l_Lean_Meta_mkForallFVars(v_ys_603_, v_t_581_, v___x_604_, v_nondep_580_, v_nondep_580_, v___x_605_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec_ref(v_ys_603_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = l_Lean_Meta_Sym_shareCommonInc(v_a_609_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_n(v_a_611_, 2);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = lean_box_usize(v_sz_600_);
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_614_, 0, v_fvarIdToPos_579_);
lean_closure_set(v___f_614_, 1, v_subst_582_);
lean_closure_set(v___f_614_, 2, v___x_612_);
lean_closure_set(v___f_614_, 3, v___x_613_);
lean_closure_set(v___f_614_, 4, v_fvarIds_599_);
lean_closure_set(v___f_614_, 5, v_x_591_);
lean_closure_set(v___f_614_, 6, v_xs_583_);
lean_closure_set(v___f_614_, 7, v_xs_x27_584_);
lean_closure_set(v___f_614_, 8, v_args_585_);
lean_closure_set(v___f_614_, 9, v_a_607_);
lean_closure_set(v___f_614_, 10, v_types_586_);
lean_closure_set(v___f_614_, 11, v_a_611_);
lean_closure_set(v___f_614_, 12, v_varDeps_587_);
lean_closure_set(v___f_614_, 13, v_varPos_602_);
lean_closure_set(v___f_614_, 14, v_haveExpr_588_);
lean_closure_set(v___f_614_, 15, v_body_589_);
v___x_615_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_590_, v_a_611_, v___f_614_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_607_);
lean_dec_ref(v_varPos_602_);
lean_dec_ref(v_fvarIds_599_);
lean_dec_ref(v_x_591_);
lean_dec(v_declName_590_);
lean_dec_ref(v_body_589_);
lean_dec_ref(v_haveExpr_588_);
lean_dec_ref(v_varDeps_587_);
lean_dec_ref(v_types_586_);
lean_dec_ref(v_args_585_);
lean_dec_ref(v_xs_x27_584_);
lean_dec_ref(v_xs_583_);
lean_dec_ref(v_subst_582_);
lean_dec(v_fvarIdToPos_579_);
v_a_616_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_610_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_a_607_);
lean_dec_ref(v_varPos_602_);
lean_dec_ref(v_fvarIds_599_);
lean_dec_ref(v_x_591_);
lean_dec(v_declName_590_);
lean_dec_ref(v_body_589_);
lean_dec_ref(v_haveExpr_588_);
lean_dec_ref(v_varDeps_587_);
lean_dec_ref(v_types_586_);
lean_dec_ref(v_args_585_);
lean_dec_ref(v_xs_x27_584_);
lean_dec_ref(v_xs_583_);
lean_dec_ref(v_subst_582_);
lean_dec(v_fvarIdToPos_579_);
v_a_624_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_608_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_608_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_ys_603_);
lean_dec_ref(v_varPos_602_);
lean_dec_ref(v_fvarIds_599_);
lean_dec_ref(v_x_591_);
lean_dec(v_declName_590_);
lean_dec_ref(v_body_589_);
lean_dec_ref(v_haveExpr_588_);
lean_dec_ref(v_varDeps_587_);
lean_dec_ref(v_types_586_);
lean_dec_ref(v_args_585_);
lean_dec_ref(v_xs_x27_584_);
lean_dec_ref(v_xs_583_);
lean_dec_ref(v_subst_582_);
lean_dec_ref(v_t_581_);
lean_dec(v_fvarIdToPos_579_);
v_a_632_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_606_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_606_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_v_640_ = _args[0];
lean_object* v_fvarIdToPos_641_ = _args[1];
lean_object* v_nondep_642_ = _args[2];
lean_object* v_t_643_ = _args[3];
lean_object* v_subst_644_ = _args[4];
lean_object* v_xs_645_ = _args[5];
lean_object* v_xs_x27_646_ = _args[6];
lean_object* v_args_647_ = _args[7];
lean_object* v_types_648_ = _args[8];
lean_object* v_varDeps_649_ = _args[9];
lean_object* v_haveExpr_650_ = _args[10];
lean_object* v_body_651_ = _args[11];
lean_object* v_declName_652_ = _args[12];
lean_object* v_x_653_ = _args[13];
lean_object* v___y_654_ = _args[14];
lean_object* v___y_655_ = _args[15];
lean_object* v___y_656_ = _args[16];
lean_object* v___y_657_ = _args[17];
lean_object* v___y_658_ = _args[18];
lean_object* v___y_659_ = _args[19];
lean_object* v___y_660_ = _args[20];
_start:
{
uint8_t v_nondep_6547__boxed_661_; lean_object* v_res_662_; 
v_nondep_6547__boxed_661_ = lean_unbox(v_nondep_642_);
v_res_662_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_v_640_, v_fvarIdToPos_641_, v_nondep_6547__boxed_661_, v_t_643_, v_subst_644_, v_xs_645_, v_xs_x27_646_, v_args_647_, v_types_648_, v_varDeps_649_, v_haveExpr_650_, v_body_651_, v_declName_652_, v_x_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_663_, lean_object* v_e_664_, lean_object* v_xs_665_, lean_object* v_xs_x27_666_, lean_object* v_args_667_, lean_object* v_subst_668_, lean_object* v_types_669_, lean_object* v_varDeps_670_, lean_object* v_fvarIdToPos_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; 
if (lean_obj_tag(v_e_664_) == 8)
{
uint8_t v_nondep_766_; 
v_nondep_766_ = lean_ctor_get_uint8(v_e_664_, sizeof(void*)*4 + 8);
if (v_nondep_766_ == 1)
{
lean_object* v_declName_767_; lean_object* v_type_768_; lean_object* v_value_769_; lean_object* v_body_770_; lean_object* v_t_771_; lean_object* v_v_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v_declName_767_ = lean_ctor_get(v_e_664_, 0);
lean_inc_n(v_declName_767_, 2);
v_type_768_ = lean_ctor_get(v_e_664_, 1);
lean_inc_ref(v_type_768_);
v_value_769_ = lean_ctor_get(v_e_664_, 2);
lean_inc_ref(v_value_769_);
v_body_770_ = lean_ctor_get(v_e_664_, 3);
lean_inc_ref(v_body_770_);
lean_dec_ref_known(v_e_664_, 4);
v_t_771_ = lean_expr_instantiate_rev(v_type_768_, v_xs_665_);
lean_dec_ref(v_type_768_);
v_v_772_ = lean_expr_instantiate_rev(v_value_769_, v_xs_665_);
lean_dec_ref(v_value_769_);
v___x_773_ = lean_box(v_nondep_766_);
lean_inc_ref(v_t_771_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 21, 13);
lean_closure_set(v___f_774_, 0, v_v_772_);
lean_closure_set(v___f_774_, 1, v_fvarIdToPos_671_);
lean_closure_set(v___f_774_, 2, v___x_773_);
lean_closure_set(v___f_774_, 3, v_t_771_);
lean_closure_set(v___f_774_, 4, v_subst_668_);
lean_closure_set(v___f_774_, 5, v_xs_665_);
lean_closure_set(v___f_774_, 6, v_xs_x27_666_);
lean_closure_set(v___f_774_, 7, v_args_667_);
lean_closure_set(v___f_774_, 8, v_types_669_);
lean_closure_set(v___f_774_, 9, v_varDeps_670_);
lean_closure_set(v___f_774_, 10, v_haveExpr_663_);
lean_closure_set(v___f_774_, 11, v_body_770_);
lean_closure_set(v___f_774_, 12, v_declName_767_);
v___x_775_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_767_, v_t_771_, v___f_774_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
return v___x_775_;
}
else
{
lean_dec(v_fvarIdToPos_671_);
lean_dec_ref(v_xs_665_);
v___y_680_ = v_a_672_;
v___y_681_ = v_a_673_;
v___y_682_ = v_a_674_;
v___y_683_ = v_a_675_;
v___y_684_ = v_a_676_;
v___y_685_ = v_a_677_;
goto v___jp_679_;
}
}
else
{
lean_dec(v_fvarIdToPos_671_);
lean_dec_ref(v_xs_665_);
v___y_680_ = v_a_672_;
v___y_681_ = v_a_673_;
v___y_682_ = v_a_674_;
v___y_683_ = v_a_675_;
v___y_684_ = v_a_676_;
v___y_685_ = v_a_677_;
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_subst_668_);
v___x_688_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_664_, v___x_686_, v___x_687_, v_subst_668_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_n(v_a_689_, 2);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = l_Lean_Meta_Sym_inferType(v_a_689_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_n(v_a_691_, 2);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_691_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
lean_inc(v_a_691_);
v___x_694_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_669_, v_a_691_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec_ref(v_types_669_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_666_, v_a_689_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = l_Lean_mkAppN(v_a_697_, v_args_667_);
lean_dec_ref(v_args_667_);
v___x_699_ = l_Lean_Meta_Sym_shareCommonInc(v___x_698_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_717_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_717_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_705_ = lean_box(0);
lean_inc(v_a_693_);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_693_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
lean_inc_ref(v___x_706_);
v___x_707_ = l_Lean_mkConst(v___x_704_, v___x_706_);
lean_inc(v_a_700_);
lean_inc_ref(v_haveExpr_663_);
lean_inc_n(v_a_691_, 2);
v___x_708_ = l_Lean_mkApp3(v___x_707_, v_a_691_, v_haveExpr_663_, v_a_700_);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_710_ = l_Lean_mkConst(v___x_709_, v___x_706_);
v___x_711_ = l_Lean_mkAppB(v___x_710_, v_a_691_, v_haveExpr_663_);
v___x_712_ = l_Lean_Meta_mkExpectedPropHint(v___x_711_, v___x_708_);
v___x_713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_713_, 0, v_a_691_);
lean_ctor_set(v___x_713_, 1, v_a_693_);
lean_ctor_set(v___x_713_, 2, v_a_700_);
lean_ctor_set(v___x_713_, 3, v___x_712_);
lean_ctor_set(v___x_713_, 4, v_varDeps_670_);
lean_ctor_set(v___x_713_, 5, v_a_695_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_a_695_);
lean_dec(v_a_693_);
lean_dec(v_a_691_);
lean_dec_ref(v_varDeps_670_);
lean_dec_ref(v_haveExpr_663_);
v_a_718_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_699_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_699_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
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
lean_dec(v_a_695_);
lean_dec(v_a_693_);
lean_dec(v_a_691_);
lean_dec_ref(v_varDeps_670_);
lean_dec_ref(v_args_667_);
lean_dec_ref(v_haveExpr_663_);
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
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_693_);
lean_dec(v_a_691_);
lean_dec(v_a_689_);
lean_dec_ref(v_varDeps_670_);
lean_dec_ref(v_args_667_);
lean_dec_ref(v_xs_x27_666_);
lean_dec_ref(v_haveExpr_663_);
v_a_734_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_694_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_694_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_691_);
lean_dec(v_a_689_);
lean_dec_ref(v_varDeps_670_);
lean_dec_ref(v_types_669_);
lean_dec_ref(v_args_667_);
lean_dec_ref(v_xs_x27_666_);
lean_dec_ref(v_haveExpr_663_);
v_a_742_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_692_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_692_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_a_689_);
lean_dec_ref(v_varDeps_670_);
lean_dec_ref(v_types_669_);
lean_dec_ref(v_args_667_);
lean_dec_ref(v_xs_x27_666_);
lean_dec_ref(v_haveExpr_663_);
v_a_750_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_690_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_690_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_varDeps_670_);
lean_dec_ref(v_types_669_);
lean_dec_ref(v_args_667_);
lean_dec_ref(v_xs_x27_666_);
lean_dec_ref(v_haveExpr_663_);
v_a_758_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_688_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_688_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_776_, lean_object* v_subst_777_, size_t v_sz_778_, size_t v___x_779_, lean_object* v_fvarIds_780_, lean_object* v_x_781_, lean_object* v_xs_782_, lean_object* v_xs_x27_783_, lean_object* v_args_784_, lean_object* v_a_785_, lean_object* v_types_786_, lean_object* v_a_787_, lean_object* v_varDeps_788_, lean_object* v_varPos_789_, lean_object* v_haveExpr_790_, lean_object* v_body_791_, lean_object* v_x_x27_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_776_, v_subst_777_, v_sz_778_, v___x_779_, v_fvarIds_780_);
lean_inc_ref(v_x_x27_792_);
v___x_801_ = l_Lean_mkAppN(v_x_x27_792_, v___x_800_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_Meta_Sym_shareCommonInc(v___x_801_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = l_Lean_Expr_fvarId_x21(v_x_781_);
v___x_805_ = lean_array_get_size(v_xs_782_);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_804_, v___x_805_, v_fvarIdToPos_776_);
v___x_807_ = lean_array_push(v_xs_782_, v_x_781_);
v___x_808_ = lean_array_push(v_xs_x27_783_, v_x_x27_792_);
v___x_809_ = lean_array_push(v_args_784_, v_a_785_);
v___x_810_ = lean_array_push(v_subst_777_, v_a_803_);
v___x_811_ = lean_array_push(v_types_786_, v_a_787_);
v___x_812_ = lean_array_push(v_varDeps_788_, v_varPos_789_);
v___x_813_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_790_, v_body_791_, v___x_807_, v___x_808_, v___x_809_, v___x_810_, v___x_811_, v___x_812_, v___x_806_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_813_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_x_x27_792_);
lean_dec_ref(v_body_791_);
lean_dec_ref(v_haveExpr_790_);
lean_dec_ref(v_varPos_789_);
lean_dec_ref(v_varDeps_788_);
lean_dec_ref(v_a_787_);
lean_dec_ref(v_types_786_);
lean_dec_ref(v_a_785_);
lean_dec_ref(v_args_784_);
lean_dec_ref(v_xs_x27_783_);
lean_dec_ref(v_xs_782_);
lean_dec_ref(v_x_781_);
lean_dec_ref(v_subst_777_);
lean_dec(v_fvarIdToPos_776_);
v_a_814_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_802_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_802_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_822_, lean_object* v_e_823_, lean_object* v_xs_824_, lean_object* v_xs_x27_825_, lean_object* v_args_826_, lean_object* v_subst_827_, lean_object* v_types_828_, lean_object* v_varDeps_829_, lean_object* v_fvarIdToPos_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_822_, v_e_823_, v_xs_824_, v_xs_x27_825_, v_args_826_, v_subst_827_, v_types_828_, v_varDeps_829_, v_fvarIdToPos_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_839_, lean_object* v_t_840_, lean_object* v_k_841_, lean_object* v_fallback_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_840_, v_k_841_, v_fallback_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_844_, lean_object* v_t_845_, lean_object* v_k_846_, lean_object* v_fallback_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_844_, v_t_845_, v_k_846_, v_fallback_847_);
lean_dec(v_fallback_847_);
lean_dec(v_k_846_);
lean_dec(v_t_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_849_, lean_object* v_name_850_, uint8_t v_bi_851_, lean_object* v_type_852_, lean_object* v_k_853_, uint8_t v_kind_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_850_, v_bi_851_, v_type_852_, v_k_853_, v_kind_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_863_, lean_object* v_name_864_, lean_object* v_bi_865_, lean_object* v_type_866_, lean_object* v_k_867_, lean_object* v_kind_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v_bi_boxed_876_; uint8_t v_kind_boxed_877_; lean_object* v_res_878_; 
v_bi_boxed_876_ = lean_unbox(v_bi_865_);
v_kind_boxed_877_ = lean_unbox(v_kind_868_);
v_res_878_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_863_, v_name_864_, v_bi_boxed_876_, v_type_866_, v_k_867_, v_kind_boxed_877_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_879_, lean_object* v_name_880_, lean_object* v_type_881_, lean_object* v_k_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_880_, v_type_881_, v_k_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_891_, lean_object* v_name_892_, lean_object* v_type_893_, lean_object* v_k_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_891_, v_name_892_, v_type_893_, v_k_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_914_ = lean_box(1);
lean_inc_ref(v_haveExpr_905_);
v___x_915_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_905_, v_haveExpr_905_, v___x_913_, v___x_913_, v___x_913_, v___x_913_, v___x_913_, v___x_913_, v___x_914_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_925_, lean_object* v_n_926_){
_start:
{
lean_object* v_zero_927_; uint8_t v_isZero_928_; 
v_zero_927_ = lean_unsigned_to_nat(0u);
v_isZero_928_ = lean_nat_dec_eq(v_n_926_, v_zero_927_);
if (v_isZero_928_ == 1)
{
lean_dec(v_n_926_);
return v_type_925_;
}
else
{
lean_object* v_one_929_; lean_object* v_n_930_; lean_object* v___x_931_; 
v_one_929_ = lean_unsigned_to_nat(1u);
v_n_930_ = lean_nat_sub(v_n_926_, v_one_929_);
lean_dec(v_n_926_);
v___x_931_ = l_Lean_Expr_bindingBody_x21(v_type_925_);
lean_dec_ref(v_type_925_);
v_type_925_ = v___x_931_;
v_n_926_ = v_n_930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(lean_object* v_idx_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = l_Lean_Expr_bvar___override(v_idx_933_);
v___x_936_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_935_, v___y_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_idx_937_, uint8_t v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v_idx_937_, v___y_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___boxed(lean_object* v_idx_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v___y_24906__boxed_946_; lean_object* v_res_947_; 
v___y_24906__boxed_946_ = lean_unbox(v___y_943_);
v_res_947_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(v_idx_942_, v___y_24906__boxed_946_, v___y_944_, v___y_945_);
lean_dec_ref(v___y_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_msg_950_, uint8_t v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___f_959_; lean_object* v___x_1543__overap_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___f_954_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0));
v___f_955_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__1));
v___x_956_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_954_, v___f_955_);
v___f_957_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_957_, 0, v___x_956_);
v___f_958_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_958_, 0, v___f_957_);
v___f_959_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_959_, 0, v___f_958_);
v___x_1543__overap_960_ = lean_panic_fn_borrowed(v___f_959_, v_msg_950_);
lean_dec_ref(v___f_959_);
v___x_961_ = lean_box(v___y_951_);
lean_inc_ref(v___y_952_);
v___x_962_ = lean_apply_3(v___x_1543__overap_960_, v___x_961_, v___y_952_, v___y_953_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___y_24921__boxed_967_; lean_object* v_res_968_; 
v___y_24921__boxed_967_ = lean_unbox(v___y_964_);
v_res_968_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_msg_963_, v___y_24921__boxed_967_, v___y_965_, v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_968_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0(void){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_1996__overap_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0);
v___x_1996__overap_979_ = lean_panic_fn_borrowed(v___x_978_, v_msg_970_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
v___x_980_ = lean_apply_7(v___x_1996__overap_979_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, lean_box(0));
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object* v_x_990_, lean_object* v_t_991_, lean_object* v_v_992_, lean_object* v_b_993_, uint8_t v_nondep_994_, lean_object* v___y_995_, uint8_t v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___y_1000_; lean_object* v___y_1001_; 
if (v___y_996_ == 0)
{
v___y_1000_ = v___y_995_;
v___y_1001_ = v___y_998_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_991_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 1);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 2);
v___x_1025_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_992_, v___y_996_, v___y_997_, v_a_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 2);
v___x_1027_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_993_, v___y_996_, v___y_997_, v_a_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 1);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 2);
v___y_1000_ = v___y_995_;
v___y_1001_ = v_a_1028_;
goto v___jp_999_;
}
else
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v___y_995_);
lean_dec_ref(v_b_993_);
lean_dec_ref(v_v_992_);
lean_dec_ref(v_t_991_);
lean_dec(v_x_990_);
v_a_1029_ = lean_ctor_get(v___x_1027_, 0);
v_a_1030_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1027_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_inc(v_a_1029_);
lean_dec(v___x_1027_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1029_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v___y_995_);
lean_dec_ref(v_b_993_);
lean_dec_ref(v_v_992_);
lean_dec_ref(v_t_991_);
lean_dec(v_x_990_);
v_a_1038_ = lean_ctor_get(v___x_1025_, 0);
v_a_1039_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1025_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_inc(v_a_1038_);
lean_dec(v___x_1025_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___y_995_);
lean_dec_ref(v_b_993_);
lean_dec_ref(v_v_992_);
lean_dec_ref(v_t_991_);
lean_dec(v_x_990_);
v_a_1047_ = lean_ctor_get(v___x_1023_, 0);
v_a_1048_ = lean_ctor_get(v___x_1023_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1023_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_inc(v_a_1047_);
lean_dec(v___x_1023_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1047_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
v___jp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = l_Lean_Expr_letE___override(v_x_990_, v_t_991_, v_v_992_, v_b_993_, v_nondep_994_);
v___x_1003_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1002_, v___y_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1013_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_a_1005_ = lean_ctor_get(v___x_1003_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1007_ = v___x_1003_;
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_a_1004_);
lean_ctor_set(v___x_1009_, 1, v___y_1000_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1009_);
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_a_1005_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___y_1000_);
v_a_1014_ = lean_ctor_get(v___x_1003_, 0);
v_a_1015_ = lean_ctor_get(v___x_1003_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1003_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_inc(v_a_1014_);
lean_dec(v___x_1003_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1014_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object* v_x_1056_, lean_object* v_t_1057_, lean_object* v_v_1058_, lean_object* v_b_1059_, lean_object* v_nondep_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v_nondep_boxed_1065_; uint8_t v___y_24977__boxed_1066_; lean_object* v_res_1067_; 
v_nondep_boxed_1065_ = lean_unbox(v_nondep_1060_);
v___y_24977__boxed_1066_ = lean_unbox(v___y_1062_);
v_res_1067_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_x_1056_, v_t_1057_, v_v_1058_, v_b_1059_, v_nondep_boxed_1065_, v___y_1061_, v___y_24977__boxed_1066_, v___y_1063_, v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object* v_x_1068_, uint8_t v_bi_1069_, lean_object* v_t_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, uint8_t v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___y_1077_; lean_object* v___y_1078_; 
if (v___y_1073_ == 0)
{
v___y_1077_ = v___y_1072_;
v___y_1078_ = v___y_1075_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1070_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 2);
v___x_1102_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1071_, v___y_1073_, v___y_1074_, v_a_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 1);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 2);
v___y_1077_ = v___y_1072_;
v___y_1078_ = v_a_1103_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___y_1072_);
lean_dec_ref(v_b_1071_);
lean_dec_ref(v_t_1070_);
lean_dec(v_x_1068_);
v_a_1104_ = lean_ctor_get(v___x_1102_, 0);
v_a_1105_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1102_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_inc(v_a_1104_);
lean_dec(v___x_1102_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1104_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v___y_1072_);
lean_dec_ref(v_b_1071_);
lean_dec_ref(v_t_1070_);
lean_dec(v_x_1068_);
v_a_1113_ = lean_ctor_get(v___x_1100_, 0);
v_a_1114_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1100_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_inc(v_a_1113_);
lean_dec(v___x_1100_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
v___jp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = l_Lean_Expr_lam___override(v_x_1068_, v_t_1070_, v_b_1071_, v_bi_1069_);
v___x_1080_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1079_, v___y_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_a_1081_);
lean_ctor_set(v___x_1086_, 1, v___y_1077_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_1082_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v___y_1077_);
v_a_1091_ = lean_ctor_get(v___x_1080_, 0);
v_a_1092_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1080_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_inc(v_a_1091_);
lean_dec(v___x_1080_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1091_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object* v_x_1122_, lean_object* v_bi_1123_, lean_object* v_t_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_bi_boxed_1130_; uint8_t v___y_25106__boxed_1131_; lean_object* v_res_1132_; 
v_bi_boxed_1130_ = lean_unbox(v_bi_1123_);
v___y_25106__boxed_1131_ = lean_unbox(v___y_1127_);
v_res_1132_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_x_1122_, v_bi_boxed_1130_, v_t_1124_, v_b_1125_, v___y_1126_, v___y_25106__boxed_1131_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object* v_x_1133_, uint8_t v_bi_1134_, lean_object* v_t_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_, uint8_t v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___y_1142_; lean_object* v___y_1143_; 
if (v___y_1138_ == 0)
{
v___y_1142_ = v___y_1137_;
v___y_1143_ = v___y_1140_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1135_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 1);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 2);
v___x_1167_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1136_, v___y_1138_, v___y_1139_, v_a_1166_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 2);
v___y_1142_ = v___y_1137_;
v___y_1143_ = v_a_1168_;
goto v___jp_1141_;
}
else
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v___y_1137_);
lean_dec_ref(v_b_1136_);
lean_dec_ref(v_t_1135_);
lean_dec(v_x_1133_);
v_a_1169_ = lean_ctor_get(v___x_1167_, 0);
v_a_1170_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1167_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_inc(v_a_1169_);
lean_dec(v___x_1167_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1169_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v___y_1137_);
lean_dec_ref(v_b_1136_);
lean_dec_ref(v_t_1135_);
lean_dec(v_x_1133_);
v_a_1178_ = lean_ctor_get(v___x_1165_, 0);
v_a_1179_ = lean_ctor_get(v___x_1165_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1165_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_inc(v_a_1178_);
lean_dec(v___x_1165_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1178_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
v___jp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = l_Lean_Expr_forallE___override(v_x_1133_, v_t_1135_, v_b_1136_, v_bi_1134_);
v___x_1145_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1144_, v___y_1143_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_a_1147_ = lean_ctor_get(v___x_1145_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v___x_1145_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_a_1146_);
lean_ctor_set(v___x_1151_, 1, v___y_1142_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_a_1147_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v___y_1142_);
v_a_1156_ = lean_ctor_get(v___x_1145_, 0);
v_a_1157_ = lean_ctor_get(v___x_1145_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1145_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_inc(v_a_1156_);
lean_dec(v___x_1145_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1156_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object* v_x_1187_, lean_object* v_bi_1188_, lean_object* v_t_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_bi_boxed_1195_; uint8_t v___y_25212__boxed_1196_; lean_object* v_res_1197_; 
v_bi_boxed_1195_ = lean_unbox(v_bi_1188_);
v___y_25212__boxed_1196_ = lean_unbox(v___y_1192_);
v_res_1197_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_x_1187_, v_bi_boxed_1195_, v_t_1189_, v_b_1190_, v___y_1191_, v___y_25212__boxed_1196_, v___y_1193_, v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object* v_f_1198_, lean_object* v_a_1199_, lean_object* v___y_1200_, uint8_t v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___y_1205_; lean_object* v___y_1206_; 
if (v___y_1201_ == 0)
{
v___y_1205_ = v___y_1200_;
v___y_1206_ = v___y_1203_;
goto v___jp_1204_;
}
else
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1198_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 2);
v___x_1230_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1199_, v___y_1201_, v___y_1202_, v_a_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 2);
v___y_1205_ = v___y_1200_;
v___y_1206_ = v_a_1231_;
goto v___jp_1204_;
}
else
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_a_1199_);
lean_dec_ref(v_f_1198_);
v_a_1232_ = lean_ctor_get(v___x_1230_, 0);
v_a_1233_ = lean_ctor_get(v___x_1230_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1230_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_inc(v_a_1232_);
lean_dec(v___x_1230_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_a_1199_);
lean_dec_ref(v_f_1198_);
v_a_1241_ = lean_ctor_get(v___x_1228_, 0);
v_a_1242_ = lean_ctor_get(v___x_1228_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1228_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_inc(v_a_1241_);
lean_dec(v___x_1228_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
v___jp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = l_Lean_Expr_app___override(v_f_1198_, v_a_1199_);
v___x_1208_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1207_, v___y_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_a_1210_ = lean_ctor_get(v___x_1208_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v___x_1208_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_a_1209_);
lean_ctor_set(v___x_1214_, 1, v___y_1205_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_a_1210_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v___y_1205_);
v_a_1219_ = lean_ctor_get(v___x_1208_, 0);
v_a_1220_ = lean_ctor_get(v___x_1208_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1208_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_inc(v_a_1219_);
lean_dec(v___x_1208_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object* v_f_1250_, lean_object* v_a_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v___y_25318__boxed_1256_; lean_object* v_res_1257_; 
v___y_25318__boxed_1256_ = lean_unbox(v___y_1253_);
v_res_1257_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_f_1250_, v_a_1251_, v___y_1252_, v___y_25318__boxed_1256_, v___y_1254_, v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object* v_d_1258_, lean_object* v_e_1259_, lean_object* v___y_1260_, uint8_t v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___y_1265_; lean_object* v___y_1266_; 
if (v___y_1261_ == 0)
{
v___y_1265_ = v___y_1260_;
v___y_1266_ = v___y_1263_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1259_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 1);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 2);
v___y_1265_ = v___y_1260_;
v___y_1266_ = v_a_1289_;
goto v___jp_1264_;
}
else
{
lean_object* v_a_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_e_1259_);
lean_dec(v_d_1258_);
v_a_1290_ = lean_ctor_get(v___x_1288_, 0);
v_a_1291_ = lean_ctor_get(v___x_1288_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1288_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_inc(v_a_1290_);
lean_dec(v___x_1288_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
v___jp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_Lean_Expr_mdata___override(v_d_1258_, v_e_1259_);
v___x_1268_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1267_, v___y_1266_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_a_1270_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1269_);
lean_ctor_set(v___x_1274_, 1, v___y_1265_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_a_1270_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v___y_1265_);
v_a_1279_ = lean_ctor_get(v___x_1268_, 0);
v_a_1280_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1268_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_inc(v_a_1279_);
lean_dec(v___x_1268_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object* v_d_1299_, lean_object* v_e_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v___y_25424__boxed_1305_; lean_object* v_res_1306_; 
v___y_25424__boxed_1305_ = lean_unbox(v___y_1302_);
v_res_1306_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_d_1299_, v_e_1300_, v___y_1301_, v___y_25424__boxed_1305_, v___y_1303_, v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(lean_object* v_msg_1314_, lean_object* v___y_1315_, uint8_t v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_24513__overap_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___f_1319_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0));
v___f_1320_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1));
v___f_1321_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2));
v___x_1322_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3));
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v___f_1319_);
v___x_1324_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4));
v___x_1325_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5));
v___x_1326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1323_);
lean_ctor_set(v___x_1326_, 1, v___x_1324_);
lean_ctor_set(v___x_1326_, 2, v___f_1320_);
lean_ctor_set(v___x_1326_, 3, v___f_1321_);
lean_ctor_set(v___x_1326_, 4, v___x_1325_);
v___x_1327_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6));
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_ReaderT_instMonad___redArg(v___x_1328_);
v___x_1330_ = l_ReaderT_instMonad___redArg(v___x_1329_);
lean_inc_ref_n(v___x_1330_, 6);
v___f_1331_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1331_, 0, v___x_1330_);
v___f_1332_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1332_, 0, v___x_1330_);
v___f_1333_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1333_, 0, v___x_1330_);
v___f_1334_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1334_, 0, v___x_1330_);
v___x_1335_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1335_, 0, lean_box(0));
lean_closure_set(v___x_1335_, 1, lean_box(0));
lean_closure_set(v___x_1335_, 2, v___x_1330_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___f_1331_);
v___x_1337_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1337_, 0, lean_box(0));
lean_closure_set(v___x_1337_, 1, lean_box(0));
lean_closure_set(v___x_1337_, 2, v___x_1330_);
v___x_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
lean_ctor_set(v___x_1338_, 2, v___f_1332_);
lean_ctor_set(v___x_1338_, 3, v___f_1333_);
lean_ctor_set(v___x_1338_, 4, v___f_1334_);
v___x_1339_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1339_, 0, lean_box(0));
lean_closure_set(v___x_1339_, 1, lean_box(0));
lean_closure_set(v___x_1339_, 2, v___x_1330_);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_Lean_instInhabitedExpr;
v___x_1342_ = l_instInhabitedOfMonad___redArg(v___x_1340_, v___x_1341_);
v___x_24513__overap_1343_ = lean_panic_fn_borrowed(v___x_1342_, v_msg_1314_);
lean_dec(v___x_1342_);
v___x_1344_ = lean_box(v___y_1316_);
lean_inc_ref(v___y_1317_);
v___x_1345_ = lean_apply_4(v___x_24513__overap_1343_, v___y_1315_, v___x_1344_, v___y_1317_, v___y_1318_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___boxed(lean_object* v_msg_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v___y_25521__boxed_1351_; lean_object* v_res_1352_; 
v___y_25521__boxed_1351_ = lean_unbox(v___y_1348_);
v_res_1352_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v_msg_1346_, v___y_1347_, v___y_25521__boxed_1351_, v___y_1349_, v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object* v_structName_1353_, lean_object* v_idx_1354_, lean_object* v_struct_1355_, lean_object* v___y_1356_, uint8_t v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___y_1361_; lean_object* v___y_1362_; 
if (v___y_1357_ == 0)
{
v___y_1361_ = v___y_1356_;
v___y_1362_ = v___y_1359_;
goto v___jp_1360_;
}
else
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1355_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 2);
v___y_1361_ = v___y_1356_;
v___y_1362_ = v_a_1385_;
goto v___jp_1360_;
}
else
{
lean_object* v_a_1386_; lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v___y_1356_);
lean_dec_ref(v_struct_1355_);
lean_dec(v_idx_1354_);
lean_dec(v_structName_1353_);
v_a_1386_ = lean_ctor_get(v___x_1384_, 0);
v_a_1387_ = lean_ctor_get(v___x_1384_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1384_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_inc(v_a_1386_);
lean_dec(v___x_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1386_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = l_Lean_Expr_proj___override(v_structName_1353_, v_idx_1354_, v_struct_1355_);
v___x_1364_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1363_, v___y_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1374_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_a_1366_ = lean_ctor_get(v___x_1364_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1368_ = v___x_1364_;
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1365_);
lean_ctor_set(v___x_1370_, 1, v___y_1361_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1366_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v___y_1361_);
v_a_1375_ = lean_ctor_get(v___x_1364_, 0);
v_a_1376_ = lean_ctor_get(v___x_1364_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1364_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_inc(v_a_1375_);
lean_dec(v___x_1364_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1375_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object* v_structName_1395_, lean_object* v_idx_1396_, lean_object* v_struct_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v___y_25592__boxed_1402_; lean_object* v_res_1403_; 
v___y_25592__boxed_1402_ = lean_unbox(v___y_1399_);
v_res_1403_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_structName_1395_, v_idx_1396_, v_struct_1397_, v___y_1398_, v___y_25592__boxed_1402_, v___y_1400_, v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_1404_, lean_object* v_x_1405_){
_start:
{
if (lean_obj_tag(v_x_1405_) == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_box(0);
return v___x_1406_;
}
else
{
lean_object* v_key_1407_; lean_object* v_value_1408_; lean_object* v_tail_1409_; uint8_t v___y_1411_; lean_object* v_fst_1414_; lean_object* v_snd_1415_; lean_object* v_fst_1416_; lean_object* v_snd_1417_; size_t v___x_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v_key_1407_ = lean_ctor_get(v_x_1405_, 0);
v_value_1408_ = lean_ctor_get(v_x_1405_, 1);
v_tail_1409_ = lean_ctor_get(v_x_1405_, 2);
v_fst_1414_ = lean_ctor_get(v_key_1407_, 0);
v_snd_1415_ = lean_ctor_get(v_key_1407_, 1);
v_fst_1416_ = lean_ctor_get(v_a_1404_, 0);
v_snd_1417_ = lean_ctor_get(v_a_1404_, 1);
v___x_1418_ = lean_ptr_addr(v_fst_1414_);
v___x_1419_ = lean_ptr_addr(v_fst_1416_);
v___x_1420_ = lean_usize_dec_eq(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
v___y_1411_ = v___x_1420_;
goto v___jp_1410_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_eq(v_snd_1415_, v_snd_1417_);
v___y_1411_ = v___x_1421_;
goto v___jp_1410_;
}
v___jp_1410_:
{
if (v___y_1411_ == 0)
{
v_x_1405_ = v_tail_1409_;
goto _start;
}
else
{
lean_object* v___x_1413_; 
lean_inc(v_value_1408_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_value_1408_);
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1422_, v_x_1423_);
lean_dec(v_x_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(lean_object* v_m_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_buckets_1427_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___x_1430_; size_t v___x_1431_; size_t v___x_1432_; size_t v___x_1433_; uint64_t v___x_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; uint64_t v___x_1438_; uint64_t v_fold_1439_; uint64_t v___x_1440_; uint64_t v___x_1441_; uint64_t v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_buckets_1427_ = lean_ctor_get(v_m_1425_, 1);
v_fst_1428_ = lean_ctor_get(v_a_1426_, 0);
v_snd_1429_ = lean_ctor_get(v_a_1426_, 1);
v___x_1430_ = lean_array_get_size(v_buckets_1427_);
v___x_1431_ = lean_ptr_addr(v_fst_1428_);
v___x_1432_ = ((size_t)3ULL);
v___x_1433_ = lean_usize_shift_right(v___x_1431_, v___x_1432_);
v___x_1434_ = lean_usize_to_uint64(v___x_1433_);
v___x_1435_ = lean_uint64_of_nat(v_snd_1429_);
v___x_1436_ = lean_uint64_mix_hash(v___x_1434_, v___x_1435_);
v___x_1437_ = 32ULL;
v___x_1438_ = lean_uint64_shift_right(v___x_1436_, v___x_1437_);
v_fold_1439_ = lean_uint64_xor(v___x_1436_, v___x_1438_);
v___x_1440_ = 16ULL;
v___x_1441_ = lean_uint64_shift_right(v_fold_1439_, v___x_1440_);
v___x_1442_ = lean_uint64_xor(v_fold_1439_, v___x_1441_);
v___x_1443_ = lean_uint64_to_usize(v___x_1442_);
v___x_1444_ = lean_usize_of_nat(v___x_1430_);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_sub(v___x_1444_, v___x_1445_);
v___x_1447_ = lean_usize_land(v___x_1443_, v___x_1446_);
v___x_1448_ = lean_array_uget_borrowed(v_buckets_1427_, v___x_1447_);
v___x_1449_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1426_, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1450_, v_a_1451_);
lean_dec_ref(v_a_1451_);
lean_dec_ref(v_m_1450_);
return v_res_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Array_instInhabited(lean_box(0));
return v___x_1453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3));
v___x_1458_ = lean_unsigned_to_nat(12u);
v___x_1459_ = lean_unsigned_to_nat(234u);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2));
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_1462_ = l_mkPanicMessageWithDecl(v___x_1461_, v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_);
return v___x_1462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1467_ = lean_unsigned_to_nat(67u);
v___x_1468_ = lean_unsigned_to_nat(35u);
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___x_1471_ = l_mkPanicMessageWithDecl(v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_n_1472_, lean_object* v_varDeps_1473_, lean_object* v_xs_1474_, lean_object* v_e_1475_, lean_object* v_offset_1476_, lean_object* v_a_1477_, uint8_t v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
switch(lean_obj_tag(v_e_1475_))
{
case 5:
{
lean_object* v_fn_1481_; lean_object* v_arg_1482_; lean_object* v___x_1483_; 
v_fn_1481_ = lean_ctor_get(v_e_1475_, 0);
v_arg_1482_ = lean_ctor_get(v_e_1475_, 1);
lean_inc(v_offset_1476_);
lean_inc_ref(v_fn_1481_);
v___x_1483_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_fn_1481_, v_offset_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v_a_1485_; lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1488_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
v_a_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1483_, 2);
v_fst_1486_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_fst_1486_);
v_snd_1487_ = lean_ctor_get(v_a_1484_, 1);
lean_inc(v_snd_1487_);
lean_dec(v_a_1484_);
lean_inc_ref(v_arg_1482_);
v___x_1488_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_arg_1482_, v_offset_1476_, v_snd_1487_, v_a_1478_, v_a_1479_, v_a_1485_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1515_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_a_1490_ = lean_ctor_get(v___x_1488_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1492_ = v___x_1488_;
v_isShared_1493_ = v_isSharedCheck_1515_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1515_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_fst_1494_; lean_object* v_snd_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1514_; 
v_fst_1494_ = lean_ctor_get(v_a_1489_, 0);
v_snd_1495_ = lean_ctor_get(v_a_1489_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_a_1489_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1497_ = v_a_1489_;
v_isShared_1498_ = v_isSharedCheck_1514_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snd_1495_);
lean_inc(v_fst_1494_);
lean_dec(v_a_1489_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1514_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint8_t v___y_1500_; size_t v___x_1508_; size_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_ptr_addr(v_fn_1481_);
v___x_1509_ = lean_ptr_addr(v_fst_1486_);
v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
v___y_1500_ = v___x_1510_;
goto v___jp_1499_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = lean_ptr_addr(v_arg_1482_);
v___x_1512_ = lean_ptr_addr(v_fst_1494_);
v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
v___y_1500_ = v___x_1513_;
goto v___jp_1499_;
}
v___jp_1499_:
{
if (v___y_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_del_object(v___x_1497_);
lean_del_object(v___x_1492_);
lean_dec_ref_known(v_e_1475_, 2);
v___x_1501_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1486_, v_fst_1494_, v_snd_1495_, v_a_1478_, v_a_1479_, v_a_1490_);
return v___x_1501_;
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_fst_1494_);
lean_dec(v_fst_1486_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_e_1475_);
v___x_1503_ = v___x_1497_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_e_1475_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1495_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1503_);
v___x_1505_ = v___x_1492_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_a_1490_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1486_);
lean_dec_ref_known(v_e_1475_, 2);
return v___x_1488_;
}
}
else
{
lean_dec_ref_known(v_e_1475_, 2);
lean_dec(v_offset_1476_);
return v___x_1483_;
}
}
case 6:
{
lean_object* v_binderName_1516_; lean_object* v_binderType_1517_; lean_object* v_body_1518_; uint8_t v_binderInfo_1519_; lean_object* v___x_1520_; 
v_binderName_1516_ = lean_ctor_get(v_e_1475_, 0);
v_binderType_1517_ = lean_ctor_get(v_e_1475_, 1);
v_body_1518_ = lean_ctor_get(v_e_1475_, 2);
v_binderInfo_1519_ = lean_ctor_get_uint8(v_e_1475_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1476_);
lean_inc_ref(v_binderType_1517_);
v___x_1520_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_binderType_1517_, v_offset_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_a_1522_; lean_object* v_fst_1523_; lean_object* v_snd_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
v_a_1522_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1520_, 2);
v_fst_1523_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_fst_1523_);
v_snd_1524_ = lean_ctor_get(v_a_1521_, 1);
lean_inc(v_snd_1524_);
lean_dec(v_a_1521_);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_offset_1476_, v___x_1525_);
lean_dec(v_offset_1476_);
lean_inc_ref(v_body_1518_);
v___x_1527_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_body_1518_, v___x_1526_, v_snd_1524_, v_a_1478_, v_a_1479_, v_a_1522_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1554_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_a_1529_ = lean_ctor_get(v___x_1527_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1531_ = v___x_1527_;
v_isShared_1532_ = v_isSharedCheck_1554_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1554_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_fst_1533_; lean_object* v_snd_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1553_; 
v_fst_1533_ = lean_ctor_get(v_a_1528_, 0);
v_snd_1534_ = lean_ctor_get(v_a_1528_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1536_ = v_a_1528_;
v_isShared_1537_ = v_isSharedCheck_1553_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_snd_1534_);
lean_inc(v_fst_1533_);
lean_dec(v_a_1528_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1553_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v___y_1539_; size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = lean_ptr_addr(v_binderType_1517_);
v___x_1548_ = lean_ptr_addr(v_fst_1523_);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
v___y_1539_ = v___x_1549_;
goto v___jp_1538_;
}
else
{
size_t v___x_1550_; size_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = lean_ptr_addr(v_body_1518_);
v___x_1551_ = lean_ptr_addr(v_fst_1533_);
v___x_1552_ = lean_usize_dec_eq(v___x_1550_, v___x_1551_);
v___y_1539_ = v___x_1552_;
goto v___jp_1538_;
}
v___jp_1538_:
{
if (v___y_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_inc(v_binderName_1516_);
lean_del_object(v___x_1536_);
lean_del_object(v___x_1531_);
lean_dec_ref_known(v_e_1475_, 3);
v___x_1540_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1516_, v_binderInfo_1519_, v_fst_1523_, v_fst_1533_, v_snd_1534_, v_a_1478_, v_a_1479_, v_a_1529_);
return v___x_1540_;
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_fst_1533_);
lean_dec(v_fst_1523_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_e_1475_);
v___x_1542_ = v___x_1536_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_e_1475_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_snd_1534_);
v___x_1542_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1542_);
v___x_1544_ = v___x_1531_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_a_1529_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1523_);
lean_dec_ref_known(v_e_1475_, 3);
return v___x_1527_;
}
}
else
{
lean_dec_ref_known(v_e_1475_, 3);
lean_dec(v_offset_1476_);
return v___x_1520_;
}
}
case 7:
{
lean_object* v_binderName_1555_; lean_object* v_binderType_1556_; lean_object* v_body_1557_; uint8_t v_binderInfo_1558_; lean_object* v___x_1559_; 
v_binderName_1555_ = lean_ctor_get(v_e_1475_, 0);
v_binderType_1556_ = lean_ctor_get(v_e_1475_, 1);
v_body_1557_ = lean_ctor_get(v_e_1475_, 2);
v_binderInfo_1558_ = lean_ctor_get_uint8(v_e_1475_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1476_);
lean_inc_ref(v_binderType_1556_);
v___x_1559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_binderType_1556_, v_offset_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v_a_1561_; lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
v_a_1561_ = lean_ctor_get(v___x_1559_, 1);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1559_, 2);
v_fst_1562_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_fst_1562_);
v_snd_1563_ = lean_ctor_get(v_a_1560_, 1);
lean_inc(v_snd_1563_);
lean_dec(v_a_1560_);
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_add(v_offset_1476_, v___x_1564_);
lean_dec(v_offset_1476_);
lean_inc_ref(v_body_1557_);
v___x_1566_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_body_1557_, v___x_1565_, v_snd_1563_, v_a_1478_, v_a_1479_, v_a_1561_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1593_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_a_1568_ = lean_ctor_get(v___x_1566_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1570_ = v___x_1566_;
v_isShared_1571_ = v_isSharedCheck_1593_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1593_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_fst_1572_; lean_object* v_snd_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1592_; 
v_fst_1572_ = lean_ctor_get(v_a_1567_, 0);
v_snd_1573_ = lean_ctor_get(v_a_1567_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1567_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1575_ = v_a_1567_;
v_isShared_1576_ = v_isSharedCheck_1592_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_snd_1573_);
lean_inc(v_fst_1572_);
lean_dec(v_a_1567_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1592_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint8_t v___y_1578_; size_t v___x_1586_; size_t v___x_1587_; uint8_t v___x_1588_; 
v___x_1586_ = lean_ptr_addr(v_binderType_1556_);
v___x_1587_ = lean_ptr_addr(v_fst_1562_);
v___x_1588_ = lean_usize_dec_eq(v___x_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
v___y_1578_ = v___x_1588_;
goto v___jp_1577_;
}
else
{
size_t v___x_1589_; size_t v___x_1590_; uint8_t v___x_1591_; 
v___x_1589_ = lean_ptr_addr(v_body_1557_);
v___x_1590_ = lean_ptr_addr(v_fst_1572_);
v___x_1591_ = lean_usize_dec_eq(v___x_1589_, v___x_1590_);
v___y_1578_ = v___x_1591_;
goto v___jp_1577_;
}
v___jp_1577_:
{
if (v___y_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_inc(v_binderName_1555_);
lean_del_object(v___x_1575_);
lean_del_object(v___x_1570_);
lean_dec_ref_known(v_e_1475_, 3);
v___x_1579_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1555_, v_binderInfo_1558_, v_fst_1562_, v_fst_1572_, v_snd_1573_, v_a_1478_, v_a_1479_, v_a_1568_);
return v___x_1579_;
}
else
{
lean_object* v___x_1581_; 
lean_dec(v_fst_1572_);
lean_dec(v_fst_1562_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_e_1475_);
v___x_1581_ = v___x_1575_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_e_1475_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_snd_1573_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1581_);
v___x_1583_ = v___x_1570_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_a_1568_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1562_);
lean_dec_ref_known(v_e_1475_, 3);
return v___x_1566_;
}
}
else
{
lean_dec_ref_known(v_e_1475_, 3);
lean_dec(v_offset_1476_);
return v___x_1559_;
}
}
case 8:
{
lean_object* v_declName_1594_; lean_object* v_type_1595_; lean_object* v_value_1596_; lean_object* v_body_1597_; uint8_t v_nondep_1598_; lean_object* v___x_1599_; 
v_declName_1594_ = lean_ctor_get(v_e_1475_, 0);
v_type_1595_ = lean_ctor_get(v_e_1475_, 1);
v_value_1596_ = lean_ctor_get(v_e_1475_, 2);
v_body_1597_ = lean_ctor_get(v_e_1475_, 3);
v_nondep_1598_ = lean_ctor_get_uint8(v_e_1475_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1476_);
lean_inc_ref(v_type_1595_);
v___x_1599_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_type_1595_, v_offset_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v___x_1604_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
v_a_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1599_, 2);
v_fst_1602_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_fst_1602_);
v_snd_1603_ = lean_ctor_get(v_a_1600_, 1);
lean_inc(v_snd_1603_);
lean_dec(v_a_1600_);
lean_inc(v_offset_1476_);
lean_inc_ref(v_value_1596_);
v___x_1604_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_value_1596_, v_offset_1476_, v_snd_1603_, v_a_1478_, v_a_1479_, v_a_1601_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_a_1606_; lean_object* v_fst_1607_; lean_object* v_snd_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
v_a_1606_ = lean_ctor_get(v___x_1604_, 1);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1604_, 2);
v_fst_1607_ = lean_ctor_get(v_a_1605_, 0);
lean_inc(v_fst_1607_);
v_snd_1608_ = lean_ctor_get(v_a_1605_, 1);
lean_inc(v_snd_1608_);
lean_dec(v_a_1605_);
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_add(v_offset_1476_, v___x_1609_);
lean_dec(v_offset_1476_);
lean_inc_ref(v_body_1597_);
v___x_1611_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_body_1597_, v___x_1610_, v_snd_1608_, v_a_1478_, v_a_1479_, v_a_1606_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1642_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_a_1613_ = lean_ctor_get(v___x_1611_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1615_ = v___x_1611_;
v_isShared_1616_ = v_isSharedCheck_1642_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1642_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1641_; 
v_fst_1617_ = lean_ctor_get(v_a_1612_, 0);
v_snd_1618_ = lean_ctor_get(v_a_1612_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1612_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1620_ = v_a_1612_;
v_isShared_1621_ = v_isSharedCheck_1641_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_snd_1618_);
lean_inc(v_fst_1617_);
lean_dec(v_a_1612_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1641_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
uint8_t v___y_1623_; size_t v___x_1635_; size_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_ptr_addr(v_type_1595_);
v___x_1636_ = lean_ptr_addr(v_fst_1602_);
v___x_1637_ = lean_usize_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
v___y_1623_ = v___x_1637_;
goto v___jp_1622_;
}
else
{
size_t v___x_1638_; size_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1638_ = lean_ptr_addr(v_value_1596_);
v___x_1639_ = lean_ptr_addr(v_fst_1607_);
v___x_1640_ = lean_usize_dec_eq(v___x_1638_, v___x_1639_);
v___y_1623_ = v___x_1640_;
goto v___jp_1622_;
}
v___jp_1622_:
{
if (v___y_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_inc(v_declName_1594_);
lean_del_object(v___x_1620_);
lean_del_object(v___x_1615_);
lean_dec_ref_known(v_e_1475_, 4);
v___x_1624_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1594_, v_fst_1602_, v_fst_1607_, v_fst_1617_, v_nondep_1598_, v_snd_1618_, v_a_1478_, v_a_1479_, v_a_1613_);
return v___x_1624_;
}
else
{
size_t v___x_1625_; size_t v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = lean_ptr_addr(v_body_1597_);
v___x_1626_ = lean_ptr_addr(v_fst_1617_);
v___x_1627_ = lean_usize_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_inc(v_declName_1594_);
lean_del_object(v___x_1620_);
lean_del_object(v___x_1615_);
lean_dec_ref_known(v_e_1475_, 4);
v___x_1628_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1594_, v_fst_1602_, v_fst_1607_, v_fst_1617_, v_nondep_1598_, v_snd_1618_, v_a_1478_, v_a_1479_, v_a_1613_);
return v___x_1628_;
}
else
{
lean_object* v___x_1630_; 
lean_dec(v_fst_1617_);
lean_dec(v_fst_1607_);
lean_dec(v_fst_1602_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_e_1475_);
v___x_1630_ = v___x_1620_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_e_1475_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_snd_1618_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1630_);
v___x_1632_ = v___x_1615_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_a_1613_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
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
lean_dec(v_fst_1607_);
lean_dec(v_fst_1602_);
lean_dec_ref_known(v_e_1475_, 4);
return v___x_1611_;
}
}
else
{
lean_dec(v_fst_1602_);
lean_dec_ref_known(v_e_1475_, 4);
lean_dec(v_offset_1476_);
return v___x_1604_;
}
}
else
{
lean_dec_ref_known(v_e_1475_, 4);
lean_dec(v_offset_1476_);
return v___x_1599_;
}
}
case 10:
{
lean_object* v_data_1643_; lean_object* v_expr_1644_; lean_object* v___x_1645_; 
v_data_1643_ = lean_ctor_get(v_e_1475_, 0);
v_expr_1644_ = lean_ctor_get(v_e_1475_, 1);
lean_inc_ref(v_expr_1644_);
v___x_1645_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_expr_1644_, v_offset_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1667_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_a_1647_ = lean_ctor_get(v___x_1645_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1649_ = v___x_1645_;
v_isShared_1650_ = v_isSharedCheck_1667_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1667_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; lean_object* v_snd_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1666_; 
v_fst_1651_ = lean_ctor_get(v_a_1646_, 0);
v_snd_1652_ = lean_ctor_get(v_a_1646_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_a_1646_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1654_ = v_a_1646_;
v_isShared_1655_ = v_isSharedCheck_1666_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_snd_1652_);
lean_inc(v_fst_1651_);
lean_dec(v_a_1646_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1666_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
size_t v___x_1656_; size_t v___x_1657_; uint8_t v___x_1658_; 
v___x_1656_ = lean_ptr_addr(v_expr_1644_);
v___x_1657_ = lean_ptr_addr(v_fst_1651_);
v___x_1658_ = lean_usize_dec_eq(v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
lean_inc(v_data_1643_);
lean_del_object(v___x_1654_);
lean_del_object(v___x_1649_);
lean_dec_ref_known(v_e_1475_, 2);
v___x_1659_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_data_1643_, v_fst_1651_, v_snd_1652_, v_a_1478_, v_a_1479_, v_a_1647_);
return v___x_1659_;
}
else
{
lean_object* v___x_1661_; 
lean_dec(v_fst_1651_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v_e_1475_);
v___x_1661_ = v___x_1654_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_e_1475_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_snd_1652_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1661_);
v___x_1663_ = v___x_1649_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_a_1647_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1475_, 2);
return v___x_1645_;
}
}
case 11:
{
lean_object* v_typeName_1668_; lean_object* v_idx_1669_; lean_object* v_struct_1670_; lean_object* v___x_1671_; 
v_typeName_1668_ = lean_ctor_get(v_e_1475_, 0);
v_idx_1669_ = lean_ctor_get(v_e_1475_, 1);
v_struct_1670_ = lean_ctor_get(v_e_1475_, 2);
lean_inc_ref(v_struct_1670_);
v___x_1671_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1472_, v_varDeps_1473_, v_xs_1474_, v_struct_1670_, v_offset_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1693_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_a_1673_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1675_ = v___x_1671_;
v_isShared_1676_ = v_isSharedCheck_1693_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1693_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_fst_1677_; lean_object* v_snd_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1692_; 
v_fst_1677_ = lean_ctor_get(v_a_1672_, 0);
v_snd_1678_ = lean_ctor_get(v_a_1672_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1680_ = v_a_1672_;
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snd_1678_);
lean_inc(v_fst_1677_);
lean_dec(v_a_1672_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
size_t v___x_1682_; size_t v___x_1683_; uint8_t v___x_1684_; 
v___x_1682_ = lean_ptr_addr(v_struct_1670_);
v___x_1683_ = lean_ptr_addr(v_fst_1677_);
v___x_1684_ = lean_usize_dec_eq(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_inc(v_idx_1669_);
lean_inc(v_typeName_1668_);
lean_del_object(v___x_1680_);
lean_del_object(v___x_1675_);
lean_dec_ref_known(v_e_1475_, 3);
v___x_1685_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_typeName_1668_, v_idx_1669_, v_fst_1677_, v_snd_1678_, v_a_1478_, v_a_1479_, v_a_1673_);
return v___x_1685_;
}
else
{
lean_object* v___x_1687_; 
lean_dec(v_fst_1677_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_e_1475_);
v___x_1687_ = v___x_1680_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_e_1475_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_snd_1678_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1687_);
v___x_1689_ = v___x_1675_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_a_1673_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1475_, 3);
return v___x_1671_;
}
}
default: 
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_offset_1476_);
lean_dec_ref(v_e_1475_);
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3);
v___x_1695_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v___x_1694_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(lean_object* v_n_1696_, lean_object* v_varDeps_1697_, lean_object* v_xs_1698_, lean_object* v_e_1699_, lean_object* v_offset_1700_, lean_object* v_a_1701_, uint8_t v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_key_1705_; lean_object* v_a_1707_; lean_object* v___x_1720_; 
lean_inc(v_offset_1700_);
lean_inc_ref(v_e_1699_);
v_key_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1705_, 0, v_e_1699_);
lean_ctor_set(v_key_1705_, 1, v_offset_1700_);
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_a_1701_, v_key_1705_);
if (lean_obj_tag(v___x_1720_) == 1)
{
lean_object* v_val_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec_ref_known(v_key_1705_, 2);
lean_dec(v_offset_1700_);
lean_dec_ref(v_e_1699_);
v_val_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_val_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_val_1721_);
lean_ctor_set(v___x_1722_, 1, v_a_1701_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v_a_1704_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
lean_dec(v___x_1720_);
v___x_1724_ = l_Lean_Expr_looseBVarRange(v_e_1699_);
v___x_1725_ = lean_nat_dec_le(v___x_1724_, v_offset_1700_);
lean_dec(v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Expr_getAppFn(v_e_1699_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_deBruijnIndex_1727_; uint8_t v___x_1728_; 
v_deBruijnIndex_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_deBruijnIndex_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_nat_dec_le(v_offset_1700_, v_deBruijnIndex_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec(v_deBruijnIndex_1727_);
lean_dec(v_offset_1700_);
v___x_1729_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_nat_add(v_offset_1700_, v_n_1696_);
v___x_1731_ = lean_nat_dec_lt(v_deBruijnIndex_1727_, v___x_1730_);
lean_dec(v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_offset_1700_);
lean_dec_ref(v_e_1699_);
v___x_1732_ = lean_nat_sub(v_deBruijnIndex_1727_, v_n_1696_);
lean_dec(v_deBruijnIndex_1727_);
v___x_1733_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1732_, v_a_1704_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
v_a_1735_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1733_, 2);
v___x_1736_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_a_1734_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1735_);
return v___x_1736_;
}
else
{
lean_object* v_a_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref_known(v_key_1705_, 2);
lean_dec_ref(v_a_1701_);
v_a_1737_ = lean_ctor_get(v___x_1733_, 0);
v_a_1738_ = lean_ctor_get(v___x_1733_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1733_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_dec(v___x_1733_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1737_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_i_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v_expectedNumArgs_1752_; lean_object* v_numArgs_1753_; uint8_t v___x_1754_; 
v___x_1746_ = lean_nat_sub(v_deBruijnIndex_1727_, v_offset_1700_);
lean_dec(v_deBruijnIndex_1727_);
v___x_1747_ = lean_nat_sub(v_n_1696_, v___x_1746_);
lean_dec(v___x_1746_);
v___x_1748_ = lean_unsigned_to_nat(1u);
v_i_1749_ = lean_nat_sub(v___x_1747_, v___x_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1751_ = lean_array_get_borrowed(v___x_1750_, v_varDeps_1697_, v_i_1749_);
v_expectedNumArgs_1752_ = lean_array_get_size(v___x_1751_);
v_numArgs_1753_ = l_Lean_Expr_getAppNumArgs(v_e_1699_);
v___x_1754_ = lean_nat_dec_lt(v_expectedNumArgs_1752_, v_numArgs_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_nat_dec_eq(v_numArgs_1753_, v_expectedNumArgs_1752_);
lean_dec(v_numArgs_1753_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_i_1749_);
v___x_1756_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1757_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1756_, v_a_1702_, v_a_1703_, v_a_1704_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
if (lean_obj_tag(v_a_1758_) == 1)
{
lean_object* v_a_1759_; lean_object* v_val_1760_; lean_object* v___x_1761_; 
lean_dec(v_offset_1700_);
lean_dec_ref(v_e_1699_);
v_a_1759_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1757_, 2);
v_val_1760_ = lean_ctor_get(v_a_1758_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v_a_1758_, 1);
v___x_1761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_val_1760_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1759_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; 
lean_dec(v_a_1758_);
v_a_1762_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1757_, 2);
v_a_1707_ = v_a_1762_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_a_1763_; lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref_known(v_key_1705_, 2);
lean_dec_ref(v_a_1701_);
lean_dec(v_offset_1700_);
lean_dec_ref(v_e_1699_);
v_a_1763_ = lean_ctor_get(v___x_1757_, 0);
v_a_1764_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1757_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_inc(v_a_1763_);
lean_dec(v___x_1757_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1763_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_offset_1700_);
lean_dec_ref(v_e_1699_);
v___x_1772_ = lean_array_fget_borrowed(v_xs_1698_, v_i_1749_);
lean_dec(v_i_1749_);
lean_inc(v___x_1772_);
v___x_1773_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v___x_1772_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1773_;
}
}
else
{
lean_dec(v_numArgs_1753_);
lean_dec(v_i_1749_);
v_a_1707_ = v_a_1704_;
goto v___jp_1706_;
}
}
}
}
else
{
lean_dec_ref(v___x_1726_);
v_a_1707_ = v_a_1704_;
goto v___jp_1706_;
}
}
else
{
lean_object* v___x_1774_; 
lean_dec(v_offset_1700_);
v___x_1774_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1774_;
}
}
v___jp_1706_:
{
switch(lean_obj_tag(v_e_1699_))
{
case 9:
{
lean_object* v___x_1708_; 
lean_dec(v_offset_1700_);
v___x_1708_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
return v___x_1708_;
}
case 2:
{
lean_object* v___x_1709_; 
lean_dec(v_offset_1700_);
v___x_1709_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
return v___x_1709_;
}
case 0:
{
lean_object* v___x_1710_; 
lean_dec(v_offset_1700_);
v___x_1710_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
return v___x_1710_;
}
case 1:
{
lean_object* v___x_1711_; 
lean_dec(v_offset_1700_);
v___x_1711_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
return v___x_1711_;
}
case 4:
{
lean_object* v___x_1712_; 
lean_dec(v_offset_1700_);
v___x_1712_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
return v___x_1712_;
}
case 3:
{
lean_object* v___x_1713_; 
lean_dec(v_offset_1700_);
v___x_1713_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_e_1699_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
return v___x_1713_;
}
default: 
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1696_, v_varDeps_1697_, v_xs_1698_, v_e_1699_, v_offset_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1707_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v_a_1716_; lean_object* v_fst_1717_; lean_object* v_snd_1718_; lean_object* v___x_1719_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
v_a_1716_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1714_, 2);
v_fst_1717_ = lean_ctor_get(v_a_1715_, 0);
lean_inc(v_fst_1717_);
v_snd_1718_ = lean_ctor_get(v_a_1715_, 1);
lean_inc(v_snd_1718_);
lean_dec(v_a_1715_);
v___x_1719_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1705_, v_fst_1717_, v_snd_1718_, v_a_1702_, v_a_1703_, v_a_1716_);
return v___x_1719_;
}
else
{
lean_dec_ref_known(v_key_1705_, 2);
return v___x_1714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___boxed(lean_object* v_n_1775_, lean_object* v_varDeps_1776_, lean_object* v_xs_1777_, lean_object* v_e_1778_, lean_object* v_offset_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v_a_boxed_1784_; lean_object* v_res_1785_; 
v_a_boxed_1784_ = lean_unbox(v_a_1781_);
v_res_1785_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1775_, v_varDeps_1776_, v_xs_1777_, v_e_1778_, v_offset_1779_, v_a_1780_, v_a_boxed_1784_, v_a_1782_, v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec_ref(v_xs_1777_);
lean_dec_ref(v_varDeps_1776_);
lean_dec(v_n_1775_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_n_1786_, lean_object* v_varDeps_1787_, lean_object* v_xs_1788_, lean_object* v_e_1789_, lean_object* v_offset_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
uint8_t v_a_boxed_1795_; lean_object* v_res_1796_; 
v_a_boxed_1795_ = lean_unbox(v_a_1792_);
v_res_1796_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1786_, v_varDeps_1787_, v_xs_1788_, v_e_1789_, v_offset_1790_, v_a_1791_, v_a_boxed_1795_, v_a_1793_, v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec_ref(v_xs_1788_);
lean_dec_ref(v_varDeps_1787_);
lean_dec(v_n_1786_);
return v_res_1796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_unsigned_to_nat(16u);
v___x_1799_ = lean_mk_array(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v___x_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object* v_e_1803_, lean_object* v_n_1804_, lean_object* v_varDeps_1805_, lean_object* v_xs_1806_, uint8_t v_debug_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v_a_1812_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1840_ = l_Lean_Expr_looseBVarRange(v_e_1803_);
v___x_1841_ = lean_nat_dec_le(v___x_1840_, v___x_1810_);
lean_dec(v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_Expr_getAppFn(v_e_1803_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_deBruijnIndex_1843_; uint8_t v___x_1844_; 
v_deBruijnIndex_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_deBruijnIndex_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = lean_nat_dec_le(v___x_1810_, v_deBruijnIndex_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v_deBruijnIndex_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_e_1803_);
lean_ctor_set(v___x_1845_, 1, v___y_1809_);
return v___x_1845_;
}
else
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_nat_dec_lt(v_deBruijnIndex_1843_, v_n_1804_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v_e_1803_);
v___x_1847_ = lean_nat_sub(v_deBruijnIndex_1843_, v_n_1804_);
lean_dec(v_deBruijnIndex_1843_);
v___x_1848_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1847_, v___y_1809_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v_i_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_expectedNumArgs_1854_; lean_object* v_numArgs_1855_; uint8_t v___x_1856_; 
v___x_1849_ = lean_nat_sub(v_n_1804_, v_deBruijnIndex_1843_);
lean_dec(v_deBruijnIndex_1843_);
v___x_1850_ = lean_unsigned_to_nat(1u);
v_i_1851_ = lean_nat_sub(v___x_1849_, v___x_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1853_ = lean_array_get_borrowed(v___x_1852_, v_varDeps_1805_, v_i_1851_);
v_expectedNumArgs_1854_ = lean_array_get_size(v___x_1853_);
v_numArgs_1855_ = l_Lean_Expr_getAppNumArgs(v_e_1803_);
v___x_1856_ = lean_nat_dec_lt(v_expectedNumArgs_1854_, v_numArgs_1855_);
if (v___x_1856_ == 0)
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_eq(v_numArgs_1855_, v_expectedNumArgs_1854_);
lean_dec(v_numArgs_1855_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec(v_i_1851_);
v___x_1858_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1859_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1858_, v_debug_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
if (lean_obj_tag(v_a_1860_) == 1)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_e_1803_);
v_a_1861_ = lean_ctor_get(v___x_1859_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v___x_1859_, 0);
lean_dec(v_unused_1870_);
v___x_1863_ = v___x_1859_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1859_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_val_1865_; lean_object* v___x_1867_; 
v_val_1865_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_val_1865_);
lean_dec_ref_known(v_a_1860_, 1);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_val_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_val_1865_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_a_1861_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1871_; 
lean_dec(v_a_1860_);
v_a_1871_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1859_, 2);
v_a_1812_ = v_a_1871_;
goto v___jp_1811_;
}
}
else
{
lean_object* v_a_1872_; lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_e_1803_);
v_a_1872_ = lean_ctor_get(v___x_1859_, 0);
v_a_1873_ = lean_ctor_get(v___x_1859_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1859_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_inc(v_a_1872_);
lean_dec(v___x_1859_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1872_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec_ref(v_e_1803_);
v___x_1881_ = lean_array_fget_borrowed(v_xs_1806_, v_i_1851_);
lean_dec(v_i_1851_);
lean_inc(v___x_1881_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___y_1809_);
return v___x_1882_;
}
}
else
{
lean_dec(v_numArgs_1855_);
lean_dec(v_i_1851_);
v_a_1812_ = v___y_1809_;
goto v___jp_1811_;
}
}
}
}
else
{
lean_dec_ref(v___x_1842_);
v_a_1812_ = v___y_1809_;
goto v___jp_1811_;
}
}
else
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_e_1803_);
lean_ctor_set(v___x_1883_, 1, v___y_1809_);
return v___x_1883_;
}
v___jp_1811_:
{
switch(lean_obj_tag(v_e_1803_))
{
case 9:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_e_1803_);
lean_ctor_set(v___x_1813_, 1, v_a_1812_);
return v___x_1813_;
}
case 2:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_e_1803_);
lean_ctor_set(v___x_1814_, 1, v_a_1812_);
return v___x_1814_;
}
case 0:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_e_1803_);
lean_ctor_set(v___x_1815_, 1, v_a_1812_);
return v___x_1815_;
}
case 1:
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_e_1803_);
lean_ctor_set(v___x_1816_, 1, v_a_1812_);
return v___x_1816_;
}
case 4:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_e_1803_);
lean_ctor_set(v___x_1817_, 1, v_a_1812_);
return v___x_1817_;
}
case 3:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_e_1803_);
lean_ctor_set(v___x_1818_, 1, v_a_1812_);
return v___x_1818_;
}
default: 
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1);
v___x_1820_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1804_, v_varDeps_1805_, v_xs_1806_, v_e_1803_, v___x_1810_, v___x_1819_, v_debug_1807_, v___y_1808_, v_a_1812_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1830_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_a_1822_ = lean_ctor_get(v___x_1820_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1824_ = v___x_1820_;
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_fst_1826_; lean_object* v___x_1828_; 
v_fst_1826_ = lean_ctor_get(v_a_1821_, 0);
lean_inc(v_fst_1826_);
lean_dec(v_a_1821_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_fst_1826_);
v___x_1828_ = v___x_1824_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1826_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_a_1822_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1831_ = lean_ctor_get(v___x_1820_, 0);
v_a_1832_ = lean_ctor_get(v___x_1820_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1820_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_inc(v_a_1831_);
lean_dec(v___x_1820_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1831_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object* v_e_1884_, lean_object* v_n_1885_, lean_object* v_varDeps_1886_, lean_object* v_xs_1887_, lean_object* v_debug_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v_debug_boxed_1891_; lean_object* v_res_1892_; 
v_debug_boxed_1891_ = lean_unbox(v_debug_1888_);
v_res_1892_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(v_e_1884_, v_n_1885_, v_varDeps_1886_, v_xs_1887_, v_debug_boxed_1891_, v___y_1889_, v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v_xs_1887_);
lean_dec_ref(v_varDeps_1886_);
lean_dec(v_n_1885_);
return v_res_1892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1896_ = lean_unsigned_to_nat(16u);
v___x_1897_ = lean_unsigned_to_nat(62u);
v___x_1898_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1));
v___x_1899_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0));
v___x_1900_ = l_mkPanicMessageWithDecl(v___x_1899_, v___x_1898_, v___x_1897_, v___x_1896_, v___x_1895_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1901_, lean_object* v_xs_1902_, lean_object* v_varDeps_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v_debug_1913_; lean_object* v_env_1914_; lean_object* v_n_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1911_ = lean_st_ref_get(v_a_1905_);
v___x_1912_ = lean_st_ref_get(v_a_1909_);
v_debug_1913_ = lean_ctor_get_uint8(v___x_1911_, sizeof(void*)*11);
lean_dec(v___x_1911_);
v_env_1914_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_ref(v_env_1914_);
lean_dec(v___x_1912_);
v_n_1915_ = lean_array_get_size(v_xs_1902_);
v___x_1916_ = lean_box(v_debug_1913_);
v___f_1917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1917_, 0, v_e_1901_);
lean_closure_set(v___f_1917_, 1, v_n_1915_);
lean_closure_set(v___f_1917_, 2, v_varDeps_1903_);
lean_closure_set(v___f_1917_, 3, v_xs_1902_);
lean_closure_set(v___f_1917_, 4, v___x_1916_);
v___x_1918_ = 0;
v___x_1919_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1919_, 0, v_env_1914_);
lean_ctor_set_uint8(v___x_1919_, sizeof(void*)*1, v___x_1918_);
lean_ctor_set_uint8(v___x_1919_, sizeof(void*)*1 + 1, v___x_1918_);
v___x_1920_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1917_, v___x_1919_, v_a_1905_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1931_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1931_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1931_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
if (lean_obj_tag(v_a_1921_) == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref_known(v_a_1921_, 1);
lean_del_object(v___x_1923_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2);
v___x_1926_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_1925_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1926_;
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; 
v_a_1927_ = lean_ctor_get(v_a_1921_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v_a_1921_, 1);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v_a_1927_);
v___x_1929_ = v___x_1923_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1932_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1920_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1920_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1940_, lean_object* v_xs_1941_, lean_object* v_varDeps_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1940_, v_xs_1941_, v_varDeps_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_1951_, lean_object* v_m_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1952_, v_a_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1955_, lean_object* v_m_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(v_00_u03b2_1955_, v_m_1956_, v_a_1957_);
lean_dec_ref(v_a_1957_);
lean_dec_ref(v_m_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_1959_, lean_object* v_a_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1960_, v_x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1963_, lean_object* v_a_1964_, lean_object* v_x_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_1963_, v_a_1964_, v_x_1965_);
lean_dec(v_x_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1967_, lean_object* v_type_1968_, lean_object* v_val_1969_, lean_object* v_k_1970_, uint8_t v_nondep_1971_, uint8_t v_kind_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___f_1980_; lean_object* v___x_1981_; 
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
v___f_1980_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1980_, 0, v_k_1970_);
lean_closure_set(v___f_1980_, 1, v___y_1973_);
lean_closure_set(v___f_1980_, 2, v___y_1974_);
v___x_1981_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1967_, v_type_1968_, v_val_1969_, v___f_1980_, v_nondep_1971_, v_kind_1972_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1981_) == 0)
{
return v___x_1981_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1990_, lean_object* v_type_1991_, lean_object* v_val_1992_, lean_object* v_k_1993_, lean_object* v_nondep_1994_, lean_object* v_kind_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v_nondep_boxed_2003_; uint8_t v_kind_boxed_2004_; lean_object* v_res_2005_; 
v_nondep_boxed_2003_ = lean_unbox(v_nondep_1994_);
v_kind_boxed_2004_ = lean_unbox(v_kind_1995_);
v_res_2005_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1990_, v_type_1991_, v_val_1992_, v_k_1993_, v_nondep_boxed_2003_, v_kind_boxed_2004_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_2006_, lean_object* v_name_2007_, lean_object* v_type_2008_, lean_object* v_val_2009_, lean_object* v_k_2010_, uint8_t v_nondep_2011_, uint8_t v_kind_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_2007_, v_type_2008_, v_val_2009_, v_k_2010_, v_nondep_2011_, v_kind_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_name_2022_, lean_object* v_type_2023_, lean_object* v_val_2024_, lean_object* v_k_2025_, lean_object* v_nondep_2026_, lean_object* v_kind_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_nondep_boxed_2035_; uint8_t v_kind_boxed_2036_; lean_object* v_res_2037_; 
v_nondep_boxed_2035_ = lean_unbox(v_nondep_2026_);
v_kind_boxed_2036_ = lean_unbox(v_kind_2027_);
v_res_2037_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_2021_, v_name_2022_, v_type_2023_, v_val_2024_, v_k_2025_, v_nondep_boxed_2035_, v_kind_boxed_2036_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_2038_, size_t v_sz_2039_, size_t v_i_2040_, lean_object* v_bs_2041_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = lean_usize_dec_lt(v_i_2040_, v_sz_2039_);
if (v___x_2042_ == 0)
{
return v_bs_2041_;
}
else
{
lean_object* v_v_2043_; lean_object* v___x_2044_; lean_object* v_bs_x27_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
v_v_2043_ = lean_array_uget(v_bs_2041_, v_i_2040_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v_bs_x27_2045_ = lean_array_uset(v_bs_2041_, v_i_2040_, v___x_2044_);
v___x_2046_ = l_Lean_instInhabitedExpr;
v___x_2047_ = lean_array_get_borrowed(v___x_2046_, v_xs_2038_, v_v_2043_);
lean_dec(v_v_2043_);
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2040_, v___x_2048_);
lean_inc(v___x_2047_);
v___x_2050_ = lean_array_uset(v_bs_x27_2045_, v_i_2040_, v___x_2047_);
v_i_2040_ = v___x_2049_;
v_bs_2041_ = v___x_2050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_2052_, lean_object* v_sz_2053_, lean_object* v_i_2054_, lean_object* v_bs_2055_){
_start:
{
size_t v_sz_boxed_2056_; size_t v_i_boxed_2057_; lean_object* v_res_2058_; 
v_sz_boxed_2056_ = lean_unbox_usize(v_sz_2053_);
lean_dec(v_sz_2053_);
v_i_boxed_2057_ = lean_unbox_usize(v_i_2054_);
lean_dec(v_i_2054_);
v_res_2058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2052_, v_sz_boxed_2056_, v_i_boxed_2057_, v_bs_2055_);
lean_dec_ref(v_xs_2052_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_2059_, lean_object* v_i_2060_, lean_object* v_varDeps_2061_, lean_object* v_args_2062_, lean_object* v_body_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_2059_, v_i_2060_, v_varDeps_2061_, v_args_2062_, v_body_2063_, v_x_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v_i_2060_);
return v_res_2072_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2074_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2075_ = lean_unsigned_to_nat(30u);
v___x_2076_ = lean_unsigned_to_nat(254u);
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_2078_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2079_ = l_mkPanicMessageWithDecl(v___x_2078_, v___x_2077_, v___x_2076_, v___x_2075_, v___x_2074_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_2080_, lean_object* v_args_2081_, lean_object* v_f_2082_, lean_object* v_xs_2083_, lean_object* v_i_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_array_get_size(v_args_2081_);
v___x_2093_ = lean_nat_dec_lt(v_i_2084_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec(v_i_2084_);
lean_dec_ref(v_args_2081_);
lean_inc_ref(v_xs_2083_);
v___x_2094_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_f_2082_, v_xs_2083_, v_varDeps_2080_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = 1;
v___x_2097_ = l_Lean_Meta_mkLetFVars(v_xs_2083_, v_a_2095_, v___x_2093_, v___x_2093_, v___x_2096_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec_ref(v_xs_2083_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Meta_Sym_shareCommonInc(v_a_2098_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2099_;
}
else
{
return v___x_2097_;
}
}
else
{
lean_dec_ref(v_xs_2083_);
return v___x_2094_;
}
}
else
{
if (lean_obj_tag(v_f_2082_) == 6)
{
lean_object* v_binderName_2100_; lean_object* v_binderType_2101_; lean_object* v_body_2102_; lean_object* v_varPos_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v_ys_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_binderName_2100_ = lean_ctor_get(v_f_2082_, 0);
lean_inc(v_binderName_2100_);
v_binderType_2101_ = lean_ctor_get(v_f_2082_, 1);
lean_inc_ref(v_binderType_2101_);
v_body_2102_ = lean_ctor_get(v_f_2082_, 2);
lean_inc_ref(v_body_2102_);
lean_dec_ref_known(v_f_2082_, 3);
v_varPos_2103_ = lean_array_fget(v_varDeps_2080_, v_i_2084_);
v_sz_2104_ = lean_array_size(v_varPos_2103_);
v___x_2105_ = ((size_t)0ULL);
lean_inc(v_varPos_2103_);
v_ys_2106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2083_, v_sz_2104_, v___x_2105_, v_varPos_2103_);
v___x_2107_ = lean_array_fget_borrowed(v_args_2081_, v_i_2084_);
v___x_2108_ = 0;
lean_inc(v___x_2107_);
v___x_2109_ = l_Lean_Expr_betaRev(v___x_2107_, v_ys_2106_, v___x_2108_, v___x_2108_);
lean_dec_ref(v_ys_2106_);
v___x_2110_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2109_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v_type_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___f_2112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2112_, 0, v_xs_2083_);
lean_closure_set(v___f_2112_, 1, v_i_2084_);
lean_closure_set(v___f_2112_, 2, v_varDeps_2080_);
lean_closure_set(v___f_2112_, 3, v_args_2081_);
lean_closure_set(v___f_2112_, 4, v_body_2102_);
v___x_2113_ = lean_array_get_size(v_varPos_2103_);
lean_dec(v_varPos_2103_);
v_type_2114_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_2101_, v___x_2113_);
v___x_2115_ = 0;
v___x_2116_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_2100_, v_type_2114_, v_a_2111_, v___f_2112_, v___x_2093_, v___x_2115_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2116_;
}
else
{
lean_dec(v_varPos_2103_);
lean_dec_ref(v_body_2102_);
lean_dec_ref(v_binderType_2101_);
lean_dec(v_binderName_2100_);
lean_dec(v_i_2084_);
lean_dec_ref(v_xs_2083_);
lean_dec_ref(v_args_2081_);
lean_dec_ref(v_varDeps_2080_);
return v___x_2110_;
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_i_2084_);
lean_dec_ref(v_xs_2083_);
lean_dec_ref(v_f_2082_);
lean_dec_ref(v_args_2081_);
lean_dec_ref(v_varDeps_2080_);
v___x_2117_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_2118_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2117_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_2119_, lean_object* v_i_2120_, lean_object* v_varDeps_2121_, lean_object* v_args_2122_, lean_object* v_body_2123_, lean_object* v_x_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Meta_Sym_shareCommonInc(v_x_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = lean_array_push(v_xs_2119_, v_a_2133_);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_add(v_i_2120_, v___x_2135_);
v___x_2137_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2121_, v_args_2122_, v_body_2123_, v___x_2134_, v___x_2136_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2137_;
}
else
{
lean_dec_ref(v_body_2123_);
lean_dec_ref(v_args_2122_);
lean_dec_ref(v_varDeps_2121_);
lean_dec_ref(v_xs_2119_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_2138_, lean_object* v_args_2139_, lean_object* v_f_2140_, lean_object* v_xs_2141_, lean_object* v_i_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2138_, v_args_2139_, v_f_2140_, v_xs_2141_, v_i_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_2151_, lean_object* v_args_2152_, lean_object* v___h_2153_, lean_object* v_f_2154_, lean_object* v_xs_2155_, lean_object* v_i_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2151_, v_args_2152_, v_f_2154_, v_xs_2155_, v_i_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_2165_, lean_object* v_args_2166_, lean_object* v___h_2167_, lean_object* v_f_2168_, lean_object* v_xs_2169_, lean_object* v_i_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2165_, v_args_2166_, v___h_2167_, v_f_2168_, v_xs_2169_, v_i_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
return v_res_2178_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2181_ = lean_unsigned_to_nat(40u);
v___x_2182_ = lean_unsigned_to_nat(251u);
v___x_2183_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2185_ = l_mkPanicMessageWithDecl(v___x_2184_, v___x_2183_, v___x_2182_, v___x_2181_, v___x_2180_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 5)
{
lean_object* v_fn_2197_; lean_object* v_arg_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_fn_2197_ = lean_ctor_get(v_x_2187_, 0);
lean_inc_ref(v_fn_2197_);
v_arg_2198_ = lean_ctor_get(v_x_2187_, 1);
lean_inc_ref(v_arg_2198_);
lean_dec_ref_known(v_x_2187_, 2);
v___x_2199_ = lean_array_set(v_x_2188_, v_x_2189_, v_arg_2198_);
v___x_2200_ = lean_unsigned_to_nat(1u);
v___x_2201_ = lean_nat_sub(v_x_2189_, v___x_2200_);
lean_dec(v_x_2189_);
v_x_2187_ = v_fn_2197_;
v_x_2188_ = v___x_2199_;
v_x_2189_ = v___x_2201_;
goto _start;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
lean_dec(v_x_2189_);
v___x_2203_ = lean_array_get_size(v_x_2188_);
v___x_2204_ = lean_array_get_size(v_varDeps_2186_);
v___x_2205_ = lean_nat_dec_eq(v___x_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v_x_2188_);
lean_dec_ref(v_x_2187_);
lean_dec_ref(v_varDeps_2186_);
v___x_2206_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2207_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2206_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2210_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2186_, v_x_2188_, v_x_2187_, v___x_2209_, v___x_2208_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2211_, v_x_2212_, v_x_2213_, v_x_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2223_; lean_object* v_dummy_2224_; 
v___x_2223_ = lean_box(0);
v_dummy_2224_ = l_Lean_Expr_sort___override(v___x_2223_);
return v_dummy_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2225_, lean_object* v_varDeps_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_dummy_2234_; lean_object* v_nargs_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_dummy_2234_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2235_ = l_Lean_Expr_getAppNumArgs(v_e_2225_);
lean_inc(v_nargs_2235_);
v___x_2236_ = lean_mk_array(v_nargs_2235_, v_dummy_2234_);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_sub(v_nargs_2235_, v___x_2237_);
lean_dec(v_nargs_2235_);
v___x_2239_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2226_, v_e_2225_, v___x_2236_, v___x_2238_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2240_, lean_object* v_varDeps_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2240_, v_varDeps_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_snd_2253_; lean_object* v_fst_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2287_; 
v_snd_2253_ = lean_ctor_get(v_a_2251_, 1);
v_fst_2254_ = lean_ctor_get(v_a_2251_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_a_2251_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2256_ = v_a_2251_;
v_isShared_2257_ = v_isSharedCheck_2287_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_snd_2253_);
lean_inc(v_fst_2254_);
lean_dec(v_a_2251_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2287_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_fst_2258_; lean_object* v_snd_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2286_; 
v_fst_2258_ = lean_ctor_get(v_snd_2253_, 0);
v_snd_2259_ = lean_ctor_get(v_snd_2253_, 1);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_snd_2253_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2261_ = v_snd_2253_;
v_isShared_2262_ = v_isSharedCheck_2286_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_snd_2259_);
lean_inc(v_fst_2258_);
lean_dec(v_snd_2253_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2286_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_nat_dec_lt(v___x_2263_, v_fst_2258_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2266_; 
if (v_isShared_2262_ == 0)
{
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_fst_2258_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_snd_2259_);
v___x_2266_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2266_);
v___x_2268_ = v___x_2256_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_fst_2254_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_sub(v_fst_2258_, v___x_2272_);
lean_dec(v_fst_2258_);
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_array_get_borrowed(v___x_2274_, v_argUnivs_2250_, v___x_2273_);
lean_inc(v___x_2275_);
v___x_2276_ = l_Lean_mkLevelIMax_x27(v___x_2275_, v_fst_2254_);
v___x_2277_ = l_Lean_Level_normalize(v___x_2276_);
lean_dec(v___x_2276_);
lean_inc(v___x_2277_);
v___x_2278_ = lean_array_push(v_snd_2259_, v___x_2277_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2278_);
lean_ctor_set(v___x_2261_, 0, v___x_2273_);
v___x_2280_ = v___x_2261_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2280_);
lean_ctor_set(v___x_2256_, 0, v___x_2277_);
v___x_2282_ = v___x_2256_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
v_a_2251_ = v___x_2282_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2288_, lean_object* v_a_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2288_, v_a_2289_);
lean_dec_ref(v_argUnivs_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2294_, lean_object* v_argUnivs_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
if (lean_obj_tag(v_type_2294_) == 7)
{
lean_object* v_binderType_2303_; lean_object* v_body_2304_; lean_object* v___x_2305_; 
v_binderType_2303_ = lean_ctor_get(v_type_2294_, 1);
lean_inc_ref(v_binderType_2303_);
v_body_2304_ = lean_ctor_get(v_type_2294_, 2);
lean_inc_ref(v_body_2304_);
lean_dec_ref_known(v_type_2294_, 3);
v___x_2305_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2303_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = lean_array_push(v_argUnivs_2295_, v_a_2306_);
v_type_2294_ = v_body_2304_;
v_argUnivs_2295_ = v___x_2307_;
goto _start;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_body_2304_);
lean_dec_ref(v_argUnivs_2295_);
v_a_2309_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2305_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2305_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2294_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = lean_array_get_size(v_argUnivs_2295_);
v___x_2320_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2318_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2295_, v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2342_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2342_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2342_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_snd_2328_; lean_object* v_snd_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2340_; 
v_snd_2328_ = lean_ctor_get(v_a_2324_, 1);
lean_inc(v_snd_2328_);
lean_dec(v_a_2324_);
v_snd_2329_ = lean_ctor_get(v_snd_2328_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_snd_2328_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v_snd_2328_, 0);
lean_dec(v_unused_2341_);
v___x_2331_ = v_snd_2328_;
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_snd_2329_);
lean_dec(v_snd_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = l_Array_reverse___redArg(v_snd_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2333_);
lean_ctor_set(v___x_2331_, 0, v_argUnivs_2295_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_argUnivs_2295_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2335_);
v___x_2337_ = v___x_2326_;
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
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v_argUnivs_2295_);
v_a_2343_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2323_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2323_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v_argUnivs_2295_);
v_a_2351_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2317_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2317_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2359_, lean_object* v_argUnivs_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2359_, v_argUnivs_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2369_, lean_object* v_inst_2370_, lean_object* v_a_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2369_, v_a_2371_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2380_, lean_object* v_inst_2381_, lean_object* v_a_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2380_, v_inst_2381_, v_a_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_argUnivs_2380_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2400_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2391_, v___x_2399_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2410_, lean_object* v_argUnivs_2411_, lean_object* v_declName_2412_, lean_object* v_fType_2413_, lean_object* v_i_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v_00_u03b1_2417_; lean_object* v_00_u03b2_2418_; lean_object* v_u_2419_; lean_object* v_v_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2416_ = lean_box(0);
v_00_u03b1_2417_ = l_Lean_Expr_bindingDomain_x21(v_fType_2413_);
v_00_u03b2_2418_ = l_Lean_Expr_bindingBody_x21(v_fType_2413_);
v_u_2419_ = lean_array_get_borrowed(v___x_2416_, v_argUnivs_2411_, v_i_2414_);
v_v_2420_ = lean_array_get_borrowed(v___x_2416_, v_fnUnivs_2410_, v_i_2414_);
v___x_2421_ = lean_box(0);
lean_inc(v_v_2420_);
v___x_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_v_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
lean_inc(v_u_2419_);
v___x_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_u_2419_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_mkConst(v_declName_2412_, v___x_2423_);
v___x_2425_ = l_Lean_mkAppB(v___x_2424_, v_00_u03b1_2417_, v_00_u03b2_2418_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2427_, lean_object* v_argUnivs_2428_, lean_object* v_declName_2429_, lean_object* v_fType_2430_, lean_object* v_i_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2427_, v_argUnivs_2428_, v_declName_2429_, v_fType_2430_, v_i_2431_);
lean_dec(v_i_2431_);
lean_dec_ref(v_fType_2430_);
lean_dec_ref(v_argUnivs_2428_);
lean_dec_ref(v_fnUnivs_2427_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2434_, lean_object* v_argUnivs_2435_, lean_object* v_declName_2436_, lean_object* v_fType_2437_, lean_object* v_i_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2434_, v_argUnivs_2435_, v_declName_2436_, v_fType_2437_, v_i_2438_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2447_, lean_object* v_argUnivs_2448_, lean_object* v_declName_2449_, lean_object* v_fType_2450_, lean_object* v_i_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2447_, v_argUnivs_2448_, v_declName_2449_, v_fType_2450_, v_i_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_i_2451_);
lean_dec_ref(v_fType_2450_);
lean_dec_ref(v_argUnivs_2448_);
lean_dec_ref(v_fnUnivs_2447_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2460_, lean_object* v_a_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___y_2470_; lean_object* v___x_2473_; uint8_t v_debug_2474_; 
v___x_2473_ = lean_st_ref_get(v___y_2463_);
v_debug_2474_ = lean_ctor_get_uint8(v___x_2473_, sizeof(void*)*11);
lean_dec(v___x_2473_);
if (v_debug_2474_ == 0)
{
v___y_2470_ = v___y_2463_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2460_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; 
lean_dec_ref_known(v___x_2475_, 1);
v___x_2476_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_dec_ref_known(v___x_2476_, 1);
v___y_2470_ = v___y_2463_;
goto v___jp_2469_;
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_a_2461_);
lean_dec_ref(v_f_2460_);
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_a_2461_);
lean_dec_ref(v_f_2460_);
v_a_2485_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2475_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2475_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = l_Lean_Expr_app___override(v_f_2460_, v_a_2461_);
v___x_2472_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2471_, v___y_2470_);
return v___x_2472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2493_, lean_object* v_a_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2493_, v_a_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2503_, lean_object* v_a_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2503_, v_a_2504_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2516_, lean_object* v_a_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2516_, v_a_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
return v_res_2528_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_15370__overap_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15370__overap_2542_ = lean_panic_fn_borrowed(v___x_2541_, v_msg_2530_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2536_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
v___x_2543_ = lean_apply_10(v___x_15370__overap_2542_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, lean_box(0));
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
return v_res_2555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2567_ = lean_unsigned_to_nat(11u);
v___x_2568_ = lean_unsigned_to_nat(346u);
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2570_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2571_ = l_mkPanicMessageWithDecl(v___x_2570_, v___x_2569_, v___x_2568_, v___x_2567_, v___x_2566_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2572_, lean_object* v_fnUnivs_2573_, lean_object* v_argUnivs_2574_, lean_object* v_simpBody_2575_, lean_object* v_e_2576_, lean_object* v_i_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
switch(lean_obj_tag(v_e_2576_))
{
case 5:
{
lean_object* v_fn_2588_; lean_object* v_arg_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_fn_2588_ = lean_ctor_get(v_e_2576_, 0);
lean_inc_ref_n(v_fn_2588_, 2);
v_arg_2589_ = lean_ctor_get(v_e_2576_, 1);
lean_inc_ref(v_arg_2589_);
lean_dec_ref_known(v_e_2576_, 2);
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_nat_sub(v_i_2577_, v___x_2590_);
v___x_2592_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2572_, v_fnUnivs_2573_, v_argUnivs_2574_, v_simpBody_2575_, v_fn_2588_, v___x_2591_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v___x_2591_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2713_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2713_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2713_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_fst_2597_; lean_object* v_snd_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2712_; 
v_fst_2597_ = lean_ctor_get(v_a_2593_, 0);
v_snd_2598_ = lean_ctor_get(v_a_2593_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_a_2593_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2600_ = v_a_2593_;
v_isShared_2601_ = v_isSharedCheck_2712_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snd_2598_);
lean_inc(v_fst_2597_);
lean_dec(v_a_2593_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2712_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_r_2603_; lean_object* v___x_2611_; 
lean_inc(v_a_2586_);
lean_inc_ref(v_a_2585_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
lean_inc_ref(v_arg_2589_);
v___x_2611_ = lean_sym_simp(v_arg_2589_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; uint8_t v___y_2614_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
if (lean_obj_tag(v_fst_2597_) == 0)
{
if (lean_obj_tag(v_a_2612_) == 0)
{
uint8_t v_contextDependent_2616_; 
lean_dec_ref(v_arg_2589_);
lean_dec_ref(v_fn_2588_);
v_contextDependent_2616_ = lean_ctor_get_uint8(v_fst_2597_, 1);
lean_dec_ref_known(v_fst_2597_, 0);
if (v_contextDependent_2616_ == 0)
{
uint8_t v_contextDependent_2617_; 
v_contextDependent_2617_ = lean_ctor_get_uint8(v_a_2612_, 1);
lean_dec_ref_known(v_a_2612_, 0);
v___y_2614_ = v_contextDependent_2617_;
goto v___jp_2613_;
}
else
{
lean_dec_ref_known(v_a_2612_, 0);
v___y_2614_ = v_contextDependent_2616_;
goto v___jp_2613_;
}
}
else
{
uint8_t v_contextDependent_2618_; lean_object* v_e_x27_2619_; lean_object* v_proof_2620_; uint8_t v_contextDependent_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2645_; 
v_contextDependent_2618_ = lean_ctor_get_uint8(v_fst_2597_, 1);
lean_dec_ref_known(v_fst_2597_, 0);
v_e_x27_2619_ = lean_ctor_get(v_a_2612_, 0);
v_proof_2620_ = lean_ctor_get(v_a_2612_, 1);
v_contextDependent_2621_ = lean_ctor_get_uint8(v_a_2612_, sizeof(void*)*2 + 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2612_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2623_ = v_a_2612_;
v_isShared_2624_ = v_isSharedCheck_2645_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_proof_2620_);
lean_inc(v_e_x27_2619_);
lean_dec(v_a_2612_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2645_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; 
lean_inc_ref(v_e_x27_2619_);
lean_inc_ref(v_fn_2588_);
v___x_2625_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2588_, v_e_x27_2619_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v_a_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; uint8_t v___y_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2628_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2573_, v_argUnivs_2574_, v___x_2627_, v_snd_2598_, v_i_2577_);
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
v___x_2630_ = l_Lean_mkApp4(v_a_2629_, v_arg_2589_, v_e_x27_2619_, v_fn_2588_, v_proof_2620_);
v___x_2631_ = 0;
if (v_contextDependent_2618_ == 0)
{
v___y_2633_ = v_contextDependent_2621_;
goto v___jp_2632_;
}
else
{
v___y_2633_ = v_contextDependent_2618_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2635_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v___x_2630_);
lean_ctor_set(v___x_2623_, 0, v_a_2626_);
v___x_2635_ = v___x_2623_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v___x_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*2, v___x_2631_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*2 + 1, v___y_2633_);
v_r_2603_ = v___x_2635_;
goto v___jp_2602_;
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_del_object(v___x_2623_);
lean_dec_ref(v_proof_2620_);
lean_dec_ref(v_e_x27_2619_);
lean_del_object(v___x_2600_);
lean_dec(v_snd_2598_);
lean_del_object(v___x_2595_);
lean_dec_ref(v_arg_2589_);
lean_dec_ref(v_fn_2588_);
v_a_2637_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2625_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2625_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2612_) == 0)
{
lean_object* v_e_x27_2646_; lean_object* v_proof_2647_; uint8_t v_contextDependent_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2673_; 
v_e_x27_2646_ = lean_ctor_get(v_fst_2597_, 0);
v_proof_2647_ = lean_ctor_get(v_fst_2597_, 1);
v_contextDependent_2648_ = lean_ctor_get_uint8(v_fst_2597_, sizeof(void*)*2 + 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_fst_2597_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2650_ = v_fst_2597_;
v_isShared_2651_ = v_isSharedCheck_2673_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_proof_2647_);
lean_inc(v_e_x27_2646_);
lean_dec(v_fst_2597_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2673_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
uint8_t v_contextDependent_2652_; lean_object* v___x_2653_; 
v_contextDependent_2652_ = lean_ctor_get_uint8(v_a_2612_, 1);
lean_dec_ref_known(v_a_2612_, 0);
lean_inc_ref(v_arg_2589_);
lean_inc_ref(v_e_x27_2646_);
v___x_2653_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2646_, v_arg_2589_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v_a_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; uint8_t v___y_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2656_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2573_, v_argUnivs_2574_, v___x_2655_, v_snd_2598_, v_i_2577_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v___x_2658_ = l_Lean_mkApp4(v_a_2657_, v_fn_2588_, v_e_x27_2646_, v_proof_2647_, v_arg_2589_);
v___x_2659_ = 0;
if (v_contextDependent_2648_ == 0)
{
v___y_2661_ = v_contextDependent_2652_;
goto v___jp_2660_;
}
else
{
v___y_2661_ = v_contextDependent_2648_;
goto v___jp_2660_;
}
v___jp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2658_);
lean_ctor_set(v___x_2650_, 0, v_a_2654_);
v___x_2663_ = v___x_2650_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2654_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*2, v___x_2659_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*2 + 1, v___y_2661_);
v_r_2603_ = v___x_2663_;
goto v___jp_2602_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_del_object(v___x_2650_);
lean_dec_ref(v_proof_2647_);
lean_dec_ref(v_e_x27_2646_);
lean_del_object(v___x_2600_);
lean_dec(v_snd_2598_);
lean_del_object(v___x_2595_);
lean_dec_ref(v_arg_2589_);
lean_dec_ref(v_fn_2588_);
v_a_2665_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2653_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2653_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2674_; lean_object* v_proof_2675_; uint8_t v_contextDependent_2676_; lean_object* v_e_x27_2677_; lean_object* v_proof_2678_; uint8_t v_contextDependent_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2703_; 
v_e_x27_2674_ = lean_ctor_get(v_fst_2597_, 0);
lean_inc_ref(v_e_x27_2674_);
v_proof_2675_ = lean_ctor_get(v_fst_2597_, 1);
lean_inc_ref(v_proof_2675_);
v_contextDependent_2676_ = lean_ctor_get_uint8(v_fst_2597_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2597_, 2);
v_e_x27_2677_ = lean_ctor_get(v_a_2612_, 0);
v_proof_2678_ = lean_ctor_get(v_a_2612_, 1);
v_contextDependent_2679_ = lean_ctor_get_uint8(v_a_2612_, sizeof(void*)*2 + 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_a_2612_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2681_ = v_a_2612_;
v_isShared_2682_ = v_isSharedCheck_2703_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_proof_2678_);
lean_inc(v_e_x27_2677_);
lean_dec(v_a_2612_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2703_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; 
lean_inc_ref(v_e_x27_2677_);
lean_inc_ref(v_e_x27_2674_);
v___x_2683_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2674_, v_e_x27_2677_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v_a_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; uint8_t v___y_2691_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2686_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2573_, v_argUnivs_2574_, v___x_2685_, v_snd_2598_, v_i_2577_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2686_);
v___x_2688_ = l_Lean_mkApp6(v_a_2687_, v_fn_2588_, v_e_x27_2674_, v_arg_2589_, v_e_x27_2677_, v_proof_2675_, v_proof_2678_);
v___x_2689_ = 0;
if (v_contextDependent_2676_ == 0)
{
v___y_2691_ = v_contextDependent_2679_;
goto v___jp_2690_;
}
else
{
v___y_2691_ = v_contextDependent_2676_;
goto v___jp_2690_;
}
v___jp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2688_);
lean_ctor_set(v___x_2681_, 0, v_a_2684_);
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2684_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*2, v___x_2689_);
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*2 + 1, v___y_2691_);
v_r_2603_ = v___x_2693_;
goto v___jp_2602_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_del_object(v___x_2681_);
lean_dec_ref(v_proof_2678_);
lean_dec_ref(v_e_x27_2677_);
lean_dec_ref(v_proof_2675_);
lean_dec_ref(v_e_x27_2674_);
lean_del_object(v___x_2600_);
lean_dec(v_snd_2598_);
lean_del_object(v___x_2595_);
lean_dec_ref(v_arg_2589_);
lean_dec_ref(v_fn_2588_);
v_a_2695_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2683_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2683_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
v___jp_2613_:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2614_);
v_r_2603_ = v___x_2615_;
goto v___jp_2602_;
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_del_object(v___x_2600_);
lean_dec(v_snd_2598_);
lean_dec(v_fst_2597_);
lean_del_object(v___x_2595_);
lean_dec_ref(v_arg_2589_);
lean_dec_ref(v_fn_2588_);
v_a_2704_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2611_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2611_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
v___jp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = l_Lean_Expr_bindingBody_x21(v_snd_2598_);
lean_dec(v_snd_2598_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v___x_2604_);
lean_ctor_set(v___x_2600_, 0, v_r_2603_);
v___x_2606_ = v___x_2600_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_r_2603_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2608_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2606_);
v___x_2608_ = v___x_2595_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2589_);
lean_dec_ref(v_fn_2588_);
return v___x_2592_;
}
}
case 6:
{
lean_object* v___x_2714_; 
lean_inc(v_a_2586_);
lean_inc_ref(v_a_2585_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
v___x_2714_ = lean_apply_11(v_simpBody_2575_, v_e_2576_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, lean_box(0));
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2723_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_a_2715_);
lean_ctor_set(v___x_2719_, 1, v_fType_2572_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2719_);
v___x_2721_ = v___x_2717_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec_ref(v_fType_2572_);
v_a_2724_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2714_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2714_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
default: 
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec_ref(v_e_2576_);
lean_dec_ref(v_simpBody_2575_);
lean_dec_ref(v_fType_2572_);
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2733_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2732_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
return v___x_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2734_, lean_object* v_fnUnivs_2735_, lean_object* v_argUnivs_2736_, lean_object* v_simpBody_2737_, lean_object* v_e_2738_, lean_object* v_i_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2734_, v_fnUnivs_2735_, v_argUnivs_2736_, v_simpBody_2737_, v_e_2738_, v_i_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec(v_i_2739_);
lean_dec_ref(v_argUnivs_2736_);
lean_dec_ref(v_fnUnivs_2735_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2751_, lean_object* v_fType_2752_, lean_object* v_fnUnivs_2753_, lean_object* v_argUnivs_2754_, lean_object* v_simpBody_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_numArgs_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_numArgs_2766_ = lean_array_get_size(v_argUnivs_2754_);
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = lean_nat_sub(v_numArgs_2766_, v___x_2767_);
v___x_2769_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2752_, v_fnUnivs_2753_, v_argUnivs_2754_, v_simpBody_2755_, v_e_2751_, v___x_2768_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v___x_2768_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2778_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_fst_2774_; lean_object* v___x_2776_; 
v_fst_2774_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_fst_2774_);
lean_dec(v_a_2770_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_fst_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_fst_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_a_2779_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2769_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2769_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2787_, lean_object* v_fType_2788_, lean_object* v_fnUnivs_2789_, lean_object* v_argUnivs_2790_, lean_object* v_simpBody_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2787_, v_fType_2788_, v_fnUnivs_2789_, v_argUnivs_2790_, v_simpBody_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_argUnivs_2790_);
lean_dec_ref(v_fnUnivs_2789_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2807_, lean_object* v_simpBody_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___x_2819_; 
lean_inc_ref(v_e_2807_);
v___x_2819_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2807_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v_00_u03b1_2821_; lean_object* v_u_2822_; lean_object* v_e_2823_; lean_object* v_h_2824_; lean_object* v_varDeps_2825_; lean_object* v_fType_2826_; lean_object* v___x_2827_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v_00_u03b1_2821_ = lean_ctor_get(v_a_2820_, 0);
lean_inc_ref(v_00_u03b1_2821_);
v_u_2822_ = lean_ctor_get(v_a_2820_, 1);
lean_inc(v_u_2822_);
v_e_2823_ = lean_ctor_get(v_a_2820_, 2);
lean_inc_ref(v_e_2823_);
v_h_2824_ = lean_ctor_get(v_a_2820_, 3);
lean_inc_ref(v_h_2824_);
v_varDeps_2825_ = lean_ctor_get(v_a_2820_, 4);
lean_inc_ref(v_varDeps_2825_);
v_fType_2826_ = lean_ctor_get(v_a_2820_, 5);
lean_inc_ref_n(v_fType_2826_, 2);
lean_dec(v_a_2820_);
v___x_2827_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2826_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v_argUnivs_2829_; lean_object* v_fnUnivs_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2898_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v_argUnivs_2829_ = lean_ctor_get(v_a_2828_, 0);
v_fnUnivs_2830_ = lean_ctor_get(v_a_2828_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2828_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2832_ = v_a_2828_;
v_isShared_2833_ = v_isSharedCheck_2898_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_fnUnivs_2830_);
lean_inc(v_argUnivs_2829_);
lean_dec(v_a_2828_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2898_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; 
lean_inc_ref(v_e_2823_);
v___x_2834_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2823_, v_fType_2826_, v_fnUnivs_2830_, v_argUnivs_2829_, v_simpBody_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec_ref(v_argUnivs_2829_);
lean_dec_ref(v_fnUnivs_2830_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2889_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2889_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2889_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
if (lean_obj_tag(v_a_2835_) == 0)
{
uint8_t v_contextDependent_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
lean_del_object(v___x_2832_);
lean_dec_ref(v_varDeps_2825_);
lean_dec_ref(v_h_2824_);
lean_dec_ref(v_e_2823_);
lean_dec_ref(v_e_2807_);
v_contextDependent_2839_ = lean_ctor_get_uint8(v_a_2835_, 1);
lean_dec_ref_known(v_a_2835_, 0);
v___x_2840_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2839_);
v___x_2841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v_00_u03b1_2821_);
lean_ctor_set(v___x_2841_, 2, v_u_2822_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2841_);
v___x_2843_ = v___x_2837_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
else
{
lean_object* v_e_x27_2845_; lean_object* v_proof_2846_; uint8_t v_contextDependent_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2888_; 
lean_del_object(v___x_2837_);
v_e_x27_2845_ = lean_ctor_get(v_a_2835_, 0);
v_proof_2846_ = lean_ctor_get(v_a_2835_, 1);
v_contextDependent_2847_ = lean_ctor_get_uint8(v_a_2835_, sizeof(void*)*2 + 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_a_2835_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2849_ = v_a_2835_;
v_isShared_2850_ = v_isSharedCheck_2888_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_proof_2846_);
lean_inc(v_e_x27_2845_);
lean_dec(v_a_2835_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2888_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2852_ = lean_box(0);
lean_inc(v_u_2822_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 1);
lean_ctor_set(v___x_2832_, 1, v___x_2852_);
lean_ctor_set(v___x_2832_, 0, v_u_2822_);
v___x_2854_ = v___x_2832_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_u_2822_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_inc_ref(v___x_2854_);
v___x_2855_ = l_Lean_mkConst(v___x_2851_, v___x_2854_);
lean_inc_ref_n(v_e_x27_2845_, 2);
lean_inc_ref(v_e_2807_);
lean_inc_ref(v_00_u03b1_2821_);
lean_inc_ref(v___x_2855_);
v___x_2856_ = l_Lean_mkApp6(v___x_2855_, v_00_u03b1_2821_, v_e_2807_, v_e_2823_, v_e_x27_2845_, v_h_2824_, v_proof_2846_);
v___x_2857_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2845_, v_varDeps_2825_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2878_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2878_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2878_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2872_; 
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2854_);
v___x_2863_ = l_Lean_mkConst(v___x_2862_, v___x_2854_);
lean_inc_n(v_a_2858_, 2);
lean_inc_ref_n(v_e_x27_2845_, 2);
lean_inc_ref_n(v_00_u03b1_2821_, 3);
v___x_2864_ = l_Lean_mkApp3(v___x_2863_, v_00_u03b1_2821_, v_e_x27_2845_, v_a_2858_);
v___x_2865_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2866_ = l_Lean_mkConst(v___x_2865_, v___x_2854_);
v___x_2867_ = l_Lean_mkAppB(v___x_2866_, v_00_u03b1_2821_, v_e_x27_2845_);
v___x_2868_ = l_Lean_Meta_mkExpectedPropHint(v___x_2867_, v___x_2864_);
v___x_2869_ = l_Lean_mkApp6(v___x_2855_, v_00_u03b1_2821_, v_e_2807_, v_e_x27_2845_, v_a_2858_, v___x_2856_, v___x_2868_);
v___x_2870_ = 0;
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2869_);
lean_ctor_set(v___x_2849_, 0, v_a_2858_);
v___x_2872_ = v___x_2849_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2858_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2869_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*2 + 1, v_contextDependent_2847_);
v___x_2872_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*2, v___x_2870_);
v___x_2873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v_00_u03b1_2821_);
lean_ctor_set(v___x_2873_, 2, v_u_2822_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2873_);
v___x_2875_ = v___x_2860_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_e_x27_2845_);
lean_dec(v_u_2822_);
lean_dec_ref(v_00_u03b1_2821_);
lean_dec_ref(v_e_2807_);
v_a_2879_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2857_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2857_);
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
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_del_object(v___x_2832_);
lean_dec_ref(v_varDeps_2825_);
lean_dec_ref(v_h_2824_);
lean_dec_ref(v_e_2823_);
lean_dec(v_u_2822_);
lean_dec_ref(v_00_u03b1_2821_);
lean_dec_ref(v_e_2807_);
v_a_2890_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2834_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2834_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v_fType_2826_);
lean_dec_ref(v_varDeps_2825_);
lean_dec_ref(v_h_2824_);
lean_dec_ref(v_e_2823_);
lean_dec(v_u_2822_);
lean_dec_ref(v_00_u03b1_2821_);
lean_dec_ref(v_simpBody_2808_);
lean_dec_ref(v_e_2807_);
v_a_2899_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2827_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2827_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref(v_simpBody_2808_);
lean_dec_ref(v_e_2807_);
v_a_2907_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2819_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2819_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2915_, lean_object* v_simpBody_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2915_, v_simpBody_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2928_, lean_object* v_simpBody_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2928_, v_simpBody_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2949_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_result_2945_; lean_object* v___x_2947_; 
v_result_2945_ = lean_ctor_get(v_a_2941_, 0);
lean_inc_ref(v_result_2945_);
lean_dec(v_a_2941_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v_result_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_result_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2940_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2940_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2958_, lean_object* v_simpBody_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2958_, v_simpBody_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2971_, lean_object* v_simpBody_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v___x_2983_; 
lean_inc_ref(v_e_u2081_2971_);
v___x_2983_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2971_, v_simpBody_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v_result_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v_result_2985_ = lean_ctor_get(v_a_2984_, 0);
lean_inc_ref(v_result_2985_);
if (lean_obj_tag(v_result_2985_) == 0)
{
lean_object* v_00_u03b1_2986_; lean_object* v_u_2987_; uint8_t v_contextDependent_2988_; lean_object* v___x_2989_; 
v_00_u03b1_2986_ = lean_ctor_get(v_a_2984_, 1);
lean_inc_ref(v_00_u03b1_2986_);
v_u_2987_ = lean_ctor_get(v_a_2984_, 2);
lean_inc(v_u_2987_);
lean_dec(v_a_2984_);
v_contextDependent_2988_ = lean_ctor_get_uint8(v_result_2985_, 1);
lean_dec_ref_known(v_result_2985_, 0);
lean_inc_ref(v_e_u2081_2971_);
v___x_2989_ = l_Lean_Meta_zetaUnused(v_e_u2081_2971_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3010_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3010_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3010_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
size_t v___x_2994_; size_t v___x_2995_; uint8_t v___x_2996_; 
v___x_2994_ = lean_ptr_addr(v_e_u2081_2971_);
lean_dec_ref(v_e_u2081_2971_);
v___x_2995_ = lean_ptr_addr(v_a_2990_);
v___x_2996_ = lean_usize_dec_eq(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_u_2987_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Lean_mkConst(v___x_2997_, v___x_2999_);
lean_inc(v_a_2990_);
v___x_3001_ = l_Lean_mkAppB(v___x_3000_, v_00_u03b1_2986_, v_a_2990_);
v___x_3002_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3002_, 0, v_a_2990_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*2, v___x_2996_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*2 + 1, v_contextDependent_2988_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_3002_);
v___x_3004_ = v___x_2992_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
lean_dec(v_a_2990_);
lean_dec(v_u_2987_);
lean_dec_ref(v_00_u03b1_2986_);
v___x_3006_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2988_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_3006_);
v___x_3008_ = v___x_2992_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_u_2987_);
lean_dec_ref(v_00_u03b1_2986_);
lean_dec_ref(v_e_u2081_2971_);
v_a_3011_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2989_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2989_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_00_u03b1_3019_; lean_object* v_u_3020_; lean_object* v_e_x27_3021_; lean_object* v_proof_3022_; uint8_t v_contextDependent_3023_; lean_object* v___x_3024_; 
v_00_u03b1_3019_ = lean_ctor_get(v_a_2984_, 1);
lean_inc_ref(v_00_u03b1_3019_);
v_u_3020_ = lean_ctor_get(v_a_2984_, 2);
lean_inc(v_u_3020_);
lean_dec(v_a_2984_);
v_e_x27_3021_ = lean_ctor_get(v_result_2985_, 0);
v_proof_3022_ = lean_ctor_get(v_result_2985_, 1);
v_contextDependent_3023_ = lean_ctor_get_uint8(v_result_2985_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_3021_);
v___x_3024_ = l_Lean_Meta_zetaUnused(v_e_x27_3021_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3055_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3055_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3055_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
size_t v___x_3029_; size_t v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_ptr_addr(v_e_x27_3021_);
v___x_3030_ = lean_ptr_addr(v_a_3025_);
v___x_3031_ = lean_usize_dec_eq(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3049_; 
lean_inc_ref(v_proof_3022_);
lean_inc_ref(v_e_x27_3021_);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_result_2985_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; lean_object* v_unused_3051_; 
v_unused_3050_ = lean_ctor_get(v_result_2985_, 1);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v_result_2985_, 0);
lean_dec(v_unused_3051_);
v___x_3033_ = v_result_2985_;
v_isShared_3034_ = v_isSharedCheck_3049_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v_result_2985_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3049_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3035_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_u_3020_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
lean_inc_ref(v___x_3037_);
v___x_3038_ = l_Lean_mkConst(v___x_3035_, v___x_3037_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3040_ = l_Lean_mkConst(v___x_3039_, v___x_3037_);
lean_inc_n(v_a_3025_, 2);
lean_inc_ref(v_00_u03b1_3019_);
v___x_3041_ = l_Lean_mkAppB(v___x_3040_, v_00_u03b1_3019_, v_a_3025_);
v___x_3042_ = l_Lean_mkApp6(v___x_3038_, v_00_u03b1_3019_, v_e_u2081_2971_, v_e_x27_3021_, v_a_3025_, v_proof_3022_, v___x_3041_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v___x_3042_);
lean_ctor_set(v___x_3033_, 0, v_a_3025_);
v___x_3044_ = v___x_3033_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3025_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, sizeof(void*)*2 + 1, v_contextDependent_3023_);
v___x_3044_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3046_; 
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*2, v___x_3031_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3044_);
v___x_3046_ = v___x_3027_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v___x_3053_; 
lean_dec(v_a_3025_);
lean_dec(v_u_3020_);
lean_dec_ref(v_00_u03b1_3019_);
lean_dec_ref(v_e_u2081_2971_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v_result_2985_);
v___x_3053_ = v___x_3027_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_result_2985_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_u_3020_);
lean_dec_ref(v_00_u03b1_3019_);
lean_dec_ref_known(v_result_2985_, 2);
lean_dec_ref(v_e_u2081_2971_);
v_a_3056_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3024_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3024_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v_e_u2081_2971_);
v_a_3064_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2983_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2983_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_3072_, lean_object* v_simpBody_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_3072_, v_simpBody_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_3085_, lean_object* v_e_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
uint8_t v___x_3097_; 
v___x_3097_ = l_Lean_Expr_letNondep_x21(v_e_3086_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref(v_e_3086_);
lean_dec_ref(v_simpBody_3085_);
v___x_3098_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3098_, 0, v___x_3097_);
lean_ctor_set_uint8(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_3086_, v_simpBody_3085_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_3101_, lean_object* v_e_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_3101_, v_e_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_3127_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_3126_, v_e_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
return v_res_3139_;
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
