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
lean_object* l_Array_instInhabited___redArg();
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0;
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(lean_object* v_k_15_, lean_object* v_t_16_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_15_ = stack[0].m_obj;
lean_object* v_t_16_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_15_, v_t_16_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg___boxed(lean_object* v_k_26_, lean_object* v_t_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_26_, v_t_27_);
lean_dec(v_t_27_);
lean_dec(v_k_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(lean_object* v_fvarIdToPos_30_, lean_object* v_as_31_, size_t v_i_32_, size_t v_stop_33_, lean_object* v_b_34_){
_start:
{
lean_object* v___y_36_; uint8_t v___x_40_; 
v___x_40_ = lean_usize_dec_eq(v_i_32_, v_stop_33_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_array_uget_borrowed(v_as_31_, v_i_32_);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v___x_41_, v_fvarIdToPos_30_);
if (v___x_42_ == 0)
{
v___y_36_ = v_b_34_;
goto v___jp_35_;
}
else
{
lean_object* v___x_43_; 
lean_inc(v___x_41_);
v___x_43_ = lean_array_push(v_b_34_, v___x_41_);
v___y_36_ = v___x_43_;
goto v___jp_35_;
}
}
else
{
return v_b_34_;
}
v___jp_35_:
{
size_t v___x_37_; size_t v___x_38_; 
v___x_37_ = ((size_t)1ULL);
v___x_38_ = lean_usize_add(v_i_32_, v___x_37_);
v_i_32_ = v___x_38_;
v_b_34_ = v___y_36_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIdToPos_30_ = stack[0].m_obj;
lean_object* v_as_31_ = stack[1].m_obj;
size_t v_i_32_ = stack[2].m_num;
size_t v_stop_33_ = stack[3].m_num;
lean_object* v_b_34_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_30_, v_as_31_, v_i_32_, v_stop_33_, v_b_34_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3___boxed(lean_object* v_fvarIdToPos_45_, lean_object* v_as_46_, lean_object* v_i_47_, lean_object* v_stop_48_, lean_object* v_b_49_){
_start:
{
size_t v_i_boxed_50_; size_t v_stop_boxed_51_; lean_object* v_res_52_; 
v_i_boxed_50_ = lean_unbox_usize(v_i_47_);
lean_dec(v_i_47_);
v_stop_boxed_51_ = lean_unbox_usize(v_stop_48_);
lean_dec(v_stop_48_);
v_res_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_45_, v_as_46_, v_i_boxed_50_, v_stop_boxed_51_, v_b_49_);
lean_dec_ref(v_as_46_);
lean_dec(v_fvarIdToPos_45_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object* v_msg_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_panic_fn_borrowed(v___x_54_, v_msg_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_59_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2));
v___x_60_ = lean_unsigned_to_nat(13u);
v___x_61_ = lean_unsigned_to_nat(227u);
v___x_62_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1));
v___x_63_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0));
v___x_64_ = l_mkPanicMessageWithDecl(v___x_63_, v___x_62_, v___x_61_, v___x_60_, v___x_59_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object* v_t_65_, lean_object* v_k_66_){
_start:
{
if (lean_obj_tag(v_t_65_) == 0)
{
lean_object* v_k_67_; lean_object* v_v_68_; lean_object* v_l_69_; lean_object* v_r_70_; uint8_t v___x_71_; 
v_k_67_ = lean_ctor_get(v_t_65_, 1);
v_v_68_ = lean_ctor_get(v_t_65_, 2);
v_l_69_ = lean_ctor_get(v_t_65_, 3);
v_r_70_ = lean_ctor_get(v_t_65_, 4);
v___x_71_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_66_, v_k_67_);
switch(v___x_71_)
{
case 0:
{
v_t_65_ = v_l_69_;
goto _start;
}
case 1:
{
lean_inc(v_v_68_);
return v_v_68_;
}
default: 
{
v_t_65_ = v_r_70_;
goto _start;
}
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3);
v___x_75_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object* v_t_76_, lean_object* v_k_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_t_76_, v_k_77_);
lean_dec(v_k_77_);
lean_dec(v_t_76_);
return v_res_78_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object* v_fvarIdToPos_79_, lean_object* v_fvarId_u2081_80_, lean_object* v_fvarId_u2082_81_){
_start:
{
lean_object* v_pos_u2081_82_; lean_object* v_pos_u2082_83_; uint8_t v___x_84_; 
v_pos_u2081_82_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_79_, v_fvarId_u2081_80_);
v_pos_u2082_83_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_79_, v_fvarId_u2082_81_);
v___x_84_ = lean_nat_dec_lt(v_pos_u2081_82_, v_pos_u2082_83_);
lean_dec(v_pos_u2082_83_);
lean_dec(v_pos_u2081_82_);
return v___x_84_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIdToPos_79_ = stack[0].m_obj;
lean_object* v_fvarId_u2081_80_ = stack[1].m_obj;
lean_object* v_fvarId_u2082_81_ = stack[2].m_obj;
uint8_t v_res_85_;
v_res_85_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_79_, v_fvarId_u2081_80_, v_fvarId_u2082_81_);
stack->m_num = v_res_85_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object* v_fvarIdToPos_86_, lean_object* v_fvarId_u2081_87_, lean_object* v_fvarId_u2082_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_86_, v_fvarId_u2081_87_, v_fvarId_u2082_88_);
lean_dec(v_fvarId_u2082_88_);
lean_dec(v_fvarId_u2081_87_);
lean_dec(v_fvarIdToPos_86_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(lean_object* v_fvarIdToPos_91_, lean_object* v_hi_92_, lean_object* v_pivot_93_, lean_object* v_as_94_, lean_object* v_i_95_, lean_object* v_k_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_lt(v_k_96_, v_hi_92_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_k_96_);
v___x_98_ = lean_array_fswap(v_as_94_, v_i_95_, v_hi_92_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v_i_95_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v_pos_u2081_101_; lean_object* v_pos_u2082_102_; uint8_t v___x_103_; 
v___x_100_ = lean_array_fget_borrowed(v_as_94_, v_k_96_);
v_pos_u2081_101_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_91_, v___x_100_);
v_pos_u2082_102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_91_, v_pivot_93_);
v___x_103_ = lean_nat_dec_lt(v_pos_u2081_101_, v_pos_u2082_102_);
lean_dec(v_pos_u2082_102_);
lean_dec(v_pos_u2081_101_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_k_96_, v___x_104_);
lean_dec(v_k_96_);
v_k_96_ = v___x_105_;
goto _start;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_array_fswap(v_as_94_, v_i_95_, v_k_96_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_i_95_, v___x_108_);
lean_dec(v_i_95_);
v___x_110_ = lean_nat_add(v_k_96_, v___x_108_);
lean_dec(v_k_96_);
v_as_94_ = v___x_107_;
v_i_95_ = v___x_109_;
v_k_96_ = v___x_110_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg___boxed(lean_object* v_fvarIdToPos_112_, lean_object* v_hi_113_, lean_object* v_pivot_114_, lean_object* v_as_115_, lean_object* v_i_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_112_, v_hi_113_, v_pivot_114_, v_as_115_, v_i_116_, v_k_117_);
lean_dec(v_pivot_114_);
lean_dec(v_hi_113_);
lean_dec(v_fvarIdToPos_112_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object* v_fvarIdToPos_119_, lean_object* v_n_120_, lean_object* v_as_121_, lean_object* v_lo_122_, lean_object* v_hi_123_){
_start:
{
lean_object* v___y_125_; uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_lt(v_lo_122_, v_hi_123_);
if (v___x_135_ == 0)
{
lean_dec(v_lo_122_);
return v_as_121_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_mid_138_; lean_object* v___y_140_; lean_object* v___y_146_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_136_ = lean_nat_add(v_lo_122_, v_hi_123_);
v___x_137_ = lean_unsigned_to_nat(1u);
v_mid_138_ = lean_nat_shiftr(v___x_136_, v___x_137_);
lean_dec(v___x_136_);
v___x_151_ = lean_array_fget_borrowed(v_as_121_, v_mid_138_);
v___x_152_ = lean_array_fget_borrowed(v_as_121_, v_lo_122_);
v___x_153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_119_, v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
v___y_146_ = v_as_121_;
goto v___jp_145_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_array_fswap(v_as_121_, v_lo_122_, v_mid_138_);
v___y_146_ = v___x_154_;
goto v___jp_145_;
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_array_fget_borrowed(v___y_140_, v_mid_138_);
v___x_142_ = lean_array_fget_borrowed(v___y_140_, v_hi_123_);
v___x_143_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_119_, v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_mid_138_);
v___y_125_ = v___y_140_;
goto v___jp_124_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_array_fswap(v___y_140_, v_mid_138_, v_hi_123_);
lean_dec(v_mid_138_);
v___y_125_ = v___x_144_;
goto v___jp_124_;
}
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_array_fget_borrowed(v___y_146_, v_hi_123_);
v___x_148_ = lean_array_fget_borrowed(v___y_146_, v_lo_122_);
v___x_149_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_119_, v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
v___y_140_ = v___y_146_;
goto v___jp_139_;
}
else
{
lean_object* v___x_150_; 
v___x_150_ = lean_array_fswap(v___y_146_, v_lo_122_, v_hi_123_);
v___y_140_ = v___x_150_;
goto v___jp_139_;
}
}
}
v___jp_124_:
{
lean_object* v_pivot_126_; lean_object* v___x_127_; lean_object* v_fst_128_; lean_object* v_snd_129_; uint8_t v___x_130_; 
v_pivot_126_ = lean_array_fget(v___y_125_, v_hi_123_);
lean_inc_n(v_lo_122_, 2);
v___x_127_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_119_, v_hi_123_, v_pivot_126_, v___y_125_, v_lo_122_, v_lo_122_);
lean_dec(v_pivot_126_);
v_fst_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_fst_128_);
v_snd_129_ = lean_ctor_get(v___x_127_, 1);
lean_inc(v_snd_129_);
lean_dec_ref(v___x_127_);
v___x_130_ = lean_nat_dec_le(v_hi_123_, v_fst_128_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_119_, v_n_120_, v_snd_129_, v_lo_122_, v_fst_128_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_fst_128_, v___x_132_);
lean_dec(v_fst_128_);
v_as_121_ = v___x_131_;
v_lo_122_ = v___x_133_;
goto _start;
}
else
{
lean_dec(v_fst_128_);
lean_dec(v_lo_122_);
return v_snd_129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object* v_fvarIdToPos_155_, lean_object* v_n_156_, lean_object* v_as_157_, lean_object* v_lo_158_, lean_object* v_hi_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_155_, v_n_156_, v_as_157_, v_lo_158_, v_hi_159_);
lean_dec(v_hi_159_);
lean_dec(v_n_156_);
lean_dec(v_fvarIdToPos_155_);
return v_res_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_unsigned_to_nat(16u);
v___x_163_ = lean_mk_array(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_170_ = lean_box(1);
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_173_, lean_object* v_fvarIdToPos_174_){
_start:
{
lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___x_183_; lean_object* v___y_185_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_s_193_; lean_object* v_fvarIds_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_192_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3);
v_s_193_ = l_Lean_collectFVars(v___x_192_, v_e_173_);
v_fvarIds_194_ = lean_ctor_get(v_s_193_, 2);
lean_inc_ref(v_fvarIds_194_);
lean_dec_ref(v_s_193_);
v___x_195_ = lean_array_get_size(v_fvarIds_194_);
v___x_196_ = lean_nat_dec_lt(v___x_183_, v___x_195_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_fvarIds_194_);
v___y_185_ = v___x_191_;
goto v___jp_184_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = lean_nat_dec_le(v___x_195_, v___x_195_);
if (v___x_197_ == 0)
{
if (v___x_196_ == 0)
{
lean_dec_ref(v_fvarIds_194_);
v___y_185_ = v___x_191_;
goto v___jp_184_;
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_195_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_174_, v_fvarIds_194_, v___x_198_, v___x_199_, v___x_191_);
lean_dec_ref(v_fvarIds_194_);
v___y_185_ = v___x_200_;
goto v___jp_184_;
}
}
else
{
size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((size_t)0ULL);
v___x_202_ = lean_usize_of_nat(v___x_195_);
v___x_203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_174_, v_fvarIds_194_, v___x_201_, v___x_202_, v___x_191_);
lean_dec_ref(v_fvarIds_194_);
v___y_185_ = v___x_203_;
goto v___jp_184_;
}
}
v___jp_175_:
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_le(v___y_179_, v___y_176_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec(v___y_176_);
lean_inc(v___y_179_);
v___x_181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_174_, v___y_177_, v___y_178_, v___y_179_, v___y_179_);
lean_dec(v___y_179_);
lean_dec(v___y_177_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_174_, v___y_177_, v___y_178_, v___y_179_, v___y_176_);
lean_dec(v___y_176_);
lean_dec(v___y_177_);
return v___x_182_;
}
}
v___jp_184_:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_array_get_size(v___y_185_);
v___x_187_ = lean_nat_dec_eq(v___x_186_, v___x_183_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_sub(v___x_186_, v___x_188_);
v___x_190_ = lean_nat_dec_le(v___x_183_, v___x_189_);
if (v___x_190_ == 0)
{
lean_inc(v___x_189_);
v___y_176_ = v___x_189_;
v___y_177_ = v___x_186_;
v___y_178_ = v___y_185_;
v___y_179_ = v___x_189_;
goto v___jp_175_;
}
else
{
v___y_176_ = v___x_189_;
v___y_177_ = v___x_186_;
v___y_178_ = v___y_185_;
v___y_179_ = v___x_183_;
goto v___jp_175_;
}
}
else
{
return v___y_185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(lean_object* v_e_204_, lean_object* v_fvarIdToPos_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_e_204_, v_fvarIdToPos_205_);
lean_dec(v_fvarIdToPos_205_);
return v_res_206_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_207_, lean_object* v_k_208_, lean_object* v_t_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_208_, v_t_209_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_208_ = stack[1].m_obj;
lean_object* v_t_209_ = stack[2].m_obj;
uint8_t v_res_211_;
v_res_211_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_box(0), v_k_208_, v_t_209_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_212_, lean_object* v_k_213_, lean_object* v_t_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_212_, v_k_213_, v_t_214_);
lean_dec(v_t_214_);
lean_dec(v_k_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_217_, lean_object* v_n_218_, lean_object* v_as_219_, lean_object* v_lo_220_, lean_object* v_hi_221_, lean_object* v_w_222_, lean_object* v_hlo_223_, lean_object* v_hhi_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_217_, v_n_218_, v_as_219_, v_lo_220_, v_hi_221_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_226_, lean_object* v_n_227_, lean_object* v_as_228_, lean_object* v_lo_229_, lean_object* v_hi_230_, lean_object* v_w_231_, lean_object* v_hlo_232_, lean_object* v_hhi_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_226_, v_n_227_, v_as_228_, v_lo_229_, v_hi_230_, v_w_231_, v_hlo_232_, v_hhi_233_);
lean_dec(v_hi_230_);
lean_dec(v_n_227_);
lean_dec(v_fvarIdToPos_226_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(lean_object* v_fvarIdToPos_235_, lean_object* v_n_236_, lean_object* v_lo_237_, lean_object* v_hi_238_, lean_object* v_hhi_239_, lean_object* v_pivot_240_, lean_object* v_as_241_, lean_object* v_i_242_, lean_object* v_k_243_, lean_object* v_ilo_244_, lean_object* v_ik_245_, lean_object* v_w_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_235_, v_hi_238_, v_pivot_240_, v_as_241_, v_i_242_, v_k_243_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(lean_object* v_fvarIdToPos_248_, lean_object* v_n_249_, lean_object* v_lo_250_, lean_object* v_hi_251_, lean_object* v_hhi_252_, lean_object* v_pivot_253_, lean_object* v_as_254_, lean_object* v_i_255_, lean_object* v_k_256_, lean_object* v_ilo_257_, lean_object* v_ik_258_, lean_object* v_w_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(v_fvarIdToPos_248_, v_n_249_, v_lo_250_, v_hi_251_, v_hhi_252_, v_pivot_253_, v_as_254_, v_i_255_, v_k_256_, v_ilo_257_, v_ik_258_, v_w_259_);
lean_dec(v_pivot_253_);
lean_dec(v_hi_251_);
lean_dec(v_lo_250_);
lean_dec(v_n_249_);
lean_dec(v_fvarIdToPos_248_);
return v_res_260_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_261_, uint8_t v_bi_262_, lean_object* v_t_263_, lean_object* v_b_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___y_273_; lean_object* v___x_276_; uint8_t v_debug_277_; 
v___x_276_ = lean_st_ref_get(v___y_266_);
v_debug_277_ = lean_ctor_get_uint8(v___x_276_, sizeof(void*)*12);
lean_dec(v___x_276_);
if (v_debug_277_ == 0)
{
v___y_273_ = v___y_266_;
goto v___jp_272_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_263_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_dec_ref_known(v___x_279_, 1);
v___y_273_ = v___y_266_;
goto v___jp_272_;
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v_b_264_);
lean_dec_ref(v_t_263_);
lean_dec(v_x_261_);
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_b_264_);
lean_dec_ref(v_t_263_);
lean_dec(v_x_261_);
v_a_288_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_278_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_278_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_Lean_Expr_forallE___override(v_x_261_, v_t_263_, v_b_264_, v_bi_262_);
v___x_275_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_274_, v___y_273_);
return v___x_275_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_261_ = stack[0].m_obj;
uint8_t v_bi_262_ = stack[1].m_num;
lean_object* v_t_263_ = stack[2].m_obj;
lean_object* v_b_264_ = stack[3].m_obj;
lean_object* v___y_265_ = stack[4].m_obj;
lean_object* v___y_266_ = stack[5].m_obj;
lean_object* v___y_267_ = stack[6].m_obj;
lean_object* v___y_268_ = stack[7].m_obj;
lean_object* v___y_269_ = stack[8].m_obj;
lean_object* v___y_270_ = stack[9].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_261_, v_bi_262_, v_t_263_, v_b_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_297_, lean_object* v_bi_298_, lean_object* v_t_299_, lean_object* v_b_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
uint8_t v_bi_boxed_308_; lean_object* v_res_309_; 
v_bi_boxed_308_ = lean_unbox(v_bi_298_);
v_res_309_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_297_, v_bi_boxed_308_, v_t_299_, v_b_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_309_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_313_, lean_object* v_i_314_, lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_zero_323_; uint8_t v_isZero_324_; 
v_zero_323_ = lean_unsigned_to_nat(0u);
v_isZero_324_ = lean_nat_dec_eq(v_i_314_, v_zero_323_);
if (v_isZero_324_ == 1)
{
lean_object* v___x_325_; 
lean_dec(v_i_314_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_00_u03b2_315_);
return v___x_325_;
}
else
{
lean_object* v_one_326_; lean_object* v_n_327_; lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_one_326_ = lean_unsigned_to_nat(1u);
v_n_327_ = lean_nat_sub(v_i_314_, v_one_326_);
lean_dec(v_i_314_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_329_ = 0;
v___x_330_ = lean_array_fget_borrowed(v_00_u03b1s_313_, v_n_327_);
lean_inc(v___x_330_);
v___x_331_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_328_, v___x_329_, v___x_330_, v_00_u03b2_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v_i_314_ = v_n_327_;
v_00_u03b2_315_ = v_a_332_;
goto _start;
}
else
{
lean_dec(v_n_327_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1s_313_ = stack[0].m_obj;
lean_object* v_i_314_ = stack[1].m_obj;
lean_object* v_00_u03b2_315_ = stack[2].m_obj;
lean_object* v_a_316_ = stack[3].m_obj;
lean_object* v_a_317_ = stack[4].m_obj;
lean_object* v_a_318_ = stack[5].m_obj;
lean_object* v_a_319_ = stack[6].m_obj;
lean_object* v_a_320_ = stack[7].m_obj;
lean_object* v_a_321_ = stack[8].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_313_, v_i_314_, v_00_u03b2_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_335_, lean_object* v_i_336_, lean_object* v_00_u03b2_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_335_, v_i_336_, v_00_u03b2_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec_ref(v_00_u03b1s_335_);
return v_res_345_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_346_, lean_object* v_i_347_, lean_object* v_00_u03b2_348_, lean_object* v_h_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_346_, v_i_347_, v_00_u03b2_348_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1s_346_ = stack[0].m_obj;
lean_object* v_i_347_ = stack[1].m_obj;
lean_object* v_00_u03b2_348_ = stack[2].m_obj;
lean_object* v_a_350_ = stack[4].m_obj;
lean_object* v_a_351_ = stack[5].m_obj;
lean_object* v_a_352_ = stack[6].m_obj;
lean_object* v_a_353_ = stack[7].m_obj;
lean_object* v_a_354_ = stack[8].m_obj;
lean_object* v_a_355_ = stack[9].m_obj;
lean_object* v_res_358_;
v_res_358_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_346_, v_i_347_, v_00_u03b2_348_, lean_box(0), v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_359_, lean_object* v_i_360_, lean_object* v_00_u03b2_361_, lean_object* v_h_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_359_, v_i_360_, v_00_u03b2_361_, v_h_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec_ref(v_00_u03b1s_359_);
return v_res_370_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_371_, lean_object* v_00_u03b2_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_array_get_size(v_00_u03b1s_371_);
v___x_381_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_371_, v___x_380_, v_00_u03b2_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
return v___x_381_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1s_371_ = stack[0].m_obj;
lean_object* v_00_u03b2_372_ = stack[1].m_obj;
lean_object* v_a_373_ = stack[2].m_obj;
lean_object* v_a_374_ = stack[3].m_obj;
lean_object* v_a_375_ = stack[4].m_obj;
lean_object* v_a_376_ = stack[5].m_obj;
lean_object* v_a_377_ = stack[6].m_obj;
lean_object* v_a_378_ = stack[7].m_obj;
lean_object* v_res_382_;
v_res_382_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_371_, v_00_u03b2_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_383_, lean_object* v_00_u03b2_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_383_, v_00_u03b2_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_00_u03b1s_383_);
return v_res_392_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_393_, lean_object* v_subst_394_, size_t v_sz_395_, size_t v_i_396_, lean_object* v_bs_397_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_lt(v_i_396_, v_sz_395_);
if (v___x_398_ == 0)
{
return v_bs_397_;
}
else
{
lean_object* v___x_399_; lean_object* v_v_400_; lean_object* v___x_401_; lean_object* v_bs_x27_402_; lean_object* v___x_403_; lean_object* v___x_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v___x_399_ = l_Lean_instInhabitedExpr;
v_v_400_ = lean_array_uget(v_bs_397_, v_i_396_);
v___x_401_ = lean_unsigned_to_nat(0u);
v_bs_x27_402_ = lean_array_uset(v_bs_397_, v_i_396_, v___x_401_);
v___x_403_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_393_, v_v_400_);
lean_dec(v_v_400_);
v___x_404_ = lean_array_get_borrowed(v___x_399_, v_subst_394_, v___x_403_);
lean_dec(v___x_403_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_396_, v___x_405_);
lean_inc(v___x_404_);
v___x_407_ = lean_array_uset(v_bs_x27_402_, v_i_396_, v___x_404_);
v_i_396_ = v___x_406_;
v_bs_397_ = v___x_407_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIdToPos_393_ = stack[0].m_obj;
lean_object* v_subst_394_ = stack[1].m_obj;
size_t v_sz_395_ = stack[2].m_num;
size_t v_i_396_ = stack[3].m_num;
lean_object* v_bs_397_ = stack[4].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_393_, v_subst_394_, v_sz_395_, v_i_396_, v_bs_397_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_410_, lean_object* v_subst_411_, lean_object* v_sz_412_, lean_object* v_i_413_, lean_object* v_bs_414_){
_start:
{
size_t v_sz_boxed_415_; size_t v_i_boxed_416_; lean_object* v_res_417_; 
v_sz_boxed_415_ = lean_unbox_usize(v_sz_412_);
lean_dec(v_sz_412_);
v_i_boxed_416_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_res_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_410_, v_subst_411_, v_sz_boxed_415_, v_i_boxed_416_, v_bs_414_);
lean_dec_ref(v_subst_411_);
lean_dec(v_fvarIdToPos_410_);
return v_res_417_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_418_, size_t v_i_419_, lean_object* v_bs_420_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_419_, v_sz_418_);
if (v___x_421_ == 0)
{
return v_bs_420_;
}
else
{
lean_object* v_v_422_; lean_object* v___x_423_; lean_object* v_bs_x27_424_; lean_object* v___x_425_; size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v_v_422_ = lean_array_uget(v_bs_420_, v_i_419_);
v___x_423_ = lean_unsigned_to_nat(0u);
v_bs_x27_424_ = lean_array_uset(v_bs_420_, v_i_419_, v___x_423_);
v___x_425_ = l_Lean_mkFVar(v_v_422_);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_419_, v___x_426_);
v___x_428_ = lean_array_uset(v_bs_x27_424_, v_i_419_, v___x_425_);
v_i_419_ = v___x_427_;
v_bs_420_ = v___x_428_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_418_ = stack[0].m_num;
size_t v_i_419_ = stack[1].m_num;
lean_object* v_bs_420_ = stack[2].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_418_, v_i_419_, v_bs_420_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_431_, lean_object* v_i_432_, lean_object* v_bs_433_){
_start:
{
size_t v_sz_boxed_434_; size_t v_i_boxed_435_; lean_object* v_res_436_; 
v_sz_boxed_434_ = lean_unbox_usize(v_sz_431_);
lean_dec(v_sz_431_);
v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_434_, v_i_boxed_435_, v_bs_433_);
return v_res_436_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
v___x_446_ = lean_apply_8(v_k_437_, v_b_440_, v___y_438_, v___y_439_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, lean_box(0));
return v___x_446_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_437_ = stack[0].m_obj;
lean_object* v___y_438_ = stack[1].m_obj;
lean_object* v___y_439_ = stack[2].m_obj;
lean_object* v_b_440_ = stack[3].m_obj;
lean_object* v___y_441_ = stack[4].m_obj;
lean_object* v___y_442_ = stack[5].m_obj;
lean_object* v___y_443_ = stack[6].m_obj;
lean_object* v___y_444_ = stack[7].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_437_, v___y_438_, v___y_439_, v_b_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v_b_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_448_, v___y_449_, v___y_450_, v_b_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_457_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_458_, uint8_t v_bi_459_, lean_object* v_type_460_, lean_object* v_k_461_, uint8_t v_kind_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; 
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_470_, 0, v_k_461_);
lean_closure_set(v___f_470_, 1, v___y_463_);
lean_closure_set(v___f_470_, 2, v___y_464_);
v___x_471_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_458_, v_bi_459_, v_type_460_, v___f_470_, v_kind_462_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_471_) == 0)
{
return v___x_471_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
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
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_458_ = stack[0].m_obj;
uint8_t v_bi_459_ = stack[1].m_num;
lean_object* v_type_460_ = stack[2].m_obj;
lean_object* v_k_461_ = stack[3].m_obj;
uint8_t v_kind_462_ = stack[4].m_num;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v___y_464_ = stack[6].m_obj;
lean_object* v___y_465_ = stack[7].m_obj;
lean_object* v___y_466_ = stack[8].m_obj;
lean_object* v___y_467_ = stack[9].m_obj;
lean_object* v___y_468_ = stack[10].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_458_, v_bi_459_, v_type_460_, v_k_461_, v_kind_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_481_, lean_object* v_bi_482_, lean_object* v_type_483_, lean_object* v_k_484_, lean_object* v_kind_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v_bi_boxed_493_; uint8_t v_kind_boxed_494_; lean_object* v_res_495_; 
v_bi_boxed_493_ = lean_unbox(v_bi_482_);
v_kind_boxed_494_ = lean_unbox(v_kind_485_);
v_res_495_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_481_, v_bi_boxed_493_, v_type_483_, v_k_484_, v_kind_boxed_494_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_495_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_496_, lean_object* v_type_497_, lean_object* v_k_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = 0;
v___x_507_ = 0;
v___x_508_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_496_, v___x_506_, v_type_497_, v_k_498_, v___x_507_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_508_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_496_ = stack[0].m_obj;
lean_object* v_type_497_ = stack[1].m_obj;
lean_object* v_k_498_ = stack[2].m_obj;
lean_object* v___y_499_ = stack[3].m_obj;
lean_object* v___y_500_ = stack[4].m_obj;
lean_object* v___y_501_ = stack[5].m_obj;
lean_object* v___y_502_ = stack[6].m_obj;
lean_object* v___y_503_ = stack[7].m_obj;
lean_object* v___y_504_ = stack[8].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_496_, v_type_497_, v_k_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_510_, lean_object* v_type_511_, lean_object* v_k_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_510_, v_type_511_, v_k_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_521_, lean_object* v_k_522_, lean_object* v_fallback_523_){
_start:
{
if (lean_obj_tag(v_t_521_) == 0)
{
lean_object* v_k_524_; lean_object* v_v_525_; lean_object* v_l_526_; lean_object* v_r_527_; uint8_t v___x_528_; 
v_k_524_ = lean_ctor_get(v_t_521_, 1);
v_v_525_ = lean_ctor_get(v_t_521_, 2);
v_l_526_ = lean_ctor_get(v_t_521_, 3);
v_r_527_ = lean_ctor_get(v_t_521_, 4);
v___x_528_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_522_, v_k_524_);
switch(v___x_528_)
{
case 0:
{
v_t_521_ = v_l_526_;
goto _start;
}
case 1:
{
lean_inc(v_v_525_);
return v_v_525_;
}
default: 
{
v_t_521_ = v_r_527_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_523_);
return v_fallback_523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_531_, lean_object* v_k_532_, lean_object* v_fallback_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_531_, v_k_532_, v_fallback_533_);
lean_dec(v_fallback_533_);
lean_dec(v_k_532_);
lean_dec(v_t_531_);
return v_res_534_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_535_, size_t v_sz_536_, size_t v_i_537_, lean_object* v_bs_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_539_ == 0)
{
return v_bs_538_;
}
else
{
lean_object* v_v_540_; lean_object* v___x_541_; lean_object* v_bs_x27_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_v_540_ = lean_array_uget(v_bs_538_, v_i_537_);
v___x_541_ = lean_unsigned_to_nat(0u);
v_bs_x27_542_ = lean_array_uset(v_bs_538_, v_i_537_, v___x_541_);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_535_, v_v_540_, v___x_541_);
lean_dec(v_v_540_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v___x_546_ = lean_array_uset(v_bs_x27_542_, v_i_537_, v___x_543_);
v_i_537_ = v___x_545_;
v_bs_538_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIdToPos_535_ = stack[0].m_obj;
size_t v_sz_536_ = stack[1].m_num;
size_t v_i_537_ = stack[2].m_num;
lean_object* v_bs_538_ = stack[3].m_obj;
lean_object* v_res_548_;
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_535_, v_sz_536_, v_i_537_, v_bs_538_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_549_, lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_549_, v_sz_boxed_553_, v_i_boxed_554_, v_bs_552_);
lean_dec(v_fvarIdToPos_549_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_565_ = _args[0];
lean_object* v_subst_566_ = _args[1];
lean_object* v_sz_567_ = _args[2];
lean_object* v___x_568_ = _args[3];
lean_object* v_fvarIds_569_ = _args[4];
lean_object* v_x_570_ = _args[5];
lean_object* v_xs_571_ = _args[6];
lean_object* v_xs_x27_572_ = _args[7];
lean_object* v_args_573_ = _args[8];
lean_object* v_a_574_ = _args[9];
lean_object* v_types_575_ = _args[10];
lean_object* v_a_576_ = _args[11];
lean_object* v_varDeps_577_ = _args[12];
lean_object* v_varPos_578_ = _args[13];
lean_object* v_haveExpr_579_ = _args[14];
lean_object* v_body_580_ = _args[15];
lean_object* v_x_x27_581_ = _args[16];
lean_object* v___y_582_ = _args[17];
lean_object* v___y_583_ = _args[18];
lean_object* v___y_584_ = _args[19];
lean_object* v___y_585_ = _args[20];
lean_object* v___y_586_ = _args[21];
lean_object* v___y_587_ = _args[22];
lean_object* v___y_588_ = _args[23];
_start:
{
size_t v_sz_boxed_589_; size_t v___x_6493__boxed_590_; lean_object* v_res_591_; 
v_sz_boxed_589_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v___x_6493__boxed_590_ = lean_unbox_usize(v___x_568_);
lean_dec(v___x_568_);
v_res_591_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_565_, v_subst_566_, v_sz_boxed_589_, v___x_6493__boxed_590_, v_fvarIds_569_, v_x_570_, v_xs_571_, v_xs_x27_572_, v_args_573_, v_a_574_, v_types_575_, v_a_576_, v_varDeps_577_, v_varPos_578_, v_haveExpr_579_, v_body_580_, v_x_x27_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_591_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_v_592_, lean_object* v_fvarIdToPos_593_, uint8_t v_nondep_594_, lean_object* v_t_595_, lean_object* v_subst_596_, lean_object* v_xs_597_, lean_object* v_xs_x27_598_, lean_object* v_args_599_, lean_object* v_types_600_, lean_object* v_varDeps_601_, lean_object* v_haveExpr_602_, lean_object* v_body_603_, lean_object* v_declName_604_, lean_object* v_x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_fvarIds_613_; size_t v_sz_614_; size_t v___x_615_; lean_object* v_varPos_616_; lean_object* v_ys_617_; uint8_t v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; 
lean_inc_ref(v_v_592_);
v_fvarIds_613_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_592_, v_fvarIdToPos_593_);
v_sz_614_ = lean_array_size(v_fvarIds_613_);
v___x_615_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_613_, 2);
v_varPos_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_593_, v_sz_614_, v___x_615_, v_fvarIds_613_);
v_ys_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_614_, v___x_615_, v_fvarIds_613_);
v___x_618_ = 0;
v___x_619_ = 1;
v___x_620_ = l_Lean_Meta_mkLambdaFVars(v_ys_617_, v_v_592_, v___x_618_, v_nondep_594_, v___x_618_, v_nondep_594_, v___x_619_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = l_Lean_Meta_mkForallFVars(v_ys_617_, v_t_595_, v___x_618_, v_nondep_594_, v_nondep_594_, v___x_619_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec_ref(v_ys_617_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = l_Lean_Meta_Sym_shareCommonInc(v_a_623_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___x_629_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc_n(v_a_625_, 2);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_box_usize(v_sz_614_);
v___x_627_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_628_, 0, v_fvarIdToPos_593_);
lean_closure_set(v___f_628_, 1, v_subst_596_);
lean_closure_set(v___f_628_, 2, v___x_626_);
lean_closure_set(v___f_628_, 3, v___x_627_);
lean_closure_set(v___f_628_, 4, v_fvarIds_613_);
lean_closure_set(v___f_628_, 5, v_x_605_);
lean_closure_set(v___f_628_, 6, v_xs_597_);
lean_closure_set(v___f_628_, 7, v_xs_x27_598_);
lean_closure_set(v___f_628_, 8, v_args_599_);
lean_closure_set(v___f_628_, 9, v_a_621_);
lean_closure_set(v___f_628_, 10, v_types_600_);
lean_closure_set(v___f_628_, 11, v_a_625_);
lean_closure_set(v___f_628_, 12, v_varDeps_601_);
lean_closure_set(v___f_628_, 13, v_varPos_616_);
lean_closure_set(v___f_628_, 14, v_haveExpr_602_);
lean_closure_set(v___f_628_, 15, v_body_603_);
v___x_629_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_604_, v_a_625_, v___f_628_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v___x_629_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_621_);
lean_dec_ref(v_varPos_616_);
lean_dec_ref(v_fvarIds_613_);
lean_dec_ref(v_x_605_);
lean_dec(v_declName_604_);
lean_dec_ref(v_body_603_);
lean_dec_ref(v_haveExpr_602_);
lean_dec_ref(v_varDeps_601_);
lean_dec_ref(v_types_600_);
lean_dec_ref(v_args_599_);
lean_dec_ref(v_xs_x27_598_);
lean_dec_ref(v_xs_597_);
lean_dec_ref(v_subst_596_);
lean_dec(v_fvarIdToPos_593_);
v_a_630_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_624_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_624_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_a_621_);
lean_dec_ref(v_varPos_616_);
lean_dec_ref(v_fvarIds_613_);
lean_dec_ref(v_x_605_);
lean_dec(v_declName_604_);
lean_dec_ref(v_body_603_);
lean_dec_ref(v_haveExpr_602_);
lean_dec_ref(v_varDeps_601_);
lean_dec_ref(v_types_600_);
lean_dec_ref(v_args_599_);
lean_dec_ref(v_xs_x27_598_);
lean_dec_ref(v_xs_597_);
lean_dec_ref(v_subst_596_);
lean_dec(v_fvarIdToPos_593_);
v_a_638_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_622_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_622_);
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
lean_dec_ref(v_ys_617_);
lean_dec_ref(v_varPos_616_);
lean_dec_ref(v_fvarIds_613_);
lean_dec_ref(v_x_605_);
lean_dec(v_declName_604_);
lean_dec_ref(v_body_603_);
lean_dec_ref(v_haveExpr_602_);
lean_dec_ref(v_varDeps_601_);
lean_dec_ref(v_types_600_);
lean_dec_ref(v_args_599_);
lean_dec_ref(v_xs_x27_598_);
lean_dec_ref(v_xs_597_);
lean_dec_ref(v_subst_596_);
lean_dec_ref(v_t_595_);
lean_dec(v_fvarIdToPos_593_);
v_a_646_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_620_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_620_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_592_ = stack[0].m_obj;
lean_object* v_fvarIdToPos_593_ = stack[1].m_obj;
uint8_t v_nondep_594_ = stack[2].m_num;
lean_object* v_t_595_ = stack[3].m_obj;
lean_object* v_subst_596_ = stack[4].m_obj;
lean_object* v_xs_597_ = stack[5].m_obj;
lean_object* v_xs_x27_598_ = stack[6].m_obj;
lean_object* v_args_599_ = stack[7].m_obj;
lean_object* v_types_600_ = stack[8].m_obj;
lean_object* v_varDeps_601_ = stack[9].m_obj;
lean_object* v_haveExpr_602_ = stack[10].m_obj;
lean_object* v_body_603_ = stack[11].m_obj;
lean_object* v_declName_604_ = stack[12].m_obj;
lean_object* v_x_605_ = stack[13].m_obj;
lean_object* v___y_606_ = stack[14].m_obj;
lean_object* v___y_607_ = stack[15].m_obj;
lean_object* v___y_608_ = stack[16].m_obj;
lean_object* v___y_609_ = stack[17].m_obj;
lean_object* v___y_610_ = stack[18].m_obj;
lean_object* v___y_611_ = stack[19].m_obj;
lean_object* v_res_654_;
v_res_654_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_v_592_, v_fvarIdToPos_593_, v_nondep_594_, v_t_595_, v_subst_596_, v_xs_597_, v_xs_x27_598_, v_args_599_, v_types_600_, v_varDeps_601_, v_haveExpr_602_, v_body_603_, v_declName_604_, v_x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
stack->m_obj
 = v_res_654_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_v_655_ = _args[0];
lean_object* v_fvarIdToPos_656_ = _args[1];
lean_object* v_nondep_657_ = _args[2];
lean_object* v_t_658_ = _args[3];
lean_object* v_subst_659_ = _args[4];
lean_object* v_xs_660_ = _args[5];
lean_object* v_xs_x27_661_ = _args[6];
lean_object* v_args_662_ = _args[7];
lean_object* v_types_663_ = _args[8];
lean_object* v_varDeps_664_ = _args[9];
lean_object* v_haveExpr_665_ = _args[10];
lean_object* v_body_666_ = _args[11];
lean_object* v_declName_667_ = _args[12];
lean_object* v_x_668_ = _args[13];
lean_object* v___y_669_ = _args[14];
lean_object* v___y_670_ = _args[15];
lean_object* v___y_671_ = _args[16];
lean_object* v___y_672_ = _args[17];
lean_object* v___y_673_ = _args[18];
lean_object* v___y_674_ = _args[19];
lean_object* v___y_675_ = _args[20];
_start:
{
uint8_t v_nondep_6520__boxed_676_; lean_object* v_res_677_; 
v_nondep_6520__boxed_676_ = lean_unbox(v_nondep_657_);
v_res_677_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_v_655_, v_fvarIdToPos_656_, v_nondep_6520__boxed_676_, v_t_658_, v_subst_659_, v_xs_660_, v_xs_x27_661_, v_args_662_, v_types_663_, v_varDeps_664_, v_haveExpr_665_, v_body_666_, v_declName_667_, v_x_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_677_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_678_, lean_object* v_e_679_, lean_object* v_xs_680_, lean_object* v_xs_x27_681_, lean_object* v_args_682_, lean_object* v_subst_683_, lean_object* v_types_684_, lean_object* v_varDeps_685_, lean_object* v_fvarIdToPos_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; 
if (lean_obj_tag(v_e_679_) == 8)
{
uint8_t v_nondep_781_; 
v_nondep_781_ = lean_ctor_get_uint8(v_e_679_, sizeof(void*)*4 + 8);
if (v_nondep_781_ == 1)
{
lean_object* v_declName_782_; lean_object* v_type_783_; lean_object* v_value_784_; lean_object* v_body_785_; lean_object* v_t_786_; lean_object* v_v_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___x_790_; 
v_declName_782_ = lean_ctor_get(v_e_679_, 0);
lean_inc_n(v_declName_782_, 2);
v_type_783_ = lean_ctor_get(v_e_679_, 1);
lean_inc_ref(v_type_783_);
v_value_784_ = lean_ctor_get(v_e_679_, 2);
lean_inc_ref(v_value_784_);
v_body_785_ = lean_ctor_get(v_e_679_, 3);
lean_inc_ref(v_body_785_);
lean_dec_ref_known(v_e_679_, 4);
v_t_786_ = lean_expr_instantiate_rev(v_type_783_, v_xs_680_);
lean_dec_ref(v_type_783_);
v_v_787_ = lean_expr_instantiate_rev(v_value_784_, v_xs_680_);
lean_dec_ref(v_value_784_);
v___x_788_ = lean_box(v_nondep_781_);
lean_inc_ref(v_t_786_);
v___f_789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 21, 13);
lean_closure_set(v___f_789_, 0, v_v_787_);
lean_closure_set(v___f_789_, 1, v_fvarIdToPos_686_);
lean_closure_set(v___f_789_, 2, v___x_788_);
lean_closure_set(v___f_789_, 3, v_t_786_);
lean_closure_set(v___f_789_, 4, v_subst_683_);
lean_closure_set(v___f_789_, 5, v_xs_680_);
lean_closure_set(v___f_789_, 6, v_xs_x27_681_);
lean_closure_set(v___f_789_, 7, v_args_682_);
lean_closure_set(v___f_789_, 8, v_types_684_);
lean_closure_set(v___f_789_, 9, v_varDeps_685_);
lean_closure_set(v___f_789_, 10, v_haveExpr_678_);
lean_closure_set(v___f_789_, 11, v_body_785_);
lean_closure_set(v___f_789_, 12, v_declName_782_);
v___x_790_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_782_, v_t_786_, v___f_789_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v___x_790_;
}
else
{
lean_dec(v_fvarIdToPos_686_);
lean_dec_ref(v_xs_680_);
v___y_695_ = v_a_687_;
v___y_696_ = v_a_688_;
v___y_697_ = v_a_689_;
v___y_698_ = v_a_690_;
v___y_699_ = v_a_691_;
v___y_700_ = v_a_692_;
goto v___jp_694_;
}
}
else
{
lean_dec(v_fvarIdToPos_686_);
lean_dec_ref(v_xs_680_);
v___y_695_ = v_a_687_;
v___y_696_ = v_a_688_;
v___y_697_ = v_a_689_;
v___y_698_ = v_a_690_;
v___y_699_ = v_a_691_;
v___y_700_ = v_a_692_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_array_get_size(v_subst_683_);
v___x_703_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_679_, v___x_701_, v___x_702_, v_subst_683_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_n(v_a_704_, 2);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = l_Lean_Meta_Sym_inferType(v_a_704_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_n(v_a_706_, 2);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_706_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
lean_inc(v_a_706_);
v___x_709_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_684_, v_a_706_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec_ref(v_types_684_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_681_, v_a_704_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = l_Lean_mkAppN(v_a_712_, v_args_682_);
lean_dec_ref(v_args_682_);
v___x_714_ = l_Lean_Meta_Sym_shareCommonInc(v___x_713_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_732_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_732_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_732_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_732_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_720_ = lean_box(0);
lean_inc(v_a_708_);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v_a_708_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
lean_inc_ref(v___x_721_);
v___x_722_ = l_Lean_mkConst(v___x_719_, v___x_721_);
lean_inc(v_a_715_);
lean_inc_ref(v_haveExpr_678_);
lean_inc_n(v_a_706_, 2);
v___x_723_ = l_Lean_mkApp3(v___x_722_, v_a_706_, v_haveExpr_678_, v_a_715_);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_725_ = l_Lean_mkConst(v___x_724_, v___x_721_);
v___x_726_ = l_Lean_mkAppB(v___x_725_, v_a_706_, v_haveExpr_678_);
v___x_727_ = l_Lean_Meta_mkExpectedPropHint(v___x_726_, v___x_723_);
v___x_728_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_728_, 0, v_a_706_);
lean_ctor_set(v___x_728_, 1, v_a_708_);
lean_ctor_set(v___x_728_, 2, v_a_715_);
lean_ctor_set(v___x_728_, 3, v___x_727_);
lean_ctor_set(v___x_728_, 4, v_varDeps_685_);
lean_ctor_set(v___x_728_, 5, v_a_710_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_728_);
v___x_730_ = v___x_717_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_a_710_);
lean_dec(v_a_708_);
lean_dec(v_a_706_);
lean_dec_ref(v_varDeps_685_);
lean_dec_ref(v_haveExpr_678_);
v_a_733_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_714_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_714_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_710_);
lean_dec(v_a_708_);
lean_dec(v_a_706_);
lean_dec_ref(v_varDeps_685_);
lean_dec_ref(v_args_682_);
lean_dec_ref(v_haveExpr_678_);
v_a_741_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_711_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_711_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_708_);
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec_ref(v_varDeps_685_);
lean_dec_ref(v_args_682_);
lean_dec_ref(v_xs_x27_681_);
lean_dec_ref(v_haveExpr_678_);
v_a_749_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_709_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_709_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec_ref(v_varDeps_685_);
lean_dec_ref(v_types_684_);
lean_dec_ref(v_args_682_);
lean_dec_ref(v_xs_x27_681_);
lean_dec_ref(v_haveExpr_678_);
v_a_757_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_707_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_707_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_a_704_);
lean_dec_ref(v_varDeps_685_);
lean_dec_ref(v_types_684_);
lean_dec_ref(v_args_682_);
lean_dec_ref(v_xs_x27_681_);
lean_dec_ref(v_haveExpr_678_);
v_a_765_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_705_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_705_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_varDeps_685_);
lean_dec_ref(v_types_684_);
lean_dec_ref(v_args_682_);
lean_dec_ref(v_xs_x27_681_);
lean_dec_ref(v_haveExpr_678_);
v_a_773_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_703_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_703_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_haveExpr_678_ = stack[0].m_obj;
lean_object* v_e_679_ = stack[1].m_obj;
lean_object* v_xs_680_ = stack[2].m_obj;
lean_object* v_xs_x27_681_ = stack[3].m_obj;
lean_object* v_args_682_ = stack[4].m_obj;
lean_object* v_subst_683_ = stack[5].m_obj;
lean_object* v_types_684_ = stack[6].m_obj;
lean_object* v_varDeps_685_ = stack[7].m_obj;
lean_object* v_fvarIdToPos_686_ = stack[8].m_obj;
lean_object* v_a_687_ = stack[9].m_obj;
lean_object* v_a_688_ = stack[10].m_obj;
lean_object* v_a_689_ = stack[11].m_obj;
lean_object* v_a_690_ = stack[12].m_obj;
lean_object* v_a_691_ = stack[13].m_obj;
lean_object* v_a_692_ = stack[14].m_obj;
lean_object* v_res_791_;
v_res_791_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_678_, v_e_679_, v_xs_680_, v_xs_x27_681_, v_args_682_, v_subst_683_, v_types_684_, v_varDeps_685_, v_fvarIdToPos_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
stack->m_obj
 = v_res_791_;
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_792_, lean_object* v_subst_793_, size_t v_sz_794_, size_t v___x_795_, lean_object* v_fvarIds_796_, lean_object* v_x_797_, lean_object* v_xs_798_, lean_object* v_xs_x27_799_, lean_object* v_args_800_, lean_object* v_a_801_, lean_object* v_types_802_, lean_object* v_a_803_, lean_object* v_varDeps_804_, lean_object* v_varPos_805_, lean_object* v_haveExpr_806_, lean_object* v_body_807_, lean_object* v_x_x27_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_792_, v_subst_793_, v_sz_794_, v___x_795_, v_fvarIds_796_);
lean_inc_ref(v_x_x27_808_);
v___x_817_ = l_Lean_mkAppN(v_x_x27_808_, v___x_816_);
lean_dec_ref(v___x_816_);
v___x_818_ = l_Lean_Meta_Sym_shareCommonInc(v___x_817_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = l_Lean_Expr_fvarId_x21(v_x_797_);
v___x_821_ = lean_array_get_size(v_xs_798_);
v___x_822_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_820_, v___x_821_, v_fvarIdToPos_792_);
v___x_823_ = lean_array_push(v_xs_798_, v_x_797_);
v___x_824_ = lean_array_push(v_xs_x27_799_, v_x_x27_808_);
v___x_825_ = lean_array_push(v_args_800_, v_a_801_);
v___x_826_ = lean_array_push(v_subst_793_, v_a_819_);
v___x_827_ = lean_array_push(v_types_802_, v_a_803_);
v___x_828_ = lean_array_push(v_varDeps_804_, v_varPos_805_);
v___x_829_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_806_, v_body_807_, v___x_823_, v___x_824_, v___x_825_, v___x_826_, v___x_827_, v___x_828_, v___x_822_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
return v___x_829_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_x_x27_808_);
lean_dec_ref(v_body_807_);
lean_dec_ref(v_haveExpr_806_);
lean_dec_ref(v_varPos_805_);
lean_dec_ref(v_varDeps_804_);
lean_dec_ref(v_a_803_);
lean_dec_ref(v_types_802_);
lean_dec_ref(v_a_801_);
lean_dec_ref(v_args_800_);
lean_dec_ref(v_xs_x27_799_);
lean_dec_ref(v_xs_798_);
lean_dec_ref(v_x_797_);
lean_dec_ref(v_subst_793_);
lean_dec(v_fvarIdToPos_792_);
v_a_830_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_818_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_818_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIdToPos_792_ = stack[0].m_obj;
lean_object* v_subst_793_ = stack[1].m_obj;
size_t v_sz_794_ = stack[2].m_num;
size_t v___x_795_ = stack[3].m_num;
lean_object* v_fvarIds_796_ = stack[4].m_obj;
lean_object* v_x_797_ = stack[5].m_obj;
lean_object* v_xs_798_ = stack[6].m_obj;
lean_object* v_xs_x27_799_ = stack[7].m_obj;
lean_object* v_args_800_ = stack[8].m_obj;
lean_object* v_a_801_ = stack[9].m_obj;
lean_object* v_types_802_ = stack[10].m_obj;
lean_object* v_a_803_ = stack[11].m_obj;
lean_object* v_varDeps_804_ = stack[12].m_obj;
lean_object* v_varPos_805_ = stack[13].m_obj;
lean_object* v_haveExpr_806_ = stack[14].m_obj;
lean_object* v_body_807_ = stack[15].m_obj;
lean_object* v_x_x27_808_ = stack[16].m_obj;
lean_object* v___y_809_ = stack[17].m_obj;
lean_object* v___y_810_ = stack[18].m_obj;
lean_object* v___y_811_ = stack[19].m_obj;
lean_object* v___y_812_ = stack[20].m_obj;
lean_object* v___y_813_ = stack[21].m_obj;
lean_object* v___y_814_ = stack[22].m_obj;
lean_object* v_res_838_;
v_res_838_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_792_, v_subst_793_, v_sz_794_, v___x_795_, v_fvarIds_796_, v_x_797_, v_xs_798_, v_xs_x27_799_, v_args_800_, v_a_801_, v_types_802_, v_a_803_, v_varDeps_804_, v_varPos_805_, v_haveExpr_806_, v_body_807_, v_x_x27_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_839_, lean_object* v_e_840_, lean_object* v_xs_841_, lean_object* v_xs_x27_842_, lean_object* v_args_843_, lean_object* v_subst_844_, lean_object* v_types_845_, lean_object* v_varDeps_846_, lean_object* v_fvarIdToPos_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_839_, v_e_840_, v_xs_841_, v_xs_x27_842_, v_args_843_, v_subst_844_, v_types_845_, v_varDeps_846_, v_fvarIdToPos_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_856_, lean_object* v_t_857_, lean_object* v_k_858_, lean_object* v_fallback_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_857_, v_k_858_, v_fallback_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_861_, lean_object* v_t_862_, lean_object* v_k_863_, lean_object* v_fallback_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_861_, v_t_862_, v_k_863_, v_fallback_864_);
lean_dec(v_fallback_864_);
lean_dec(v_k_863_);
lean_dec(v_t_862_);
return v_res_865_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_866_, lean_object* v_name_867_, uint8_t v_bi_868_, lean_object* v_type_869_, lean_object* v_k_870_, uint8_t v_kind_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_867_, v_bi_868_, v_type_869_, v_k_870_, v_kind_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
return v___x_879_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_867_ = stack[1].m_obj;
uint8_t v_bi_868_ = stack[2].m_num;
lean_object* v_type_869_ = stack[3].m_obj;
lean_object* v_k_870_ = stack[4].m_obj;
uint8_t v_kind_871_ = stack[5].m_num;
lean_object* v___y_872_ = stack[6].m_obj;
lean_object* v___y_873_ = stack[7].m_obj;
lean_object* v___y_874_ = stack[8].m_obj;
lean_object* v___y_875_ = stack[9].m_obj;
lean_object* v___y_876_ = stack[10].m_obj;
lean_object* v___y_877_ = stack[11].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_box(0), v_name_867_, v_bi_868_, v_type_869_, v_k_870_, v_kind_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_881_, lean_object* v_name_882_, lean_object* v_bi_883_, lean_object* v_type_884_, lean_object* v_k_885_, lean_object* v_kind_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
uint8_t v_bi_boxed_894_; uint8_t v_kind_boxed_895_; lean_object* v_res_896_; 
v_bi_boxed_894_ = lean_unbox(v_bi_883_);
v_kind_boxed_895_ = lean_unbox(v_kind_886_);
v_res_896_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_881_, v_name_882_, v_bi_boxed_894_, v_type_884_, v_k_885_, v_kind_boxed_895_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_896_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_897_, lean_object* v_name_898_, lean_object* v_type_899_, lean_object* v_k_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_898_, v_type_899_, v_k_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_898_ = stack[1].m_obj;
lean_object* v_type_899_ = stack[2].m_obj;
lean_object* v_k_900_ = stack[3].m_obj;
lean_object* v___y_901_ = stack[4].m_obj;
lean_object* v___y_902_ = stack[5].m_obj;
lean_object* v___y_903_ = stack[6].m_obj;
lean_object* v___y_904_ = stack[7].m_obj;
lean_object* v___y_905_ = stack[8].m_obj;
lean_object* v___y_906_ = stack[9].m_obj;
lean_object* v_res_909_;
v_res_909_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_box(0), v_name_898_, v_type_899_, v_k_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
stack->m_obj
 = v_res_909_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_910_, lean_object* v_name_911_, lean_object* v_type_912_, lean_object* v_k_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_910_, v_name_911_, v_type_912_, v_k_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_921_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_933_ = lean_box(1);
lean_inc_ref(v_haveExpr_924_);
v___x_934_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_924_, v_haveExpr_924_, v___x_932_, v___x_932_, v___x_932_, v___x_932_, v___x_932_, v___x_932_, v___x_933_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_934_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_toBetaApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_haveExpr_924_ = stack[0].m_obj;
lean_object* v_a_925_ = stack[1].m_obj;
lean_object* v_a_926_ = stack[2].m_obj;
lean_object* v_a_927_ = stack[3].m_obj;
lean_object* v_a_928_ = stack[4].m_obj;
lean_object* v_a_929_ = stack[5].m_obj;
lean_object* v_a_930_ = stack[6].m_obj;
lean_object* v_res_935_;
v_res_935_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
stack->m_obj
 = v_res_935_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_945_, lean_object* v_n_946_){
_start:
{
lean_object* v_zero_947_; uint8_t v_isZero_948_; 
v_zero_947_ = lean_unsigned_to_nat(0u);
v_isZero_948_ = lean_nat_dec_eq(v_n_946_, v_zero_947_);
if (v_isZero_948_ == 1)
{
lean_dec(v_n_946_);
return v_type_945_;
}
else
{
lean_object* v_one_949_; lean_object* v_n_950_; lean_object* v___x_951_; 
v_one_949_ = lean_unsigned_to_nat(1u);
v_n_950_ = lean_nat_sub(v_n_946_, v_one_949_);
lean_dec(v_n_946_);
v___x_951_ = l_Lean_Expr_bindingBody_x21(v_type_945_);
lean_dec_ref(v_type_945_);
v_type_945_ = v___x_951_;
v_n_946_ = v_n_950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(lean_object* v_idx_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Lean_Expr_bvar___override(v_idx_953_);
v___x_956_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_955_, v___y_954_);
return v___x_956_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_idx_957_, uint8_t v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v_idx_957_, v___y_960_);
return v___x_961_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_957_ = stack[0].m_obj;
uint8_t v___y_958_ = stack[1].m_num;
lean_object* v___y_959_ = stack[2].m_obj;
lean_object* v___y_960_ = stack[3].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(v_idx_957_, v___y_958_, v___y_959_, v___y_960_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___boxed(lean_object* v_idx_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___y_24943__boxed_967_; lean_object* v_res_968_; 
v___y_24943__boxed_967_ = lean_unbox(v___y_964_);
v_res_968_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(v_idx_963_, v___y_24943__boxed_967_, v___y_965_, v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_968_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0(void){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_HashMap_instInhabited___redArg();
return v___x_969_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_msg_970_, uint8_t v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_1486__overap_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_974_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0);
v___f_975_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_975_, 0, v___x_974_);
v___f_976_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_976_, 0, v___f_975_);
v___f_977_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_977_, 0, v___f_976_);
v___x_1486__overap_978_ = lean_panic_fn_borrowed(v___f_977_, v_msg_970_);
lean_dec_ref(v___f_977_);
v___x_979_ = lean_box(v___y_971_);
lean_inc_ref(v___y_972_);
v___x_980_ = lean_apply_3(v___x_1486__overap_978_, v___x_979_, v___y_972_, v___y_973_);
return v___x_980_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_970_ = stack[0].m_obj;
uint8_t v___y_971_ = stack[1].m_num;
lean_object* v___y_972_ = stack[2].m_obj;
lean_object* v___y_973_ = stack[3].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_msg_970_, v___y_971_, v___y_972_, v___y_973_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_msg_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v___y_24963__boxed_986_; lean_object* v_res_987_; 
v___y_24963__boxed_986_ = lean_unbox(v___y_983_);
v_res_987_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_msg_982_, v___y_24963__boxed_986_, v___y_984_, v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_987_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_988_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_1948__overap_998_; lean_object* v___x_999_; 
v___x_997_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0);
v___x_1948__overap_998_ = lean_panic_fn_borrowed(v___x_997_, v_msg_989_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
v___x_999_ = lean_apply_7(v___x_1948__overap_998_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, lean_box(0));
return v___x_999_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_989_ = stack[0].m_obj;
lean_object* v___y_990_ = stack[1].m_obj;
lean_object* v___y_991_ = stack[2].m_obj;
lean_object* v___y_992_ = stack[3].m_obj;
lean_object* v___y_993_ = stack[4].m_obj;
lean_object* v___y_994_ = stack[5].m_obj;
lean_object* v___y_995_ = stack[6].m_obj;
lean_object* v_res_1000_;
v_res_1000_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_msg_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
stack->m_obj
 = v_res_1000_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_msg_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1009_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object* v_x_1010_, lean_object* v_t_1011_, lean_object* v_v_1012_, lean_object* v_b_1013_, uint8_t v_nondep_1014_, lean_object* v___y_1015_, uint8_t v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___y_1020_; lean_object* v___y_1021_; 
if (v___y_1016_ == 0)
{
v___y_1020_ = v___y_1015_;
v___y_1021_ = v___y_1018_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1011_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 1);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 2);
v___x_1045_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1012_, v___y_1016_, v___y_1017_, v_a_1044_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 2);
v___x_1047_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1013_, v___y_1016_, v___y_1017_, v_a_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 2);
v___y_1020_ = v___y_1015_;
v___y_1021_ = v_a_1048_;
goto v___jp_1019_;
}
else
{
lean_object* v_a_1049_; lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_b_1013_);
lean_dec_ref(v_v_1012_);
lean_dec_ref(v_t_1011_);
lean_dec(v_x_1010_);
v_a_1049_ = lean_ctor_get(v___x_1047_, 0);
v_a_1050_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1047_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_inc(v_a_1049_);
lean_dec(v___x_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_b_1013_);
lean_dec_ref(v_v_1012_);
lean_dec_ref(v_t_1011_);
lean_dec(v_x_1010_);
v_a_1058_ = lean_ctor_get(v___x_1045_, 0);
v_a_1059_ = lean_ctor_get(v___x_1045_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1045_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_inc(v_a_1058_);
lean_dec(v___x_1045_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_b_1013_);
lean_dec_ref(v_v_1012_);
lean_dec_ref(v_t_1011_);
lean_dec(v_x_1010_);
v_a_1067_ = lean_ctor_get(v___x_1043_, 0);
v_a_1068_ = lean_ctor_get(v___x_1043_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1043_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_inc(v_a_1067_);
lean_dec(v___x_1043_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1067_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
v___jp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = l_Lean_Expr_letE___override(v_x_1010_, v_t_1011_, v_v_1012_, v_b_1013_, v_nondep_1014_);
v___x_1023_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1022_, v___y_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_a_1025_ = lean_ctor_get(v___x_1023_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1027_ = v___x_1023_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1024_);
lean_ctor_set(v___x_1029_, 1, v___y_1020_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_a_1025_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v___y_1020_);
v_a_1034_ = lean_ctor_get(v___x_1023_, 0);
v_a_1035_ = lean_ctor_get(v___x_1023_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1023_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_inc(v_a_1034_);
lean_dec(v___x_1023_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1034_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1010_ = stack[0].m_obj;
lean_object* v_t_1011_ = stack[1].m_obj;
lean_object* v_v_1012_ = stack[2].m_obj;
lean_object* v_b_1013_ = stack[3].m_obj;
uint8_t v_nondep_1014_ = stack[4].m_num;
lean_object* v___y_1015_ = stack[5].m_obj;
uint8_t v___y_1016_ = stack[6].m_num;
lean_object* v___y_1017_ = stack[7].m_obj;
lean_object* v___y_1018_ = stack[8].m_obj;
lean_object* v_res_1076_;
v_res_1076_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_x_1010_, v_t_1011_, v_v_1012_, v_b_1013_, v_nondep_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
stack->m_obj
 = v_res_1076_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object* v_x_1077_, lean_object* v_t_1078_, lean_object* v_v_1079_, lean_object* v_b_1080_, lean_object* v_nondep_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_nondep_boxed_1086_; uint8_t v___y_25044__boxed_1087_; lean_object* v_res_1088_; 
v_nondep_boxed_1086_ = lean_unbox(v_nondep_1081_);
v___y_25044__boxed_1087_ = lean_unbox(v___y_1083_);
v_res_1088_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_x_1077_, v_t_1078_, v_v_1079_, v_b_1080_, v_nondep_boxed_1086_, v___y_1082_, v___y_25044__boxed_1087_, v___y_1084_, v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1088_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object* v_x_1089_, uint8_t v_bi_1090_, lean_object* v_t_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, uint8_t v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___y_1098_; lean_object* v___y_1099_; 
if (v___y_1094_ == 0)
{
v___y_1098_ = v___y_1093_;
v___y_1099_ = v___y_1096_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1091_, v___y_1094_, v___y_1095_, v___y_1096_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 1);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 2);
v___x_1123_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1092_, v___y_1094_, v___y_1095_, v_a_1122_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 2);
v___y_1098_ = v___y_1093_;
v___y_1099_ = v_a_1124_;
goto v___jp_1097_;
}
else
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_b_1092_);
lean_dec_ref(v_t_1091_);
lean_dec(v_x_1089_);
v_a_1125_ = lean_ctor_get(v___x_1123_, 0);
v_a_1126_ = lean_ctor_get(v___x_1123_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1123_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_inc(v_a_1125_);
lean_dec(v___x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_b_1092_);
lean_dec_ref(v_t_1091_);
lean_dec(v_x_1089_);
v_a_1134_ = lean_ctor_get(v___x_1121_, 0);
v_a_1135_ = lean_ctor_get(v___x_1121_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1121_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_inc(v_a_1134_);
lean_dec(v___x_1121_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1134_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
v___jp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l_Lean_Expr_lam___override(v_x_1089_, v_t_1091_, v_b_1092_, v_bi_1090_);
v___x_1101_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1100_, v___y_1099_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1111_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_a_1103_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1105_ = v___x_1101_;
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_a_1102_);
lean_ctor_set(v___x_1107_, 1, v___y_1098_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_a_1103_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v___y_1098_);
v_a_1112_ = lean_ctor_get(v___x_1101_, 0);
v_a_1113_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1101_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_inc(v_a_1112_);
lean_dec(v___x_1101_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1112_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1089_ = stack[0].m_obj;
uint8_t v_bi_1090_ = stack[1].m_num;
lean_object* v_t_1091_ = stack[2].m_obj;
lean_object* v_b_1092_ = stack[3].m_obj;
lean_object* v___y_1093_ = stack[4].m_obj;
uint8_t v___y_1094_ = stack[5].m_num;
lean_object* v___y_1095_ = stack[6].m_obj;
lean_object* v___y_1096_ = stack[7].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_x_1089_, v_bi_1090_, v_t_1091_, v_b_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object* v_x_1144_, lean_object* v_bi_1145_, lean_object* v_t_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v_bi_boxed_1152_; uint8_t v___y_25238__boxed_1153_; lean_object* v_res_1154_; 
v_bi_boxed_1152_ = lean_unbox(v_bi_1145_);
v___y_25238__boxed_1153_ = lean_unbox(v___y_1149_);
v_res_1154_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_x_1144_, v_bi_boxed_1152_, v_t_1146_, v_b_1147_, v___y_1148_, v___y_25238__boxed_1153_, v___y_1150_, v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1154_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object* v_x_1155_, uint8_t v_bi_1156_, lean_object* v_t_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, uint8_t v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___y_1164_; lean_object* v___y_1165_; 
if (v___y_1160_ == 0)
{
v___y_1164_ = v___y_1159_;
v___y_1165_ = v___y_1162_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1157_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 1);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 2);
v___x_1189_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1158_, v___y_1160_, v___y_1161_, v_a_1188_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 1);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 2);
v___y_1164_ = v___y_1159_;
v___y_1165_ = v_a_1190_;
goto v___jp_1163_;
}
else
{
lean_object* v_a_1191_; lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_b_1158_);
lean_dec_ref(v_t_1157_);
lean_dec(v_x_1155_);
v_a_1191_ = lean_ctor_get(v___x_1189_, 0);
v_a_1192_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1189_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_inc(v_a_1191_);
lean_dec(v___x_1189_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1191_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_b_1158_);
lean_dec_ref(v_t_1157_);
lean_dec(v_x_1155_);
v_a_1200_ = lean_ctor_get(v___x_1187_, 0);
v_a_1201_ = lean_ctor_get(v___x_1187_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1187_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_inc(v_a_1200_);
lean_dec(v___x_1187_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1200_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
v___jp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = l_Lean_Expr_forallE___override(v_x_1155_, v_t_1157_, v_b_1158_, v_bi_1156_);
v___x_1167_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1166_, v___y_1165_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1177_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_a_1169_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1171_ = v___x_1167_;
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_a_1168_);
lean_ctor_set(v___x_1173_, 1, v___y_1164_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1169_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v___y_1164_);
v_a_1178_ = lean_ctor_get(v___x_1167_, 0);
v_a_1179_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1167_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_inc(v_a_1178_);
lean_dec(v___x_1167_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1155_ = stack[0].m_obj;
uint8_t v_bi_1156_ = stack[1].m_num;
lean_object* v_t_1157_ = stack[2].m_obj;
lean_object* v_b_1158_ = stack[3].m_obj;
lean_object* v___y_1159_ = stack[4].m_obj;
uint8_t v___y_1160_ = stack[5].m_num;
lean_object* v___y_1161_ = stack[6].m_obj;
lean_object* v___y_1162_ = stack[7].m_obj;
lean_object* v_res_1209_;
v_res_1209_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_x_1155_, v_bi_1156_, v_t_1157_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
stack->m_obj
 = v_res_1209_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object* v_x_1210_, lean_object* v_bi_1211_, lean_object* v_t_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_bi_boxed_1218_; uint8_t v___y_25398__boxed_1219_; lean_object* v_res_1220_; 
v_bi_boxed_1218_ = lean_unbox(v_bi_1211_);
v___y_25398__boxed_1219_ = lean_unbox(v___y_1215_);
v_res_1220_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_x_1210_, v_bi_boxed_1218_, v_t_1212_, v_b_1213_, v___y_1214_, v___y_25398__boxed_1219_, v___y_1216_, v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1220_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object* v_f_1221_, lean_object* v_a_1222_, lean_object* v___y_1223_, uint8_t v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___y_1228_; lean_object* v___y_1229_; 
if (v___y_1224_ == 0)
{
v___y_1228_ = v___y_1223_;
v___y_1229_ = v___y_1226_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1221_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 2);
v___x_1253_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1222_, v___y_1224_, v___y_1225_, v_a_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 2);
v___y_1228_ = v___y_1223_;
v___y_1229_ = v_a_1254_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1255_; lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v___y_1223_);
lean_dec_ref(v_a_1222_);
lean_dec_ref(v_f_1221_);
v_a_1255_ = lean_ctor_get(v___x_1253_, 0);
v_a_1256_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1253_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_inc(v_a_1255_);
lean_dec(v___x_1253_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1255_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v___y_1223_);
lean_dec_ref(v_a_1222_);
lean_dec_ref(v_f_1221_);
v_a_1264_ = lean_ctor_get(v___x_1251_, 0);
v_a_1265_ = lean_ctor_get(v___x_1251_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1251_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_inc(v_a_1264_);
lean_dec(v___x_1251_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1264_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
v___jp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_Expr_app___override(v_f_1221_, v_a_1222_);
v___x_1231_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1230_, v___y_1229_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1241_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_a_1233_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1235_ = v___x_1231_;
v_isShared_1236_ = v_isSharedCheck_1241_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1241_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_a_1232_);
lean_ctor_set(v___x_1237_, 1, v___y_1228_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1237_);
v___x_1239_ = v___x_1235_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_a_1233_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v___y_1228_);
v_a_1242_ = lean_ctor_get(v___x_1231_, 0);
v_a_1243_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1231_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_inc(v_a_1242_);
lean_dec(v___x_1231_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1242_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1221_ = stack[0].m_obj;
lean_object* v_a_1222_ = stack[1].m_obj;
lean_object* v___y_1223_ = stack[2].m_obj;
uint8_t v___y_1224_ = stack[3].m_num;
lean_object* v___y_1225_ = stack[4].m_obj;
lean_object* v___y_1226_ = stack[5].m_obj;
lean_object* v_res_1273_;
v_res_1273_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_f_1221_, v_a_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
stack->m_obj
 = v_res_1273_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object* v_f_1274_, lean_object* v_a_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v___y_25558__boxed_1280_; lean_object* v_res_1281_; 
v___y_25558__boxed_1280_ = lean_unbox(v___y_1277_);
v_res_1281_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_f_1274_, v_a_1275_, v___y_1276_, v___y_25558__boxed_1280_, v___y_1278_, v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1281_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object* v_d_1282_, lean_object* v_e_1283_, lean_object* v___y_1284_, uint8_t v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___y_1289_; lean_object* v___y_1290_; 
if (v___y_1285_ == 0)
{
v___y_1289_ = v___y_1284_;
v___y_1290_ = v___y_1287_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1283_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 2);
v___y_1289_ = v___y_1284_;
v___y_1290_ = v_a_1313_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_e_1283_);
lean_dec(v_d_1282_);
v_a_1314_ = lean_ctor_get(v___x_1312_, 0);
v_a_1315_ = lean_ctor_get(v___x_1312_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1312_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_inc(v_a_1314_);
lean_dec(v___x_1312_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1314_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
v___jp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = l_Lean_Expr_mdata___override(v_d_1282_, v_e_1283_);
v___x_1292_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1291_, v___y_1290_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_a_1294_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1296_ = v___x_1292_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_a_1293_);
lean_ctor_set(v___x_1298_, 1, v___y_1289_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_a_1294_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___y_1289_);
v_a_1303_ = lean_ctor_get(v___x_1292_, 0);
v_a_1304_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1292_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_inc(v_a_1303_);
lean_dec(v___x_1292_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_a_1304_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1282_ = stack[0].m_obj;
lean_object* v_e_1283_ = stack[1].m_obj;
lean_object* v___y_1284_ = stack[2].m_obj;
uint8_t v___y_1285_ = stack[3].m_num;
lean_object* v___y_1286_ = stack[4].m_obj;
lean_object* v___y_1287_ = stack[5].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_d_1282_, v_e_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object* v_d_1324_, lean_object* v_e_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___y_25718__boxed_1330_; lean_object* v_res_1331_; 
v___y_25718__boxed_1330_ = lean_unbox(v___y_1327_);
v_res_1331_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_d_1324_, v_e_1325_, v___y_1326_, v___y_25718__boxed_1330_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1331_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(lean_object* v_msg_1339_, lean_object* v___y_1340_, uint8_t v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___f_1344_; lean_object* v___f_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_24463__overap_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___f_1344_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0));
v___f_1345_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1));
v___f_1346_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2));
v___x_1347_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3));
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___f_1344_);
v___x_1349_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4));
v___x_1350_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5));
v___x_1351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1348_);
lean_ctor_set(v___x_1351_, 1, v___x_1349_);
lean_ctor_set(v___x_1351_, 2, v___f_1345_);
lean_ctor_set(v___x_1351_, 3, v___f_1346_);
lean_ctor_set(v___x_1351_, 4, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6));
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_ReaderT_instMonad___redArg(v___x_1353_);
v___x_1355_ = l_ReaderT_instMonad___redArg(v___x_1354_);
lean_inc_ref_n(v___x_1355_, 6);
v___f_1356_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1356_, 0, v___x_1355_);
v___f_1357_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1357_, 0, v___x_1355_);
v___f_1358_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1358_, 0, v___x_1355_);
v___f_1359_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1359_, 0, v___x_1355_);
v___x_1360_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1360_, 0, lean_box(0));
lean_closure_set(v___x_1360_, 1, lean_box(0));
lean_closure_set(v___x_1360_, 2, v___x_1355_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___f_1356_);
v___x_1362_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1362_, 0, lean_box(0));
lean_closure_set(v___x_1362_, 1, lean_box(0));
lean_closure_set(v___x_1362_, 2, v___x_1355_);
v___x_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
lean_ctor_set(v___x_1363_, 2, v___f_1357_);
lean_ctor_set(v___x_1363_, 3, v___f_1358_);
lean_ctor_set(v___x_1363_, 4, v___f_1359_);
v___x_1364_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1364_, 0, lean_box(0));
lean_closure_set(v___x_1364_, 1, lean_box(0));
lean_closure_set(v___x_1364_, 2, v___x_1355_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_instInhabitedExpr;
v___x_1367_ = l_instInhabitedOfMonad___redArg(v___x_1365_, v___x_1366_);
v___x_24463__overap_1368_ = lean_panic_fn_borrowed(v___x_1367_, v_msg_1339_);
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(v___y_1341_);
lean_inc_ref(v___y_1342_);
v___x_1370_ = lean_apply_4(v___x_24463__overap_1368_, v___y_1340_, v___x_1369_, v___y_1342_, v___y_1343_);
return v___x_1370_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1339_ = stack[0].m_obj;
lean_object* v___y_1340_ = stack[1].m_obj;
uint8_t v___y_1341_ = stack[2].m_num;
lean_object* v___y_1342_ = stack[3].m_obj;
lean_object* v___y_1343_ = stack[4].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___boxed(lean_object* v_msg_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v___y_25858__boxed_1377_; lean_object* v_res_1378_; 
v___y_25858__boxed_1377_ = lean_unbox(v___y_1374_);
v_res_1378_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v_msg_1372_, v___y_1373_, v___y_25858__boxed_1377_, v___y_1375_, v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1378_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object* v_structName_1379_, lean_object* v_idx_1380_, lean_object* v_struct_1381_, lean_object* v___y_1382_, uint8_t v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___y_1387_; lean_object* v___y_1388_; 
if (v___y_1383_ == 0)
{
v___y_1387_ = v___y_1382_;
v___y_1388_ = v___y_1385_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1381_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 2);
v___y_1387_ = v___y_1382_;
v___y_1388_ = v_a_1411_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1412_; lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_struct_1381_);
lean_dec(v_idx_1380_);
lean_dec(v_structName_1379_);
v_a_1412_ = lean_ctor_get(v___x_1410_, 0);
v_a_1413_ = lean_ctor_get(v___x_1410_, 1);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1410_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_inc(v_a_1412_);
lean_dec(v___x_1410_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1412_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
v___jp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = l_Lean_Expr_proj___override(v_structName_1379_, v_idx_1380_, v_struct_1381_);
v___x_1390_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1389_, v___y_1388_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_a_1392_ = lean_ctor_get(v___x_1390_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v___x_1390_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_a_1391_);
lean_ctor_set(v___x_1396_, 1, v___y_1387_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_a_1392_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v___y_1387_);
v_a_1401_ = lean_ctor_get(v___x_1390_, 0);
v_a_1402_ = lean_ctor_get(v___x_1390_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1390_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_inc(v_a_1401_);
lean_dec(v___x_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1401_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_1379_ = stack[0].m_obj;
lean_object* v_idx_1380_ = stack[1].m_obj;
lean_object* v_struct_1381_ = stack[2].m_obj;
lean_object* v___y_1382_ = stack[3].m_obj;
uint8_t v___y_1383_ = stack[4].m_num;
lean_object* v___y_1384_ = stack[5].m_obj;
lean_object* v___y_1385_ = stack[6].m_obj;
lean_object* v_res_1421_;
v_res_1421_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_structName_1379_, v_idx_1380_, v_struct_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
stack->m_obj
 = v_res_1421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object* v_structName_1422_, lean_object* v_idx_1423_, lean_object* v_struct_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v___y_25970__boxed_1429_; lean_object* v_res_1430_; 
v___y_25970__boxed_1429_ = lean_unbox(v___y_1426_);
v_res_1430_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_structName_1422_, v_idx_1423_, v_struct_1424_, v___y_1425_, v___y_25970__boxed_1429_, v___y_1427_, v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_1431_, lean_object* v_x_1432_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_box(0);
return v___x_1433_;
}
else
{
lean_object* v_key_1434_; lean_object* v_value_1435_; lean_object* v_tail_1436_; lean_object* v_fst_1437_; lean_object* v_snd_1438_; lean_object* v_fst_1439_; lean_object* v_snd_1440_; size_t v___x_1441_; size_t v___x_1442_; uint8_t v___x_1443_; 
v_key_1434_ = lean_ctor_get(v_x_1432_, 0);
v_value_1435_ = lean_ctor_get(v_x_1432_, 1);
v_tail_1436_ = lean_ctor_get(v_x_1432_, 2);
v_fst_1437_ = lean_ctor_get(v_key_1434_, 0);
v_snd_1438_ = lean_ctor_get(v_key_1434_, 1);
v_fst_1439_ = lean_ctor_get(v_a_1431_, 0);
v_snd_1440_ = lean_ctor_get(v_a_1431_, 1);
v___x_1441_ = lean_ptr_addr(v_fst_1437_);
v___x_1442_ = lean_ptr_addr(v_fst_1439_);
v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
v_x_1432_ = v_tail_1436_;
goto _start;
}
else
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_nat_dec_eq(v_snd_1438_, v_snd_1440_);
if (v___x_1445_ == 0)
{
v_x_1432_ = v_tail_1436_;
goto _start;
}
else
{
lean_object* v___x_1447_; 
lean_inc(v_value_1435_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_value_1435_);
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1448_, v_x_1449_);
lean_dec(v_x_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(lean_object* v_m_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_buckets_1453_; lean_object* v_fst_1454_; lean_object* v_snd_1455_; lean_object* v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v___x_1462_; uint64_t v___x_1463_; uint64_t v___x_1464_; uint64_t v_fold_1465_; uint64_t v___x_1466_; uint64_t v___x_1467_; uint64_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_buckets_1453_ = lean_ctor_get(v_m_1451_, 1);
v_fst_1454_ = lean_ctor_get(v_a_1452_, 0);
v_snd_1455_ = lean_ctor_get(v_a_1452_, 1);
v___x_1456_ = lean_array_get_size(v_buckets_1453_);
v___x_1457_ = lean_ptr_addr(v_fst_1454_);
v___x_1458_ = ((size_t)3ULL);
v___x_1459_ = lean_usize_shift_right(v___x_1457_, v___x_1458_);
v___x_1460_ = lean_usize_to_uint64(v___x_1459_);
v___x_1461_ = lean_uint64_of_nat(v_snd_1455_);
v___x_1462_ = lean_uint64_mix_hash(v___x_1460_, v___x_1461_);
v___x_1463_ = 32ULL;
v___x_1464_ = lean_uint64_shift_right(v___x_1462_, v___x_1463_);
v_fold_1465_ = lean_uint64_xor(v___x_1462_, v___x_1464_);
v___x_1466_ = 16ULL;
v___x_1467_ = lean_uint64_shift_right(v_fold_1465_, v___x_1466_);
v___x_1468_ = lean_uint64_xor(v_fold_1465_, v___x_1467_);
v___x_1469_ = lean_uint64_to_usize(v___x_1468_);
v___x_1470_ = lean_usize_of_nat(v___x_1456_);
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_sub(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_usize_land(v___x_1469_, v___x_1472_);
v___x_1474_ = lean_array_uget_borrowed(v_buckets_1453_, v___x_1473_);
v___x_1475_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1452_, v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1476_, v_a_1477_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_m_1476_);
return v_res_1478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Array_instInhabited___redArg();
return v___x_1479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3));
v___x_1484_ = lean_unsigned_to_nat(12u);
v___x_1485_ = lean_unsigned_to_nat(234u);
v___x_1486_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2));
v___x_1487_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_1488_ = l_mkPanicMessageWithDecl(v___x_1487_, v___x_1486_, v___x_1485_, v___x_1484_, v___x_1483_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1493_ = lean_unsigned_to_nat(67u);
v___x_1494_ = lean_unsigned_to_nat(35u);
v___x_1495_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___x_1496_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___x_1497_ = l_mkPanicMessageWithDecl(v___x_1496_, v___x_1495_, v___x_1494_, v___x_1493_, v___x_1492_);
return v___x_1497_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_n_1498_, lean_object* v_varDeps_1499_, lean_object* v_xs_1500_, lean_object* v_e_1501_, lean_object* v_offset_1502_, lean_object* v_a_1503_, uint8_t v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
switch(lean_obj_tag(v_e_1501_))
{
case 5:
{
lean_object* v_fn_1507_; lean_object* v_arg_1508_; lean_object* v___x_1509_; 
v_fn_1507_ = lean_ctor_get(v_e_1501_, 0);
v_arg_1508_ = lean_ctor_get(v_e_1501_, 1);
lean_inc(v_offset_1502_);
lean_inc_ref(v_fn_1507_);
v___x_1509_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_fn_1507_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_a_1511_; lean_object* v_fst_1512_; lean_object* v_snd_1513_; lean_object* v___x_1514_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
v_a_1511_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1509_, 2);
v_fst_1512_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_fst_1512_);
v_snd_1513_ = lean_ctor_get(v_a_1510_, 1);
lean_inc(v_snd_1513_);
lean_dec(v_a_1510_);
lean_inc_ref(v_arg_1508_);
v___x_1514_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_arg_1508_, v_offset_1502_, v_snd_1513_, v_a_1504_, v_a_1505_, v_a_1511_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1540_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_a_1516_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1518_ = v___x_1514_;
v_isShared_1519_ = v_isSharedCheck_1540_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1540_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_fst_1520_; lean_object* v_snd_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1539_; 
v_fst_1520_ = lean_ctor_get(v_a_1515_, 0);
v_snd_1521_ = lean_ctor_get(v_a_1515_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1523_ = v_a_1515_;
v_isShared_1524_ = v_isSharedCheck_1539_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_snd_1521_);
lean_inc(v_fst_1520_);
lean_dec(v_a_1515_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1539_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
size_t v___x_1525_; size_t v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_ptr_addr(v_fn_1507_);
v___x_1526_ = lean_ptr_addr(v_fst_1512_);
v___x_1527_ = lean_usize_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_del_object(v___x_1523_);
lean_del_object(v___x_1518_);
lean_dec_ref_known(v_e_1501_, 2);
v___x_1528_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1512_, v_fst_1520_, v_snd_1521_, v_a_1504_, v_a_1505_, v_a_1516_);
return v___x_1528_;
}
else
{
size_t v___x_1529_; size_t v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_ptr_addr(v_arg_1508_);
v___x_1530_ = lean_ptr_addr(v_fst_1520_);
v___x_1531_ = lean_usize_dec_eq(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_del_object(v___x_1523_);
lean_del_object(v___x_1518_);
lean_dec_ref_known(v_e_1501_, 2);
v___x_1532_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1512_, v_fst_1520_, v_snd_1521_, v_a_1504_, v_a_1505_, v_a_1516_);
return v___x_1532_;
}
else
{
lean_object* v___x_1534_; 
lean_dec(v_fst_1520_);
lean_dec(v_fst_1512_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_e_1501_);
v___x_1534_ = v___x_1523_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_e_1501_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_snd_1521_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1534_);
v___x_1536_ = v___x_1518_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_a_1516_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1512_);
lean_dec_ref_known(v_e_1501_, 2);
return v___x_1514_;
}
}
else
{
lean_dec_ref_known(v_e_1501_, 2);
lean_dec(v_offset_1502_);
return v___x_1509_;
}
}
case 6:
{
lean_object* v_binderName_1541_; lean_object* v_binderType_1542_; lean_object* v_body_1543_; uint8_t v_binderInfo_1544_; lean_object* v___x_1545_; 
v_binderName_1541_ = lean_ctor_get(v_e_1501_, 0);
v_binderType_1542_ = lean_ctor_get(v_e_1501_, 1);
v_body_1543_ = lean_ctor_get(v_e_1501_, 2);
v_binderInfo_1544_ = lean_ctor_get_uint8(v_e_1501_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1502_);
lean_inc_ref(v_binderType_1542_);
v___x_1545_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_binderType_1542_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_a_1547_; lean_object* v_fst_1548_; lean_object* v_snd_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
v_a_1547_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1545_, 2);
v_fst_1548_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_fst_1548_);
v_snd_1549_ = lean_ctor_get(v_a_1546_, 1);
lean_inc(v_snd_1549_);
lean_dec(v_a_1546_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_offset_1502_, v___x_1550_);
lean_dec(v_offset_1502_);
lean_inc_ref(v_body_1543_);
v___x_1552_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_body_1543_, v___x_1551_, v_snd_1549_, v_a_1504_, v_a_1505_, v_a_1547_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1578_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_a_1554_ = lean_ctor_get(v___x_1552_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1556_ = v___x_1552_;
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_fst_1558_; lean_object* v_snd_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1577_; 
v_fst_1558_ = lean_ctor_get(v_a_1553_, 0);
v_snd_1559_ = lean_ctor_get(v_a_1553_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_a_1553_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1561_ = v_a_1553_;
v_isShared_1562_ = v_isSharedCheck_1577_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snd_1559_);
lean_inc(v_fst_1558_);
lean_dec(v_a_1553_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1577_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
size_t v___x_1563_; size_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_ptr_addr(v_binderType_1542_);
v___x_1564_ = lean_ptr_addr(v_fst_1548_);
v___x_1565_ = lean_usize_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_inc(v_binderName_1541_);
lean_del_object(v___x_1561_);
lean_del_object(v___x_1556_);
lean_dec_ref_known(v_e_1501_, 3);
v___x_1566_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1541_, v_binderInfo_1544_, v_fst_1548_, v_fst_1558_, v_snd_1559_, v_a_1504_, v_a_1505_, v_a_1554_);
return v___x_1566_;
}
else
{
size_t v___x_1567_; size_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = lean_ptr_addr(v_body_1543_);
v___x_1568_ = lean_ptr_addr(v_fst_1558_);
v___x_1569_ = lean_usize_dec_eq(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_inc(v_binderName_1541_);
lean_del_object(v___x_1561_);
lean_del_object(v___x_1556_);
lean_dec_ref_known(v_e_1501_, 3);
v___x_1570_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1541_, v_binderInfo_1544_, v_fst_1548_, v_fst_1558_, v_snd_1559_, v_a_1504_, v_a_1505_, v_a_1554_);
return v___x_1570_;
}
else
{
lean_object* v___x_1572_; 
lean_dec(v_fst_1558_);
lean_dec(v_fst_1548_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_e_1501_);
v___x_1572_ = v___x_1561_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_e_1501_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_snd_1559_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1574_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1572_);
v___x_1574_ = v___x_1556_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_a_1554_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1548_);
lean_dec_ref_known(v_e_1501_, 3);
return v___x_1552_;
}
}
else
{
lean_dec_ref_known(v_e_1501_, 3);
lean_dec(v_offset_1502_);
return v___x_1545_;
}
}
case 7:
{
lean_object* v_binderName_1579_; lean_object* v_binderType_1580_; lean_object* v_body_1581_; uint8_t v_binderInfo_1582_; lean_object* v___x_1583_; 
v_binderName_1579_ = lean_ctor_get(v_e_1501_, 0);
v_binderType_1580_ = lean_ctor_get(v_e_1501_, 1);
v_body_1581_ = lean_ctor_get(v_e_1501_, 2);
v_binderInfo_1582_ = lean_ctor_get_uint8(v_e_1501_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1502_);
lean_inc_ref(v_binderType_1580_);
v___x_1583_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_binderType_1580_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v_a_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
v_a_1585_ = lean_ctor_get(v___x_1583_, 1);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1583_, 2);
v_fst_1586_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_fst_1586_);
v_snd_1587_ = lean_ctor_get(v_a_1584_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_a_1584_);
v___x_1588_ = lean_unsigned_to_nat(1u);
v___x_1589_ = lean_nat_add(v_offset_1502_, v___x_1588_);
lean_dec(v_offset_1502_);
lean_inc_ref(v_body_1581_);
v___x_1590_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_body_1581_, v___x_1589_, v_snd_1587_, v_a_1504_, v_a_1505_, v_a_1585_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1616_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_a_1592_ = lean_ctor_get(v___x_1590_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1594_ = v___x_1590_;
v_isShared_1595_ = v_isSharedCheck_1616_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1616_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1615_; 
v_fst_1596_ = lean_ctor_get(v_a_1591_, 0);
v_snd_1597_ = lean_ctor_get(v_a_1591_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_a_1591_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1599_ = v_a_1591_;
v_isShared_1600_ = v_isSharedCheck_1615_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_inc(v_fst_1596_);
lean_dec(v_a_1591_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1615_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
size_t v___x_1601_; size_t v___x_1602_; uint8_t v___x_1603_; 
v___x_1601_ = lean_ptr_addr(v_binderType_1580_);
v___x_1602_ = lean_ptr_addr(v_fst_1586_);
v___x_1603_ = lean_usize_dec_eq(v___x_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_inc(v_binderName_1579_);
lean_del_object(v___x_1599_);
lean_del_object(v___x_1594_);
lean_dec_ref_known(v_e_1501_, 3);
v___x_1604_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1579_, v_binderInfo_1582_, v_fst_1586_, v_fst_1596_, v_snd_1597_, v_a_1504_, v_a_1505_, v_a_1592_);
return v___x_1604_;
}
else
{
size_t v___x_1605_; size_t v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = lean_ptr_addr(v_body_1581_);
v___x_1606_ = lean_ptr_addr(v_fst_1596_);
v___x_1607_ = lean_usize_dec_eq(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_inc(v_binderName_1579_);
lean_del_object(v___x_1599_);
lean_del_object(v___x_1594_);
lean_dec_ref_known(v_e_1501_, 3);
v___x_1608_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1579_, v_binderInfo_1582_, v_fst_1586_, v_fst_1596_, v_snd_1597_, v_a_1504_, v_a_1505_, v_a_1592_);
return v___x_1608_;
}
else
{
lean_object* v___x_1610_; 
lean_dec(v_fst_1596_);
lean_dec(v_fst_1586_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_e_1501_);
v___x_1610_ = v___x_1599_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_e_1501_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_snd_1597_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1610_);
v___x_1612_ = v___x_1594_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_a_1592_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1586_);
lean_dec_ref_known(v_e_1501_, 3);
return v___x_1590_;
}
}
else
{
lean_dec_ref_known(v_e_1501_, 3);
lean_dec(v_offset_1502_);
return v___x_1583_;
}
}
case 8:
{
lean_object* v_declName_1617_; lean_object* v_type_1618_; lean_object* v_value_1619_; lean_object* v_body_1620_; uint8_t v_nondep_1621_; lean_object* v___x_1622_; 
v_declName_1617_ = lean_ctor_get(v_e_1501_, 0);
v_type_1618_ = lean_ctor_get(v_e_1501_, 1);
v_value_1619_ = lean_ctor_get(v_e_1501_, 2);
v_body_1620_ = lean_ctor_get(v_e_1501_, 3);
v_nondep_1621_ = lean_ctor_get_uint8(v_e_1501_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1502_);
lean_inc_ref(v_type_1618_);
v___x_1622_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_type_1618_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_a_1624_; lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
v_a_1624_ = lean_ctor_get(v___x_1622_, 1);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1622_, 2);
v_fst_1625_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_fst_1625_);
v_snd_1626_ = lean_ctor_get(v_a_1623_, 1);
lean_inc(v_snd_1626_);
lean_dec(v_a_1623_);
lean_inc(v_offset_1502_);
lean_inc_ref(v_value_1619_);
v___x_1627_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_value_1619_, v_offset_1502_, v_snd_1626_, v_a_1504_, v_a_1505_, v_a_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v_a_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
v_a_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1627_, 2);
v_fst_1630_ = lean_ctor_get(v_a_1628_, 0);
lean_inc(v_fst_1630_);
v_snd_1631_ = lean_ctor_get(v_a_1628_, 1);
lean_inc(v_snd_1631_);
lean_dec(v_a_1628_);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_nat_add(v_offset_1502_, v___x_1632_);
lean_dec(v_offset_1502_);
lean_inc_ref(v_body_1620_);
v___x_1634_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_body_1620_, v___x_1633_, v_snd_1631_, v_a_1504_, v_a_1505_, v_a_1629_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1664_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_a_1636_ = lean_ctor_get(v___x_1634_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1638_ = v___x_1634_;
v_isShared_1639_ = v_isSharedCheck_1664_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1664_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_fst_1640_; lean_object* v_snd_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1663_; 
v_fst_1640_ = lean_ctor_get(v_a_1635_, 0);
v_snd_1641_ = lean_ctor_get(v_a_1635_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_a_1635_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1643_ = v_a_1635_;
v_isShared_1644_ = v_isSharedCheck_1663_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snd_1641_);
lean_inc(v_fst_1640_);
lean_dec(v_a_1635_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1663_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
size_t v___x_1645_; size_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_ptr_addr(v_type_1618_);
v___x_1646_ = lean_ptr_addr(v_fst_1625_);
v___x_1647_ = lean_usize_dec_eq(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_inc(v_declName_1617_);
lean_del_object(v___x_1643_);
lean_del_object(v___x_1638_);
lean_dec_ref_known(v_e_1501_, 4);
v___x_1648_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1617_, v_fst_1625_, v_fst_1630_, v_fst_1640_, v_nondep_1621_, v_snd_1641_, v_a_1504_, v_a_1505_, v_a_1636_);
return v___x_1648_;
}
else
{
size_t v___x_1649_; size_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1649_ = lean_ptr_addr(v_value_1619_);
v___x_1650_ = lean_ptr_addr(v_fst_1630_);
v___x_1651_ = lean_usize_dec_eq(v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_inc(v_declName_1617_);
lean_del_object(v___x_1643_);
lean_del_object(v___x_1638_);
lean_dec_ref_known(v_e_1501_, 4);
v___x_1652_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1617_, v_fst_1625_, v_fst_1630_, v_fst_1640_, v_nondep_1621_, v_snd_1641_, v_a_1504_, v_a_1505_, v_a_1636_);
return v___x_1652_;
}
else
{
size_t v___x_1653_; size_t v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = lean_ptr_addr(v_body_1620_);
v___x_1654_ = lean_ptr_addr(v_fst_1640_);
v___x_1655_ = lean_usize_dec_eq(v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_inc(v_declName_1617_);
lean_del_object(v___x_1643_);
lean_del_object(v___x_1638_);
lean_dec_ref_known(v_e_1501_, 4);
v___x_1656_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1617_, v_fst_1625_, v_fst_1630_, v_fst_1640_, v_nondep_1621_, v_snd_1641_, v_a_1504_, v_a_1505_, v_a_1636_);
return v___x_1656_;
}
else
{
lean_object* v___x_1658_; 
lean_dec(v_fst_1640_);
lean_dec(v_fst_1630_);
lean_dec(v_fst_1625_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_e_1501_);
v___x_1658_ = v___x_1643_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_e_1501_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_snd_1641_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1658_);
v___x_1660_ = v___x_1638_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_a_1636_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
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
lean_dec(v_fst_1630_);
lean_dec(v_fst_1625_);
lean_dec_ref_known(v_e_1501_, 4);
return v___x_1634_;
}
}
else
{
lean_dec(v_fst_1625_);
lean_dec_ref_known(v_e_1501_, 4);
lean_dec(v_offset_1502_);
return v___x_1627_;
}
}
else
{
lean_dec_ref_known(v_e_1501_, 4);
lean_dec(v_offset_1502_);
return v___x_1622_;
}
}
case 10:
{
lean_object* v_data_1665_; lean_object* v_expr_1666_; lean_object* v___x_1667_; 
v_data_1665_ = lean_ctor_get(v_e_1501_, 0);
v_expr_1666_ = lean_ctor_get(v_e_1501_, 1);
lean_inc_ref(v_expr_1666_);
v___x_1667_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_expr_1666_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1689_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_a_1669_ = lean_ctor_get(v___x_1667_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1671_ = v___x_1667_;
v_isShared_1672_ = v_isSharedCheck_1689_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1689_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_fst_1673_; lean_object* v_snd_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1688_; 
v_fst_1673_ = lean_ctor_get(v_a_1668_, 0);
v_snd_1674_ = lean_ctor_get(v_a_1668_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_a_1668_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1676_ = v_a_1668_;
v_isShared_1677_ = v_isSharedCheck_1688_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_snd_1674_);
lean_inc(v_fst_1673_);
lean_dec(v_a_1668_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1688_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
size_t v___x_1678_; size_t v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = lean_ptr_addr(v_expr_1666_);
v___x_1679_ = lean_ptr_addr(v_fst_1673_);
v___x_1680_ = lean_usize_dec_eq(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_inc(v_data_1665_);
lean_del_object(v___x_1676_);
lean_del_object(v___x_1671_);
lean_dec_ref_known(v_e_1501_, 2);
v___x_1681_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_data_1665_, v_fst_1673_, v_snd_1674_, v_a_1504_, v_a_1505_, v_a_1669_);
return v___x_1681_;
}
else
{
lean_object* v___x_1683_; 
lean_dec(v_fst_1673_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v_e_1501_);
v___x_1683_ = v___x_1676_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_e_1501_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_snd_1674_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1683_);
v___x_1685_ = v___x_1671_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1669_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1501_, 2);
return v___x_1667_;
}
}
case 11:
{
lean_object* v_typeName_1690_; lean_object* v_idx_1691_; lean_object* v_struct_1692_; lean_object* v___x_1693_; 
v_typeName_1690_ = lean_ctor_get(v_e_1501_, 0);
v_idx_1691_ = lean_ctor_get(v_e_1501_, 1);
v_struct_1692_ = lean_ctor_get(v_e_1501_, 2);
lean_inc_ref(v_struct_1692_);
v___x_1693_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_struct_1692_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1715_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_a_1695_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1697_ = v___x_1693_;
v_isShared_1698_ = v_isSharedCheck_1715_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1715_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_fst_1699_; lean_object* v_snd_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1714_; 
v_fst_1699_ = lean_ctor_get(v_a_1694_, 0);
v_snd_1700_ = lean_ctor_get(v_a_1694_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_a_1694_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1702_ = v_a_1694_;
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snd_1700_);
lean_inc(v_fst_1699_);
lean_dec(v_a_1694_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
size_t v___x_1704_; size_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_ptr_addr(v_struct_1692_);
v___x_1705_ = lean_ptr_addr(v_fst_1699_);
v___x_1706_ = lean_usize_dec_eq(v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_inc(v_idx_1691_);
lean_inc(v_typeName_1690_);
lean_del_object(v___x_1702_);
lean_del_object(v___x_1697_);
lean_dec_ref_known(v_e_1501_, 3);
v___x_1707_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_typeName_1690_, v_idx_1691_, v_fst_1699_, v_snd_1700_, v_a_1504_, v_a_1505_, v_a_1695_);
return v___x_1707_;
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_fst_1699_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v_e_1501_);
v___x_1709_ = v___x_1702_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_e_1501_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_snd_1700_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1709_);
v___x_1711_ = v___x_1697_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_a_1695_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1501_, 3);
return v___x_1693_;
}
}
default: 
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v_offset_1502_);
lean_dec_ref(v_e_1501_);
v___x_1716_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3);
v___x_1717_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v___x_1716_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1498_ = stack[0].m_obj;
lean_object* v_varDeps_1499_ = stack[1].m_obj;
lean_object* v_xs_1500_ = stack[2].m_obj;
lean_object* v_e_1501_ = stack[3].m_obj;
lean_object* v_offset_1502_ = stack[4].m_obj;
lean_object* v_a_1503_ = stack[5].m_obj;
uint8_t v_a_1504_ = stack[6].m_num;
lean_object* v_a_1505_ = stack[7].m_obj;
lean_object* v_a_1506_ = stack[8].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1498_, v_varDeps_1499_, v_xs_1500_, v_e_1501_, v_offset_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
stack->m_obj
 = v_res_1718_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(lean_object* v_n_1719_, lean_object* v_varDeps_1720_, lean_object* v_xs_1721_, lean_object* v_e_1722_, lean_object* v_offset_1723_, lean_object* v_a_1724_, uint8_t v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_key_1728_; lean_object* v_a_1730_; lean_object* v___x_1743_; 
lean_inc(v_offset_1723_);
lean_inc_ref(v_e_1722_);
v_key_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1728_, 0, v_e_1722_);
lean_ctor_set(v_key_1728_, 1, v_offset_1723_);
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_a_1724_, v_key_1728_);
if (lean_obj_tag(v___x_1743_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec_ref_known(v_key_1728_, 2);
lean_dec(v_offset_1723_);
lean_dec_ref(v_e_1722_);
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_val_1744_);
lean_ctor_set(v___x_1745_, 1, v_a_1724_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v_a_1727_);
return v___x_1746_;
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
lean_dec(v___x_1743_);
v___x_1747_ = l_Lean_Expr_looseBVarRange(v_e_1722_);
v___x_1748_ = lean_nat_dec_le(v___x_1747_, v_offset_1723_);
lean_dec(v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Expr_getAppFn(v_e_1722_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_deBruijnIndex_1750_; uint8_t v___x_1751_; 
v_deBruijnIndex_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_deBruijnIndex_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_nat_dec_le(v_offset_1723_, v_deBruijnIndex_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_deBruijnIndex_1750_);
lean_dec(v_offset_1723_);
v___x_1752_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_nat_add(v_offset_1723_, v_n_1719_);
v___x_1754_ = lean_nat_dec_lt(v_deBruijnIndex_1750_, v___x_1753_);
lean_dec(v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_offset_1723_);
lean_dec_ref(v_e_1722_);
v___x_1755_ = lean_nat_sub(v_deBruijnIndex_1750_, v_n_1719_);
lean_dec(v_deBruijnIndex_1750_);
v___x_1756_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1755_, v_a_1727_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v_a_1758_; lean_object* v___x_1759_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
v_a_1758_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1756_, 2);
v___x_1759_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_a_1757_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1758_);
return v___x_1759_;
}
else
{
lean_object* v_a_1760_; lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref_known(v_key_1728_, 2);
lean_dec_ref(v_a_1724_);
v_a_1760_ = lean_ctor_get(v___x_1756_, 0);
v_a_1761_ = lean_ctor_get(v___x_1756_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1756_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_inc(v_a_1760_);
lean_dec(v___x_1756_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1760_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_i_1773_; lean_object* v___x_1774_; lean_object* v_expectedNumArgs_1775_; lean_object* v_numArgs_1776_; uint8_t v___x_1777_; 
v___x_1769_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1770_ = lean_nat_sub(v_deBruijnIndex_1750_, v_offset_1723_);
lean_dec(v_deBruijnIndex_1750_);
v___x_1771_ = lean_nat_sub(v_n_1719_, v___x_1770_);
lean_dec(v___x_1770_);
v___x_1772_ = lean_unsigned_to_nat(1u);
v_i_1773_ = lean_nat_sub(v___x_1771_, v___x_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_array_get_borrowed(v___x_1769_, v_varDeps_1720_, v_i_1773_);
v_expectedNumArgs_1775_ = lean_array_get_size(v___x_1774_);
v_numArgs_1776_ = l_Lean_Expr_getAppNumArgs(v_e_1722_);
v___x_1777_ = lean_nat_dec_lt(v_expectedNumArgs_1775_, v_numArgs_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_nat_dec_eq(v_numArgs_1776_, v_expectedNumArgs_1775_);
lean_dec(v_numArgs_1776_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_i_1773_);
v___x_1779_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1780_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1779_, v_a_1725_, v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
if (lean_obj_tag(v_a_1781_) == 1)
{
lean_object* v_a_1782_; lean_object* v_val_1783_; lean_object* v___x_1784_; 
lean_inc_ref(v_a_1781_);
lean_dec(v_offset_1723_);
lean_dec_ref(v_e_1722_);
v_a_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1780_, 2);
v_val_1783_ = lean_ctor_get(v_a_1781_, 0);
lean_inc(v_val_1783_);
lean_dec_ref_known(v_a_1781_, 1);
v___x_1784_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_val_1783_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1782_);
return v___x_1784_;
}
else
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1780_, 2);
v_a_1730_ = v_a_1785_;
goto v___jp_1729_;
}
}
else
{
lean_object* v_a_1786_; lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref_known(v_key_1728_, 2);
lean_dec_ref(v_a_1724_);
lean_dec(v_offset_1723_);
lean_dec_ref(v_e_1722_);
v_a_1786_ = lean_ctor_get(v___x_1780_, 0);
v_a_1787_ = lean_ctor_get(v___x_1780_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1780_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_inc(v_a_1786_);
lean_dec(v___x_1780_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1786_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_offset_1723_);
lean_dec_ref(v_e_1722_);
v___x_1795_ = lean_array_fget_borrowed(v_xs_1721_, v_i_1773_);
lean_dec(v_i_1773_);
lean_inc(v___x_1795_);
v___x_1796_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v___x_1795_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v___x_1796_;
}
}
else
{
lean_dec(v_numArgs_1776_);
lean_dec(v_i_1773_);
v_a_1730_ = v_a_1727_;
goto v___jp_1729_;
}
}
}
}
else
{
lean_dec_ref(v___x_1749_);
v_a_1730_ = v_a_1727_;
goto v___jp_1729_;
}
}
else
{
lean_object* v___x_1797_; 
lean_dec(v_offset_1723_);
v___x_1797_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v___x_1797_;
}
}
v___jp_1729_:
{
switch(lean_obj_tag(v_e_1722_))
{
case 9:
{
lean_object* v___x_1731_; 
lean_dec(v_offset_1723_);
v___x_1731_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
return v___x_1731_;
}
case 2:
{
lean_object* v___x_1732_; 
lean_dec(v_offset_1723_);
v___x_1732_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
return v___x_1732_;
}
case 0:
{
lean_object* v___x_1733_; 
lean_dec(v_offset_1723_);
v___x_1733_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
return v___x_1733_;
}
case 1:
{
lean_object* v___x_1734_; 
lean_dec(v_offset_1723_);
v___x_1734_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
return v___x_1734_;
}
case 4:
{
lean_object* v___x_1735_; 
lean_dec(v_offset_1723_);
v___x_1735_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
return v___x_1735_;
}
case 3:
{
lean_object* v___x_1736_; 
lean_dec(v_offset_1723_);
v___x_1736_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_e_1722_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
return v___x_1736_;
}
default: 
{
lean_object* v___x_1737_; 
v___x_1737_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1719_, v_varDeps_1720_, v_xs_1721_, v_e_1722_, v_offset_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1730_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v_a_1739_; lean_object* v_fst_1740_; lean_object* v_snd_1741_; lean_object* v___x_1742_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 1);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1737_, 2);
v_fst_1740_ = lean_ctor_get(v_a_1738_, 0);
lean_inc(v_fst_1740_);
v_snd_1741_ = lean_ctor_get(v_a_1738_, 1);
lean_inc(v_snd_1741_);
lean_dec(v_a_1738_);
v___x_1742_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1728_, v_fst_1740_, v_snd_1741_, v_a_1725_, v_a_1726_, v_a_1739_);
return v___x_1742_;
}
else
{
lean_dec_ref_known(v_key_1728_, 2);
return v___x_1737_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1719_ = stack[0].m_obj;
lean_object* v_varDeps_1720_ = stack[1].m_obj;
lean_object* v_xs_1721_ = stack[2].m_obj;
lean_object* v_e_1722_ = stack[3].m_obj;
lean_object* v_offset_1723_ = stack[4].m_obj;
lean_object* v_a_1724_ = stack[5].m_obj;
uint8_t v_a_1725_ = stack[6].m_num;
lean_object* v_a_1726_ = stack[7].m_obj;
lean_object* v_a_1727_ = stack[8].m_obj;
lean_object* v_res_1798_;
v_res_1798_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1719_, v_varDeps_1720_, v_xs_1721_, v_e_1722_, v_offset_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
stack->m_obj
 = v_res_1798_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___boxed(lean_object* v_n_1799_, lean_object* v_varDeps_1800_, lean_object* v_xs_1801_, lean_object* v_e_1802_, lean_object* v_offset_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
uint8_t v_a_boxed_1808_; lean_object* v_res_1809_; 
v_a_boxed_1808_ = lean_unbox(v_a_1805_);
v_res_1809_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1799_, v_varDeps_1800_, v_xs_1801_, v_e_1802_, v_offset_1803_, v_a_1804_, v_a_boxed_1808_, v_a_1806_, v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_xs_1801_);
lean_dec_ref(v_varDeps_1800_);
lean_dec(v_n_1799_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_n_1810_, lean_object* v_varDeps_1811_, lean_object* v_xs_1812_, lean_object* v_e_1813_, lean_object* v_offset_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
uint8_t v_a_boxed_1819_; lean_object* v_res_1820_; 
v_a_boxed_1819_ = lean_unbox(v_a_1816_);
v_res_1820_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1810_, v_varDeps_1811_, v_xs_1812_, v_e_1813_, v_offset_1814_, v_a_1815_, v_a_boxed_1819_, v_a_1817_, v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec_ref(v_xs_1812_);
lean_dec_ref(v_varDeps_1811_);
lean_dec(v_n_1810_);
return v_res_1820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = lean_unsigned_to_nat(16u);
v___x_1823_ = lean_mk_array(v___x_1822_, v___x_1821_);
return v___x_1823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
return v___x_1826_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object* v_e_1827_, lean_object* v_n_1828_, lean_object* v_varDeps_1829_, lean_object* v_xs_1830_, uint8_t v_debug_1831_, lean_object* v___x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v_a_1837_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l_Lean_Expr_looseBVarRange(v_e_1827_);
v___x_1866_ = lean_nat_dec_le(v___x_1865_, v___x_1835_);
lean_dec(v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Expr_getAppFn(v_e_1827_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_deBruijnIndex_1868_; uint8_t v___x_1869_; 
v_deBruijnIndex_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_deBruijnIndex_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = lean_nat_dec_le(v___x_1835_, v_deBruijnIndex_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_dec(v_deBruijnIndex_1868_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_e_1827_);
lean_ctor_set(v___x_1870_, 1, v___y_1834_);
return v___x_1870_;
}
else
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_nat_dec_lt(v_deBruijnIndex_1868_, v_n_1828_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec_ref(v_e_1827_);
v___x_1872_ = lean_nat_sub(v_deBruijnIndex_1868_, v_n_1828_);
lean_dec(v_deBruijnIndex_1868_);
v___x_1873_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1872_, v___y_1834_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_i_1876_; lean_object* v___x_1877_; lean_object* v_expectedNumArgs_1878_; lean_object* v_numArgs_1879_; uint8_t v___x_1880_; 
v___x_1874_ = lean_nat_sub(v_n_1828_, v_deBruijnIndex_1868_);
lean_dec(v_deBruijnIndex_1868_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v_i_1876_ = lean_nat_sub(v___x_1874_, v___x_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_array_get_borrowed(v___x_1832_, v_varDeps_1829_, v_i_1876_);
v_expectedNumArgs_1878_ = lean_array_get_size(v___x_1877_);
v_numArgs_1879_ = l_Lean_Expr_getAppNumArgs(v_e_1827_);
v___x_1880_ = lean_nat_dec_lt(v_expectedNumArgs_1878_, v_numArgs_1879_);
if (v___x_1880_ == 0)
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_nat_dec_eq(v_numArgs_1879_, v_expectedNumArgs_1878_);
lean_dec(v_numArgs_1879_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_i_1876_);
v___x_1882_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1883_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1882_, v_debug_1831_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
if (lean_obj_tag(v_a_1884_) == 1)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1893_; 
lean_inc_ref(v_a_1884_);
lean_dec_ref(v_e_1827_);
v_a_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1883_, 0);
lean_dec(v_unused_1894_);
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_val_1889_; lean_object* v___x_1891_; 
v_val_1889_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_val_1889_);
lean_dec_ref_known(v_a_1884_, 1);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_val_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_val_1889_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_a_1885_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1895_; 
v_a_1895_ = lean_ctor_get(v___x_1883_, 1);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1883_, 2);
v_a_1837_ = v_a_1895_;
goto v___jp_1836_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_e_1827_);
v_a_1896_ = lean_ctor_get(v___x_1883_, 0);
v_a_1897_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1883_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_inc(v_a_1896_);
lean_dec(v___x_1883_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec_ref(v_e_1827_);
v___x_1905_ = lean_array_fget_borrowed(v_xs_1830_, v_i_1876_);
lean_dec(v_i_1876_);
lean_inc(v___x_1905_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___y_1834_);
return v___x_1906_;
}
}
else
{
lean_dec(v_numArgs_1879_);
lean_dec(v_i_1876_);
v_a_1837_ = v___y_1834_;
goto v___jp_1836_;
}
}
}
}
else
{
lean_dec_ref(v___x_1867_);
v_a_1837_ = v___y_1834_;
goto v___jp_1836_;
}
}
else
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_e_1827_);
lean_ctor_set(v___x_1907_, 1, v___y_1834_);
return v___x_1907_;
}
v___jp_1836_:
{
switch(lean_obj_tag(v_e_1827_))
{
case 9:
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_e_1827_);
lean_ctor_set(v___x_1838_, 1, v_a_1837_);
return v___x_1838_;
}
case 2:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_e_1827_);
lean_ctor_set(v___x_1839_, 1, v_a_1837_);
return v___x_1839_;
}
case 0:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_e_1827_);
lean_ctor_set(v___x_1840_, 1, v_a_1837_);
return v___x_1840_;
}
case 1:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_e_1827_);
lean_ctor_set(v___x_1841_, 1, v_a_1837_);
return v___x_1841_;
}
case 4:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_e_1827_);
lean_ctor_set(v___x_1842_, 1, v_a_1837_);
return v___x_1842_;
}
case 3:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_e_1827_);
lean_ctor_set(v___x_1843_, 1, v_a_1837_);
return v___x_1843_;
}
default: 
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1);
v___x_1845_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1828_, v_varDeps_1829_, v_xs_1830_, v_e_1827_, v___x_1835_, v___x_1844_, v_debug_1831_, v___y_1833_, v_a_1837_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_a_1847_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1849_ = v___x_1845_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_fst_1851_; lean_object* v___x_1853_; 
v_fst_1851_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_fst_1851_);
lean_dec(v_a_1846_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_fst_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_fst_1851_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_a_1847_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_a_1856_ = lean_ctor_get(v___x_1845_, 0);
v_a_1857_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1845_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_inc(v_a_1856_);
lean_dec(v___x_1845_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1856_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1827_ = stack[0].m_obj;
lean_object* v_n_1828_ = stack[1].m_obj;
lean_object* v_varDeps_1829_ = stack[2].m_obj;
lean_object* v_xs_1830_ = stack[3].m_obj;
uint8_t v_debug_1831_ = stack[4].m_num;
lean_object* v___x_1832_ = stack[5].m_obj;
lean_object* v___y_1833_ = stack[6].m_obj;
lean_object* v___y_1834_ = stack[7].m_obj;
lean_object* v_res_1908_;
v_res_1908_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(v_e_1827_, v_n_1828_, v_varDeps_1829_, v_xs_1830_, v_debug_1831_, v___x_1832_, v___y_1833_, v___y_1834_);
stack->m_obj
 = v_res_1908_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object* v_e_1909_, lean_object* v_n_1910_, lean_object* v_varDeps_1911_, lean_object* v_xs_1912_, lean_object* v_debug_1913_, lean_object* v___x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
uint8_t v_debug_boxed_1917_; lean_object* v_res_1918_; 
v_debug_boxed_1917_ = lean_unbox(v_debug_1913_);
v_res_1918_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(v_e_1909_, v_n_1910_, v_varDeps_1911_, v_xs_1912_, v_debug_boxed_1917_, v___x_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec_ref(v___x_1914_);
lean_dec_ref(v_xs_1912_);
lean_dec_ref(v_varDeps_1911_);
lean_dec(v_n_1910_);
return v_res_1918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1921_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1922_ = lean_unsigned_to_nat(16u);
v___x_1923_ = lean_unsigned_to_nat(62u);
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1));
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0));
v___x_1926_ = l_mkPanicMessageWithDecl(v___x_1925_, v___x_1924_, v___x_1923_, v___x_1922_, v___x_1921_);
return v___x_1926_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1927_, lean_object* v_xs_1928_, lean_object* v_varDeps_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v_n_1938_; lean_object* v___x_1939_; uint8_t v_debug_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v_env_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1937_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v_n_1938_ = lean_array_get_size(v_xs_1928_);
v___x_1939_ = lean_st_ref_get(v_a_1931_);
v_debug_1940_ = lean_ctor_get_uint8(v___x_1939_, sizeof(void*)*12);
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(v_debug_1940_);
v___f_1942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1942_, 0, v_e_1927_);
lean_closure_set(v___f_1942_, 1, v_n_1938_);
lean_closure_set(v___f_1942_, 2, v_varDeps_1929_);
lean_closure_set(v___f_1942_, 3, v_xs_1928_);
lean_closure_set(v___f_1942_, 4, v___x_1941_);
lean_closure_set(v___f_1942_, 5, v___x_1937_);
v___x_1943_ = lean_st_ref_get(v_a_1935_);
v_env_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc_ref(v_env_1944_);
lean_dec(v___x_1943_);
v___x_1945_ = 0;
v___x_1946_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1946_, 0, v_env_1944_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*1, v___x_1945_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*1 + 1, v___x_1945_);
v___x_1947_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1942_, v___x_1946_, v_a_1931_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1958_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1958_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1958_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
if (lean_obj_tag(v_a_1948_) == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec_ref_known(v_a_1948_, 1);
lean_del_object(v___x_1950_);
v___x_1952_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2);
v___x_1953_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_1952_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_1953_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; 
v_a_1954_ = lean_ctor_get(v_a_1948_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v_a_1948_, 1);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v_a_1954_);
v___x_1956_ = v___x_1950_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1947_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1947_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1927_ = stack[0].m_obj;
lean_object* v_xs_1928_ = stack[1].m_obj;
lean_object* v_varDeps_1929_ = stack[2].m_obj;
lean_object* v_a_1930_ = stack[3].m_obj;
lean_object* v_a_1931_ = stack[4].m_obj;
lean_object* v_a_1932_ = stack[5].m_obj;
lean_object* v_a_1933_ = stack[6].m_obj;
lean_object* v_a_1934_ = stack[7].m_obj;
lean_object* v_a_1935_ = stack[8].m_obj;
lean_object* v_res_1967_;
v_res_1967_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1927_, v_xs_1928_, v_varDeps_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
stack->m_obj
 = v_res_1967_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1968_, lean_object* v_xs_1969_, lean_object* v_varDeps_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1968_, v_xs_1969_, v_varDeps_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_1979_, lean_object* v_m_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1980_, v_a_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1983_, lean_object* v_m_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(v_00_u03b2_1983_, v_m_1984_, v_a_1985_);
lean_dec_ref(v_a_1985_);
lean_dec_ref(v_m_1984_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_1987_, lean_object* v_a_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1988_, v_x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1991_, lean_object* v_a_1992_, lean_object* v_x_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_1991_, v_a_1992_, v_x_1993_);
lean_dec(v_x_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1994_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1995_, lean_object* v_type_1996_, lean_object* v_val_1997_, lean_object* v_k_1998_, uint8_t v_nondep_1999_, uint8_t v_kind_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___f_2008_; lean_object* v___x_2009_; 
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2008_, 0, v_k_1998_);
lean_closure_set(v___f_2008_, 1, v___y_2001_);
lean_closure_set(v___f_2008_, 2, v___y_2002_);
v___x_2009_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1995_, v_type_1996_, v_val_1997_, v___f_2008_, v_nondep_1999_, v_kind_2000_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2009_) == 0)
{
return v___x_2009_;
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1995_ = stack[0].m_obj;
lean_object* v_type_1996_ = stack[1].m_obj;
lean_object* v_val_1997_ = stack[2].m_obj;
lean_object* v_k_1998_ = stack[3].m_obj;
uint8_t v_nondep_1999_ = stack[4].m_num;
uint8_t v_kind_2000_ = stack[5].m_num;
lean_object* v___y_2001_ = stack[6].m_obj;
lean_object* v___y_2002_ = stack[7].m_obj;
lean_object* v___y_2003_ = stack[8].m_obj;
lean_object* v___y_2004_ = stack[9].m_obj;
lean_object* v___y_2005_ = stack[10].m_obj;
lean_object* v___y_2006_ = stack[11].m_obj;
lean_object* v_res_2018_;
v_res_2018_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1995_, v_type_1996_, v_val_1997_, v_k_1998_, v_nondep_1999_, v_kind_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
stack->m_obj
 = v_res_2018_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_2019_, lean_object* v_type_2020_, lean_object* v_val_2021_, lean_object* v_k_2022_, lean_object* v_nondep_2023_, lean_object* v_kind_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
uint8_t v_nondep_boxed_2032_; uint8_t v_kind_boxed_2033_; lean_object* v_res_2034_; 
v_nondep_boxed_2032_ = lean_unbox(v_nondep_2023_);
v_kind_boxed_2033_ = lean_unbox(v_kind_2024_);
v_res_2034_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_2019_, v_type_2020_, v_val_2021_, v_k_2022_, v_nondep_boxed_2032_, v_kind_boxed_2033_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2034_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_2035_, lean_object* v_name_2036_, lean_object* v_type_2037_, lean_object* v_val_2038_, lean_object* v_k_2039_, uint8_t v_nondep_2040_, uint8_t v_kind_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_2036_, v_type_2037_, v_val_2038_, v_k_2039_, v_nondep_2040_, v_kind_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2036_ = stack[1].m_obj;
lean_object* v_type_2037_ = stack[2].m_obj;
lean_object* v_val_2038_ = stack[3].m_obj;
lean_object* v_k_2039_ = stack[4].m_obj;
uint8_t v_nondep_2040_ = stack[5].m_num;
uint8_t v_kind_2041_ = stack[6].m_num;
lean_object* v___y_2042_ = stack[7].m_obj;
lean_object* v___y_2043_ = stack[8].m_obj;
lean_object* v___y_2044_ = stack[9].m_obj;
lean_object* v___y_2045_ = stack[10].m_obj;
lean_object* v___y_2046_ = stack[11].m_obj;
lean_object* v___y_2047_ = stack[12].m_obj;
lean_object* v_res_2050_;
v_res_2050_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_box(0), v_name_2036_, v_type_2037_, v_val_2038_, v_k_2039_, v_nondep_2040_, v_kind_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
stack->m_obj
 = v_res_2050_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_2051_, lean_object* v_name_2052_, lean_object* v_type_2053_, lean_object* v_val_2054_, lean_object* v_k_2055_, lean_object* v_nondep_2056_, lean_object* v_kind_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
uint8_t v_nondep_boxed_2065_; uint8_t v_kind_boxed_2066_; lean_object* v_res_2067_; 
v_nondep_boxed_2065_ = lean_unbox(v_nondep_2056_);
v_kind_boxed_2066_ = lean_unbox(v_kind_2057_);
v_res_2067_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_2051_, v_name_2052_, v_type_2053_, v_val_2054_, v_k_2055_, v_nondep_boxed_2065_, v_kind_boxed_2066_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2067_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_2068_, size_t v_sz_2069_, size_t v_i_2070_, lean_object* v_bs_2071_){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
if (v___x_2072_ == 0)
{
return v_bs_2071_;
}
else
{
lean_object* v___x_2073_; lean_object* v_v_2074_; lean_object* v___x_2075_; lean_object* v_bs_x27_2076_; lean_object* v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2073_ = l_Lean_instInhabitedExpr;
v_v_2074_ = lean_array_uget(v_bs_2071_, v_i_2070_);
v___x_2075_ = lean_unsigned_to_nat(0u);
v_bs_x27_2076_ = lean_array_uset(v_bs_2071_, v_i_2070_, v___x_2075_);
v___x_2077_ = lean_array_get_borrowed(v___x_2073_, v_xs_2068_, v_v_2074_);
lean_dec(v_v_2074_);
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2070_, v___x_2078_);
lean_inc(v___x_2077_);
v___x_2080_ = lean_array_uset(v_bs_x27_2076_, v_i_2070_, v___x_2077_);
v_i_2070_ = v___x_2079_;
v_bs_2071_ = v___x_2080_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2068_ = stack[0].m_obj;
size_t v_sz_2069_ = stack[1].m_num;
size_t v_i_2070_ = stack[2].m_num;
lean_object* v_bs_2071_ = stack[3].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2068_, v_sz_2069_, v_i_2070_, v_bs_2071_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_2083_, lean_object* v_sz_2084_, lean_object* v_i_2085_, lean_object* v_bs_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2084_);
lean_dec(v_sz_2084_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2083_, v_sz_boxed_2087_, v_i_boxed_2088_, v_bs_2086_);
lean_dec_ref(v_xs_2083_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_2090_, lean_object* v_i_2091_, lean_object* v_varDeps_2092_, lean_object* v_args_2093_, lean_object* v_body_2094_, lean_object* v_x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_2090_, v_i_2091_, v_varDeps_2092_, v_args_2093_, v_body_2094_, v_x_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_i_2091_);
return v_res_2103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2105_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2106_ = lean_unsigned_to_nat(30u);
v___x_2107_ = lean_unsigned_to_nat(254u);
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2110_ = l_mkPanicMessageWithDecl(v___x_2109_, v___x_2108_, v___x_2107_, v___x_2106_, v___x_2105_);
return v___x_2110_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_2111_, lean_object* v_args_2112_, lean_object* v_f_2113_, lean_object* v_xs_2114_, lean_object* v_i_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = lean_array_get_size(v_args_2112_);
v___x_2124_ = lean_nat_dec_lt(v_i_2115_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_dec(v_i_2115_);
lean_dec_ref(v_args_2112_);
lean_inc_ref(v_xs_2114_);
v___x_2125_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_f_2113_, v_xs_2114_, v_varDeps_2111_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = 1;
v___x_2128_ = l_Lean_Meta_mkLetFVars(v_xs_2114_, v_a_2126_, v___x_2124_, v___x_2124_, v___x_2127_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec_ref(v_xs_2114_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_Meta_Sym_shareCommonInc(v_a_2129_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2130_;
}
else
{
return v___x_2128_;
}
}
else
{
lean_dec_ref(v_xs_2114_);
return v___x_2125_;
}
}
else
{
if (lean_obj_tag(v_f_2113_) == 6)
{
lean_object* v_binderName_2131_; lean_object* v_binderType_2132_; lean_object* v_body_2133_; lean_object* v___f_2134_; lean_object* v_varPos_2135_; size_t v_sz_2136_; size_t v___x_2137_; lean_object* v_ys_2138_; lean_object* v___x_2139_; lean_object* v_type_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_binderName_2131_ = lean_ctor_get(v_f_2113_, 0);
lean_inc(v_binderName_2131_);
v_binderType_2132_ = lean_ctor_get(v_f_2113_, 1);
lean_inc_ref(v_binderType_2132_);
v_body_2133_ = lean_ctor_get(v_f_2113_, 2);
lean_inc_ref(v_body_2133_);
lean_dec_ref_known(v_f_2113_, 3);
lean_inc_ref(v_args_2112_);
lean_inc_ref(v_varDeps_2111_);
lean_inc(v_i_2115_);
lean_inc_ref(v_xs_2114_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2134_, 0, v_xs_2114_);
lean_closure_set(v___f_2134_, 1, v_i_2115_);
lean_closure_set(v___f_2134_, 2, v_varDeps_2111_);
lean_closure_set(v___f_2134_, 3, v_args_2112_);
lean_closure_set(v___f_2134_, 4, v_body_2133_);
v_varPos_2135_ = lean_array_fget(v_varDeps_2111_, v_i_2115_);
lean_dec_ref(v_varDeps_2111_);
v_sz_2136_ = lean_array_size(v_varPos_2135_);
v___x_2137_ = ((size_t)0ULL);
lean_inc(v_varPos_2135_);
v_ys_2138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2114_, v_sz_2136_, v___x_2137_, v_varPos_2135_);
lean_dec_ref(v_xs_2114_);
v___x_2139_ = lean_array_get_size(v_varPos_2135_);
lean_dec(v_varPos_2135_);
v_type_2140_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_2132_, v___x_2139_);
v___x_2141_ = lean_array_fget(v_args_2112_, v_i_2115_);
lean_dec(v_i_2115_);
lean_dec_ref(v_args_2112_);
v___x_2142_ = l_Lean_Expr_beta(v___x_2141_, v_ys_2138_);
v___x_2143_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2142_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = 0;
v___x_2146_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_2131_, v_type_2140_, v_a_2144_, v___f_2134_, v___x_2124_, v___x_2145_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2146_;
}
else
{
lean_dec_ref(v_type_2140_);
lean_dec_ref(v___f_2134_);
lean_dec(v_binderName_2131_);
return v___x_2143_;
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v_i_2115_);
lean_dec_ref(v_xs_2114_);
lean_dec_ref(v_f_2113_);
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_varDeps_2111_);
v___x_2147_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_2148_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2147_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2148_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_varDeps_2111_ = stack[0].m_obj;
lean_object* v_args_2112_ = stack[1].m_obj;
lean_object* v_f_2113_ = stack[2].m_obj;
lean_object* v_xs_2114_ = stack[3].m_obj;
lean_object* v_i_2115_ = stack[4].m_obj;
lean_object* v_a_2116_ = stack[5].m_obj;
lean_object* v_a_2117_ = stack[6].m_obj;
lean_object* v_a_2118_ = stack[7].m_obj;
lean_object* v_a_2119_ = stack[8].m_obj;
lean_object* v_a_2120_ = stack[9].m_obj;
lean_object* v_a_2121_ = stack[10].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2111_, v_args_2112_, v_f_2113_, v_xs_2114_, v_i_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
stack->m_obj
 = v_res_2149_;
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_2150_, lean_object* v_i_2151_, lean_object* v_varDeps_2152_, lean_object* v_args_2153_, lean_object* v_body_2154_, lean_object* v_x_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Meta_Sym_shareCommonInc(v_x_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2165_ = lean_array_push(v_xs_2150_, v_a_2164_);
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v_i_2151_, v___x_2166_);
v___x_2168_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2152_, v_args_2153_, v_body_2154_, v___x_2165_, v___x_2167_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
return v___x_2168_;
}
else
{
lean_dec_ref(v_body_2154_);
lean_dec_ref(v_args_2153_);
lean_dec_ref(v_varDeps_2152_);
lean_dec_ref(v_xs_2150_);
return v___x_2163_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2150_ = stack[0].m_obj;
lean_object* v_i_2151_ = stack[1].m_obj;
lean_object* v_varDeps_2152_ = stack[2].m_obj;
lean_object* v_args_2153_ = stack[3].m_obj;
lean_object* v_body_2154_ = stack[4].m_obj;
lean_object* v_x_2155_ = stack[5].m_obj;
lean_object* v___y_2156_ = stack[6].m_obj;
lean_object* v___y_2157_ = stack[7].m_obj;
lean_object* v___y_2158_ = stack[8].m_obj;
lean_object* v___y_2159_ = stack[9].m_obj;
lean_object* v___y_2160_ = stack[10].m_obj;
lean_object* v___y_2161_ = stack[11].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_2150_, v_i_2151_, v_varDeps_2152_, v_args_2153_, v_body_2154_, v_x_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_2170_, lean_object* v_args_2171_, lean_object* v_f_2172_, lean_object* v_xs_2173_, lean_object* v_i_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2170_, v_args_2171_, v_f_2172_, v_xs_2173_, v_i_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
return v_res_2182_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_2183_, lean_object* v_args_2184_, lean_object* v___h_2185_, lean_object* v_f_2186_, lean_object* v_xs_2187_, lean_object* v_i_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2183_, v_args_2184_, v_f_2186_, v_xs_2187_, v_i_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_varDeps_2183_ = stack[0].m_obj;
lean_object* v_args_2184_ = stack[1].m_obj;
lean_object* v_f_2186_ = stack[3].m_obj;
lean_object* v_xs_2187_ = stack[4].m_obj;
lean_object* v_i_2188_ = stack[5].m_obj;
lean_object* v_a_2189_ = stack[6].m_obj;
lean_object* v_a_2190_ = stack[7].m_obj;
lean_object* v_a_2191_ = stack[8].m_obj;
lean_object* v_a_2192_ = stack[9].m_obj;
lean_object* v_a_2193_ = stack[10].m_obj;
lean_object* v_a_2194_ = stack[11].m_obj;
lean_object* v_res_2197_;
v_res_2197_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2183_, v_args_2184_, lean_box(0), v_f_2186_, v_xs_2187_, v_i_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
stack->m_obj
 = v_res_2197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_2198_, lean_object* v_args_2199_, lean_object* v___h_2200_, lean_object* v_f_2201_, lean_object* v_xs_2202_, lean_object* v_i_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2198_, v_args_2199_, v___h_2200_, v_f_2201_, v_xs_2202_, v_i_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2211_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2214_ = lean_unsigned_to_nat(40u);
v___x_2215_ = lean_unsigned_to_nat(251u);
v___x_2216_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_2217_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2218_ = l_mkPanicMessageWithDecl(v___x_2217_, v___x_2216_, v___x_2215_, v___x_2214_, v___x_2213_);
return v___x_2218_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
if (lean_obj_tag(v_x_2220_) == 5)
{
lean_object* v_fn_2230_; lean_object* v_arg_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_fn_2230_ = lean_ctor_get(v_x_2220_, 0);
lean_inc_ref(v_fn_2230_);
v_arg_2231_ = lean_ctor_get(v_x_2220_, 1);
lean_inc_ref(v_arg_2231_);
lean_dec_ref_known(v_x_2220_, 2);
v___x_2232_ = lean_array_set(v_x_2221_, v_x_2222_, v_arg_2231_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_sub(v_x_2222_, v___x_2233_);
lean_dec(v_x_2222_);
v_x_2220_ = v_fn_2230_;
v_x_2221_ = v___x_2232_;
v_x_2222_ = v___x_2234_;
goto _start;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
lean_dec(v_x_2222_);
v___x_2236_ = lean_array_get_size(v_x_2221_);
v___x_2237_ = lean_array_get_size(v_varDeps_2219_);
v___x_2238_ = lean_nat_dec_eq(v___x_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_x_2221_);
lean_dec_ref(v_x_2220_);
lean_dec_ref(v_varDeps_2219_);
v___x_2239_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2240_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2239_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2243_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2219_, v_x_2221_, v_x_2220_, v___x_2242_, v___x_2241_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2243_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_varDeps_2219_ = stack[0].m_obj;
lean_object* v_x_2220_ = stack[1].m_obj;
lean_object* v_x_2221_ = stack[2].m_obj;
lean_object* v_x_2222_ = stack[3].m_obj;
lean_object* v___y_2223_ = stack[4].m_obj;
lean_object* v___y_2224_ = stack[5].m_obj;
lean_object* v___y_2225_ = stack[6].m_obj;
lean_object* v___y_2226_ = stack[7].m_obj;
lean_object* v___y_2227_ = stack[8].m_obj;
lean_object* v___y_2228_ = stack[9].m_obj;
lean_object* v_res_2244_;
v_res_2244_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2219_, v_x_2220_, v_x_2221_, v_x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
stack->m_obj
 = v_res_2244_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2245_, lean_object* v_x_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2245_, v_x_2246_, v_x_2247_, v_x_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2257_; lean_object* v_dummy_2258_; 
v___x_2257_ = lean_box(0);
v_dummy_2258_ = l_Lean_Expr_sort___override(v___x_2257_);
return v_dummy_2258_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2259_, lean_object* v_varDeps_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_dummy_2268_; lean_object* v_nargs_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_dummy_2268_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2269_ = l_Lean_Expr_getAppNumArgs(v_e_2259_);
lean_inc(v_nargs_2269_);
v___x_2270_ = lean_mk_array(v_nargs_2269_, v_dummy_2268_);
v___x_2271_ = lean_unsigned_to_nat(1u);
v___x_2272_ = lean_nat_sub(v_nargs_2269_, v___x_2271_);
lean_dec(v_nargs_2269_);
v___x_2273_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2260_, v_e_2259_, v___x_2270_, v___x_2272_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
return v___x_2273_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2259_ = stack[0].m_obj;
lean_object* v_varDeps_2260_ = stack[1].m_obj;
lean_object* v_a_2261_ = stack[2].m_obj;
lean_object* v_a_2262_ = stack[3].m_obj;
lean_object* v_a_2263_ = stack[4].m_obj;
lean_object* v_a_2264_ = stack[5].m_obj;
lean_object* v_a_2265_ = stack[6].m_obj;
lean_object* v_a_2266_ = stack[7].m_obj;
lean_object* v_res_2274_;
v_res_2274_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2259_, v_varDeps_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
stack->m_obj
 = v_res_2274_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2275_, lean_object* v_varDeps_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2275_, v_varDeps_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
return v_res_2284_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_snd_2288_; lean_object* v_fst_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2322_; 
v_snd_2288_ = lean_ctor_get(v_a_2286_, 1);
v_fst_2289_ = lean_ctor_get(v_a_2286_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2286_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2291_ = v_a_2286_;
v_isShared_2292_ = v_isSharedCheck_2322_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_snd_2288_);
lean_inc(v_fst_2289_);
lean_dec(v_a_2286_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2322_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_fst_2293_; lean_object* v_snd_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2321_; 
v_fst_2293_ = lean_ctor_get(v_snd_2288_, 0);
v_snd_2294_ = lean_ctor_get(v_snd_2288_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_snd_2288_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2296_ = v_snd_2288_;
v_isShared_2297_ = v_isSharedCheck_2321_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_snd_2294_);
lean_inc(v_fst_2293_);
lean_dec(v_snd_2288_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2321_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_nat_dec_lt(v___x_2298_, v_fst_2293_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2301_; 
if (v_isShared_2297_ == 0)
{
v___x_2301_ = v___x_2296_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_fst_2293_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_snd_2294_);
v___x_2301_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2303_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v___x_2301_);
v___x_2303_ = v___x_2291_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_fst_2289_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = lean_unsigned_to_nat(1u);
v___x_2309_ = lean_nat_sub(v_fst_2293_, v___x_2308_);
lean_dec(v_fst_2293_);
v___x_2310_ = lean_array_get_borrowed(v___x_2307_, v_argUnivs_2285_, v___x_2309_);
lean_inc(v___x_2310_);
v___x_2311_ = l_Lean_mkLevelIMax_x27(v___x_2310_, v_fst_2289_);
v___x_2312_ = l_Lean_Level_normalize(v___x_2311_);
lean_dec(v___x_2311_);
lean_inc(v___x_2312_);
v___x_2313_ = lean_array_push(v_snd_2294_, v___x_2312_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2313_);
lean_ctor_set(v___x_2296_, 0, v___x_2309_);
v___x_2315_ = v___x_2296_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2317_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v___x_2315_);
lean_ctor_set(v___x_2291_, 0, v___x_2312_);
v___x_2317_ = v___x_2291_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
v_a_2286_ = v___x_2317_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_argUnivs_2285_ = stack[0].m_obj;
lean_object* v_a_2286_ = stack[1].m_obj;
lean_object* v_res_2323_;
v_res_2323_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2285_, v_a_2286_);
stack->m_obj
 = v_res_2323_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2324_, lean_object* v_a_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2324_, v_a_2325_);
lean_dec_ref(v_argUnivs_2324_);
return v_res_2327_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2330_, lean_object* v_argUnivs_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
if (lean_obj_tag(v_type_2330_) == 7)
{
lean_object* v_binderType_2339_; lean_object* v_body_2340_; lean_object* v___x_2341_; 
v_binderType_2339_ = lean_ctor_get(v_type_2330_, 1);
lean_inc_ref(v_binderType_2339_);
v_body_2340_ = lean_ctor_get(v_type_2330_, 2);
lean_inc_ref(v_body_2340_);
lean_dec_ref_known(v_type_2330_, 3);
v___x_2341_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2339_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = lean_array_push(v_argUnivs_2331_, v_a_2342_);
v_type_2330_ = v_body_2340_;
v_argUnivs_2331_ = v___x_2343_;
goto _start;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_body_2340_);
lean_dec_ref(v_argUnivs_2331_);
v_a_2345_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2341_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2341_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2330_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = lean_array_get_size(v_argUnivs_2331_);
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_a_2354_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2331_, v___x_2358_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2378_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2378_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2378_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_snd_2364_; lean_object* v_snd_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2376_; 
v_snd_2364_ = lean_ctor_get(v_a_2360_, 1);
lean_inc(v_snd_2364_);
lean_dec(v_a_2360_);
v_snd_2365_ = lean_ctor_get(v_snd_2364_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_snd_2364_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_snd_2364_, 0);
lean_dec(v_unused_2377_);
v___x_2367_ = v_snd_2364_;
v_isShared_2368_ = v_isSharedCheck_2376_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_snd_2365_);
lean_dec(v_snd_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2376_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = l_Array_reverse___redArg(v_snd_2365_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 1, v___x_2369_);
lean_ctor_set(v___x_2367_, 0, v_argUnivs_2331_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_argUnivs_2331_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2371_);
v___x_2373_ = v___x_2362_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v_argUnivs_2331_);
v_a_2379_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2359_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2359_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v_argUnivs_2331_);
v_a_2387_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2353_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2353_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2330_ = stack[0].m_obj;
lean_object* v_argUnivs_2331_ = stack[1].m_obj;
lean_object* v_a_2332_ = stack[2].m_obj;
lean_object* v_a_2333_ = stack[3].m_obj;
lean_object* v_a_2334_ = stack[4].m_obj;
lean_object* v_a_2335_ = stack[5].m_obj;
lean_object* v_a_2336_ = stack[6].m_obj;
lean_object* v_a_2337_ = stack[7].m_obj;
lean_object* v_res_2395_;
v_res_2395_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2330_, v_argUnivs_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
stack->m_obj
 = v_res_2395_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2396_, lean_object* v_argUnivs_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2396_, v_argUnivs_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2405_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2406_, lean_object* v_inst_2407_, lean_object* v_a_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2406_, v_a_2408_);
return v___x_2416_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_argUnivs_2406_ = stack[0].m_obj;
lean_object* v_a_2408_ = stack[2].m_obj;
lean_object* v___y_2409_ = stack[3].m_obj;
lean_object* v___y_2410_ = stack[4].m_obj;
lean_object* v___y_2411_ = stack[5].m_obj;
lean_object* v___y_2412_ = stack[6].m_obj;
lean_object* v___y_2413_ = stack[7].m_obj;
lean_object* v___y_2414_ = stack[8].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2406_, lean_box(0), v_a_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2418_, lean_object* v_inst_2419_, lean_object* v_a_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2418_, v_inst_2419_, v_a_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec_ref(v_argUnivs_2418_);
return v_res_2428_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2438_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2429_, v___x_2437_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2438_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_0interp(lean_interpreter_value* stack)
{
lean_object* v_fType_2429_ = stack[0].m_obj;
lean_object* v_a_2430_ = stack[1].m_obj;
lean_object* v_a_2431_ = stack[2].m_obj;
lean_object* v_a_2432_ = stack[3].m_obj;
lean_object* v_a_2433_ = stack[4].m_obj;
lean_object* v_a_2434_ = stack[5].m_obj;
lean_object* v_a_2435_ = stack[6].m_obj;
lean_object* v_res_2439_;
v_res_2439_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
stack->m_obj
 = v_res_2439_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2448_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2449_, lean_object* v_argUnivs_2450_, lean_object* v_declName_2451_, lean_object* v_fType_2452_, lean_object* v_i_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v_00_u03b1_2456_; lean_object* v_00_u03b2_2457_; lean_object* v_u_2458_; lean_object* v_v_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2455_ = lean_box(0);
v_00_u03b1_2456_ = l_Lean_Expr_bindingDomain_x21(v_fType_2452_);
v_00_u03b2_2457_ = l_Lean_Expr_bindingBody_x21(v_fType_2452_);
v_u_2458_ = lean_array_get_borrowed(v___x_2455_, v_argUnivs_2450_, v_i_2453_);
v_v_2459_ = lean_array_get_borrowed(v___x_2455_, v_fnUnivs_2449_, v_i_2453_);
v___x_2460_ = lean_box(0);
lean_inc(v_v_2459_);
v___x_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_v_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
lean_inc(v_u_2458_);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_u_2458_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_mkConst(v_declName_2451_, v___x_2462_);
v___x_2464_ = l_Lean_mkAppB(v___x_2463_, v_00_u03b1_2456_, v_00_u03b2_2457_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnUnivs_2449_ = stack[0].m_obj;
lean_object* v_argUnivs_2450_ = stack[1].m_obj;
lean_object* v_declName_2451_ = stack[2].m_obj;
lean_object* v_fType_2452_ = stack[3].m_obj;
lean_object* v_i_2453_ = stack[4].m_obj;
lean_object* v_res_2466_;
v_res_2466_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2449_, v_argUnivs_2450_, v_declName_2451_, v_fType_2452_, v_i_2453_);
stack->m_obj
 = v_res_2466_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2467_, lean_object* v_argUnivs_2468_, lean_object* v_declName_2469_, lean_object* v_fType_2470_, lean_object* v_i_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2467_, v_argUnivs_2468_, v_declName_2469_, v_fType_2470_, v_i_2471_);
lean_dec(v_i_2471_);
lean_dec_ref(v_fType_2470_);
lean_dec_ref(v_argUnivs_2468_);
lean_dec_ref(v_fnUnivs_2467_);
return v_res_2473_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2474_, lean_object* v_argUnivs_2475_, lean_object* v_declName_2476_, lean_object* v_fType_2477_, lean_object* v_i_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2474_, v_argUnivs_2475_, v_declName_2476_, v_fType_2477_, v_i_2478_);
return v___x_2486_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnUnivs_2474_ = stack[0].m_obj;
lean_object* v_argUnivs_2475_ = stack[1].m_obj;
lean_object* v_declName_2476_ = stack[2].m_obj;
lean_object* v_fType_2477_ = stack[3].m_obj;
lean_object* v_i_2478_ = stack[4].m_obj;
lean_object* v_a_2479_ = stack[5].m_obj;
lean_object* v_a_2480_ = stack[6].m_obj;
lean_object* v_a_2481_ = stack[7].m_obj;
lean_object* v_a_2482_ = stack[8].m_obj;
lean_object* v_a_2483_ = stack[9].m_obj;
lean_object* v_a_2484_ = stack[10].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2474_, v_argUnivs_2475_, v_declName_2476_, v_fType_2477_, v_i_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2488_, lean_object* v_argUnivs_2489_, lean_object* v_declName_2490_, lean_object* v_fType_2491_, lean_object* v_i_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2488_, v_argUnivs_2489_, v_declName_2490_, v_fType_2491_, v_i_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_i_2492_);
lean_dec_ref(v_fType_2491_);
lean_dec_ref(v_argUnivs_2489_);
lean_dec_ref(v_fnUnivs_2488_);
return v_res_2500_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2501_, lean_object* v_a_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___y_2511_; lean_object* v___x_2514_; uint8_t v_debug_2515_; 
v___x_2514_ = lean_st_ref_get(v___y_2504_);
v_debug_2515_ = lean_ctor_get_uint8(v___x_2514_, sizeof(void*)*12);
lean_dec(v___x_2514_);
if (v_debug_2515_ == 0)
{
v___y_2511_ = v___y_2504_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2501_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref_known(v___x_2516_, 1);
v___x_2517_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
v___y_2511_ = v___y_2504_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_a_2502_);
lean_dec_ref(v_f_2501_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_a_2502_);
lean_dec_ref(v_f_2501_);
v_a_2526_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2516_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2516_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = l_Lean_Expr_app___override(v_f_2501_, v_a_2502_);
v___x_2513_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2512_, v___y_2511_);
return v___x_2513_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2501_ = stack[0].m_obj;
lean_object* v_a_2502_ = stack[1].m_obj;
lean_object* v___y_2503_ = stack[2].m_obj;
lean_object* v___y_2504_ = stack[3].m_obj;
lean_object* v___y_2505_ = stack[4].m_obj;
lean_object* v___y_2506_ = stack[5].m_obj;
lean_object* v___y_2507_ = stack[6].m_obj;
lean_object* v___y_2508_ = stack[7].m_obj;
lean_object* v_res_2534_;
v_res_2534_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2501_, v_a_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
stack->m_obj
 = v_res_2534_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2535_, lean_object* v_a_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2535_, v_a_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2544_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2545_, lean_object* v_a_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2545_, v_a_2546_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2545_ = stack[0].m_obj;
lean_object* v_a_2546_ = stack[1].m_obj;
lean_object* v___y_2547_ = stack[2].m_obj;
lean_object* v___y_2548_ = stack[3].m_obj;
lean_object* v___y_2549_ = stack[4].m_obj;
lean_object* v___y_2550_ = stack[5].m_obj;
lean_object* v___y_2551_ = stack[6].m_obj;
lean_object* v___y_2552_ = stack[7].m_obj;
lean_object* v___y_2553_ = stack[8].m_obj;
lean_object* v___y_2554_ = stack[9].m_obj;
lean_object* v___y_2555_ = stack[10].m_obj;
lean_object* v_res_2558_;
v_res_2558_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2545_, v_a_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
stack->m_obj
 = v_res_2558_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2559_, lean_object* v_a_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2559_, v_a_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
return v_res_2571_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_2572_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_15220__overap_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15220__overap_2585_ = lean_panic_fn_borrowed(v___x_2584_, v_msg_2573_);
lean_inc(v___y_2582_);
lean_inc_ref(v___y_2581_);
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
v___x_2586_ = lean_apply_10(v___x_15220__overap_2585_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, lean_box(0));
return v___x_2586_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2573_ = stack[0].m_obj;
lean_object* v___y_2574_ = stack[1].m_obj;
lean_object* v___y_2575_ = stack[2].m_obj;
lean_object* v___y_2576_ = stack[3].m_obj;
lean_object* v___y_2577_ = stack[4].m_obj;
lean_object* v___y_2578_ = stack[5].m_obj;
lean_object* v___y_2579_ = stack[6].m_obj;
lean_object* v___y_2580_ = stack[7].m_obj;
lean_object* v___y_2581_ = stack[8].m_obj;
lean_object* v___y_2582_ = stack[9].m_obj;
lean_object* v_res_2587_;
v_res_2587_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
stack->m_obj
 = v_res_2587_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
return v_res_2599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2611_ = lean_unsigned_to_nat(11u);
v___x_2612_ = lean_unsigned_to_nat(346u);
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2615_ = l_mkPanicMessageWithDecl(v___x_2614_, v___x_2613_, v___x_2612_, v___x_2611_, v___x_2610_);
return v___x_2615_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2616_, lean_object* v_fnUnivs_2617_, lean_object* v_argUnivs_2618_, lean_object* v_simpBody_2619_, lean_object* v_e_2620_, lean_object* v_i_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
switch(lean_obj_tag(v_e_2620_))
{
case 5:
{
lean_object* v_fn_2632_; lean_object* v_arg_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_fn_2632_ = lean_ctor_get(v_e_2620_, 0);
lean_inc_ref_n(v_fn_2632_, 2);
v_arg_2633_ = lean_ctor_get(v_e_2620_, 1);
lean_inc_ref(v_arg_2633_);
lean_dec_ref_known(v_e_2620_, 2);
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_sub(v_i_2621_, v___x_2634_);
v___x_2636_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2616_, v_fnUnivs_2617_, v_argUnivs_2618_, v_simpBody_2619_, v_fn_2632_, v___x_2635_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v___x_2635_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2757_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2757_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2757_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2756_; 
v_fst_2641_ = lean_ctor_get(v_a_2637_, 0);
v_snd_2642_ = lean_ctor_get(v_a_2637_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2644_ = v_a_2637_;
v_isShared_2645_ = v_isSharedCheck_2756_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_snd_2642_);
lean_inc(v_fst_2641_);
lean_dec(v_a_2637_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2756_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_r_2647_; lean_object* v___x_2655_; 
lean_inc(v_a_2630_);
lean_inc_ref(v_a_2629_);
lean_inc(v_a_2628_);
lean_inc_ref(v_a_2627_);
lean_inc(v_a_2626_);
lean_inc_ref(v_a_2625_);
lean_inc(v_a_2624_);
lean_inc_ref(v_a_2623_);
lean_inc(v_a_2622_);
lean_inc_ref(v_arg_2633_);
v___x_2655_ = lean_sym_simp(v_arg_2633_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; uint8_t v___y_2658_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
if (lean_obj_tag(v_fst_2641_) == 0)
{
if (lean_obj_tag(v_a_2656_) == 0)
{
uint8_t v_contextDependent_2660_; 
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_fn_2632_);
v_contextDependent_2660_ = lean_ctor_get_uint8(v_fst_2641_, 1);
lean_dec_ref_known(v_fst_2641_, 0);
if (v_contextDependent_2660_ == 0)
{
uint8_t v_contextDependent_2661_; 
v_contextDependent_2661_ = lean_ctor_get_uint8(v_a_2656_, 1);
lean_dec_ref_known(v_a_2656_, 0);
v___y_2658_ = v_contextDependent_2661_;
goto v___jp_2657_;
}
else
{
lean_dec_ref_known(v_a_2656_, 0);
v___y_2658_ = v_contextDependent_2660_;
goto v___jp_2657_;
}
}
else
{
uint8_t v_contextDependent_2662_; lean_object* v_e_x27_2663_; lean_object* v_proof_2664_; uint8_t v_contextDependent_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2689_; 
v_contextDependent_2662_ = lean_ctor_get_uint8(v_fst_2641_, 1);
lean_dec_ref_known(v_fst_2641_, 0);
v_e_x27_2663_ = lean_ctor_get(v_a_2656_, 0);
v_proof_2664_ = lean_ctor_get(v_a_2656_, 1);
v_contextDependent_2665_ = lean_ctor_get_uint8(v_a_2656_, sizeof(void*)*2 + 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2667_ = v_a_2656_;
v_isShared_2668_ = v_isSharedCheck_2689_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_proof_2664_);
lean_inc(v_e_x27_2663_);
lean_dec(v_a_2656_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2689_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; 
lean_inc_ref(v_e_x27_2663_);
lean_inc_ref(v_fn_2632_);
v___x_2669_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2632_, v_e_x27_2663_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_a_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; uint8_t v___y_2677_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2672_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2617_, v_argUnivs_2618_, v___x_2671_, v_snd_2642_, v_i_2621_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
v___x_2674_ = l_Lean_mkApp4(v_a_2673_, v_arg_2633_, v_e_x27_2663_, v_fn_2632_, v_proof_2664_);
v___x_2675_ = 0;
if (v_contextDependent_2662_ == 0)
{
v___y_2677_ = v_contextDependent_2665_;
goto v___jp_2676_;
}
else
{
v___y_2677_ = v_contextDependent_2662_;
goto v___jp_2676_;
}
v___jp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2674_);
lean_ctor_set(v___x_2667_, 0, v_a_2670_);
v___x_2679_ = v___x_2667_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2670_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*2, v___x_2675_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*2 + 1, v___y_2677_);
v_r_2647_ = v___x_2679_;
goto v___jp_2646_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_del_object(v___x_2667_);
lean_dec_ref(v_proof_2664_);
lean_dec_ref(v_e_x27_2663_);
lean_del_object(v___x_2644_);
lean_dec(v_snd_2642_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_fn_2632_);
v_a_2681_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2669_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2669_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2656_) == 0)
{
lean_object* v_e_x27_2690_; lean_object* v_proof_2691_; uint8_t v_contextDependent_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2717_; 
v_e_x27_2690_ = lean_ctor_get(v_fst_2641_, 0);
v_proof_2691_ = lean_ctor_get(v_fst_2641_, 1);
v_contextDependent_2692_ = lean_ctor_get_uint8(v_fst_2641_, sizeof(void*)*2 + 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_fst_2641_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2694_ = v_fst_2641_;
v_isShared_2695_ = v_isSharedCheck_2717_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_proof_2691_);
lean_inc(v_e_x27_2690_);
lean_dec(v_fst_2641_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2717_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
uint8_t v_contextDependent_2696_; lean_object* v___x_2697_; 
v_contextDependent_2696_ = lean_ctor_get_uint8(v_a_2656_, 1);
lean_dec_ref_known(v_a_2656_, 0);
lean_inc_ref(v_arg_2633_);
lean_inc_ref(v_e_x27_2690_);
v___x_2697_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2690_, v_arg_2633_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_a_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; uint8_t v___y_2705_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2700_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2617_, v_argUnivs_2618_, v___x_2699_, v_snd_2642_, v_i_2621_);
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = l_Lean_mkApp4(v_a_2701_, v_fn_2632_, v_e_x27_2690_, v_proof_2691_, v_arg_2633_);
v___x_2703_ = 0;
if (v_contextDependent_2692_ == 0)
{
v___y_2705_ = v_contextDependent_2696_;
goto v___jp_2704_;
}
else
{
v___y_2705_ = v_contextDependent_2692_;
goto v___jp_2704_;
}
v___jp_2704_:
{
lean_object* v___x_2707_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v___x_2702_);
lean_ctor_set(v___x_2694_, 0, v_a_2698_);
v___x_2707_ = v___x_2694_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2698_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*2, v___x_2703_);
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*2 + 1, v___y_2705_);
v_r_2647_ = v___x_2707_;
goto v___jp_2646_;
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_del_object(v___x_2694_);
lean_dec_ref(v_proof_2691_);
lean_dec_ref(v_e_x27_2690_);
lean_del_object(v___x_2644_);
lean_dec(v_snd_2642_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_fn_2632_);
v_a_2709_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2697_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2697_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2718_; lean_object* v_proof_2719_; uint8_t v_contextDependent_2720_; lean_object* v_e_x27_2721_; lean_object* v_proof_2722_; uint8_t v_contextDependent_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2747_; 
v_e_x27_2718_ = lean_ctor_get(v_fst_2641_, 0);
lean_inc_ref(v_e_x27_2718_);
v_proof_2719_ = lean_ctor_get(v_fst_2641_, 1);
lean_inc_ref(v_proof_2719_);
v_contextDependent_2720_ = lean_ctor_get_uint8(v_fst_2641_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2641_, 2);
v_e_x27_2721_ = lean_ctor_get(v_a_2656_, 0);
v_proof_2722_ = lean_ctor_get(v_a_2656_, 1);
v_contextDependent_2723_ = lean_ctor_get_uint8(v_a_2656_, sizeof(void*)*2 + 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2725_ = v_a_2656_;
v_isShared_2726_ = v_isSharedCheck_2747_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_proof_2722_);
lean_inc(v_e_x27_2721_);
lean_dec(v_a_2656_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2747_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; 
lean_inc_ref(v_e_x27_2721_);
lean_inc_ref(v_e_x27_2718_);
v___x_2727_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2718_, v_e_x27_2721_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v_a_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; uint8_t v___y_2735_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2730_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2617_, v_argUnivs_2618_, v___x_2729_, v_snd_2642_, v_i_2621_);
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = l_Lean_mkApp6(v_a_2731_, v_fn_2632_, v_e_x27_2718_, v_arg_2633_, v_e_x27_2721_, v_proof_2719_, v_proof_2722_);
v___x_2733_ = 0;
if (v_contextDependent_2720_ == 0)
{
v___y_2735_ = v_contextDependent_2723_;
goto v___jp_2734_;
}
else
{
v___y_2735_ = v_contextDependent_2720_;
goto v___jp_2734_;
}
v___jp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2732_);
lean_ctor_set(v___x_2725_, 0, v_a_2728_);
v___x_2737_ = v___x_2725_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2728_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v___x_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*2, v___x_2733_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*2 + 1, v___y_2735_);
v_r_2647_ = v___x_2737_;
goto v___jp_2646_;
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_del_object(v___x_2725_);
lean_dec_ref(v_proof_2722_);
lean_dec_ref(v_e_x27_2721_);
lean_dec_ref(v_proof_2719_);
lean_dec_ref(v_e_x27_2718_);
lean_del_object(v___x_2644_);
lean_dec(v_snd_2642_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_fn_2632_);
v_a_2739_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2727_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2727_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
v___jp_2657_:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2658_);
v_r_2647_ = v___x_2659_;
goto v___jp_2646_;
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_del_object(v___x_2644_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_del_object(v___x_2639_);
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_fn_2632_);
v_a_2748_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2655_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2655_);
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
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = l_Lean_Expr_bindingBody_x21(v_snd_2642_);
lean_dec(v_snd_2642_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2648_);
lean_ctor_set(v___x_2644_, 0, v_r_2647_);
v___x_2650_ = v___x_2644_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_r_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2650_);
v___x_2652_ = v___x_2639_;
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
}
}
}
}
else
{
lean_dec_ref(v_arg_2633_);
lean_dec_ref(v_fn_2632_);
return v___x_2636_;
}
}
case 6:
{
lean_object* v___x_2758_; 
lean_inc(v_a_2630_);
lean_inc_ref(v_a_2629_);
lean_inc(v_a_2628_);
lean_inc_ref(v_a_2627_);
lean_inc(v_a_2626_);
lean_inc_ref(v_a_2625_);
lean_inc(v_a_2624_);
lean_inc_ref(v_a_2623_);
lean_inc(v_a_2622_);
v___x_2758_ = lean_apply_11(v_simpBody_2619_, v_e_2620_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, lean_box(0));
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2767_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2759_);
lean_ctor_set(v___x_2763_, 1, v_fType_2616_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2763_);
v___x_2765_ = v___x_2761_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_fType_2616_);
v_a_2768_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2758_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2758_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
default: 
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec_ref(v_e_2620_);
lean_dec_ref(v_simpBody_2619_);
lean_dec_ref(v_fType_2616_);
v___x_2776_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2777_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2776_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
return v___x_2777_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_fType_2616_ = stack[0].m_obj;
lean_object* v_fnUnivs_2617_ = stack[1].m_obj;
lean_object* v_argUnivs_2618_ = stack[2].m_obj;
lean_object* v_simpBody_2619_ = stack[3].m_obj;
lean_object* v_e_2620_ = stack[4].m_obj;
lean_object* v_i_2621_ = stack[5].m_obj;
lean_object* v_a_2622_ = stack[6].m_obj;
lean_object* v_a_2623_ = stack[7].m_obj;
lean_object* v_a_2624_ = stack[8].m_obj;
lean_object* v_a_2625_ = stack[9].m_obj;
lean_object* v_a_2626_ = stack[10].m_obj;
lean_object* v_a_2627_ = stack[11].m_obj;
lean_object* v_a_2628_ = stack[12].m_obj;
lean_object* v_a_2629_ = stack[13].m_obj;
lean_object* v_a_2630_ = stack[14].m_obj;
lean_object* v_res_2778_;
v_res_2778_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2616_, v_fnUnivs_2617_, v_argUnivs_2618_, v_simpBody_2619_, v_e_2620_, v_i_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
stack->m_obj
 = v_res_2778_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2779_, lean_object* v_fnUnivs_2780_, lean_object* v_argUnivs_2781_, lean_object* v_simpBody_2782_, lean_object* v_e_2783_, lean_object* v_i_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2779_, v_fnUnivs_2780_, v_argUnivs_2781_, v_simpBody_2782_, v_e_2783_, v_i_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec(v_i_2784_);
lean_dec_ref(v_argUnivs_2781_);
lean_dec_ref(v_fnUnivs_2780_);
return v_res_2795_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2796_, lean_object* v_fType_2797_, lean_object* v_fnUnivs_2798_, lean_object* v_argUnivs_2799_, lean_object* v_simpBody_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_numArgs_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_numArgs_2811_ = lean_array_get_size(v_argUnivs_2799_);
v___x_2812_ = lean_unsigned_to_nat(1u);
v___x_2813_ = lean_nat_sub(v_numArgs_2811_, v___x_2812_);
v___x_2814_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2797_, v_fnUnivs_2798_, v_argUnivs_2799_, v_simpBody_2800_, v_e_2796_, v___x_2813_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v___x_2813_);
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
lean_object* v_fst_2819_; lean_object* v___x_2821_; 
v_fst_2819_ = lean_ctor_get(v_a_2815_, 0);
lean_inc(v_fst_2819_);
lean_dec(v_a_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_fst_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_fst_2819_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2796_ = stack[0].m_obj;
lean_object* v_fType_2797_ = stack[1].m_obj;
lean_object* v_fnUnivs_2798_ = stack[2].m_obj;
lean_object* v_argUnivs_2799_ = stack[3].m_obj;
lean_object* v_simpBody_2800_ = stack[4].m_obj;
lean_object* v_a_2801_ = stack[5].m_obj;
lean_object* v_a_2802_ = stack[6].m_obj;
lean_object* v_a_2803_ = stack[7].m_obj;
lean_object* v_a_2804_ = stack[8].m_obj;
lean_object* v_a_2805_ = stack[9].m_obj;
lean_object* v_a_2806_ = stack[10].m_obj;
lean_object* v_a_2807_ = stack[11].m_obj;
lean_object* v_a_2808_ = stack[12].m_obj;
lean_object* v_a_2809_ = stack[13].m_obj;
lean_object* v_res_2832_;
v_res_2832_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2796_, v_fType_2797_, v_fnUnivs_2798_, v_argUnivs_2799_, v_simpBody_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
stack->m_obj
 = v_res_2832_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2833_, lean_object* v_fType_2834_, lean_object* v_fnUnivs_2835_, lean_object* v_argUnivs_2836_, lean_object* v_simpBody_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2833_, v_fType_2834_, v_fnUnivs_2835_, v_argUnivs_2836_, v_simpBody_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_argUnivs_2836_);
lean_dec_ref(v_fnUnivs_2835_);
return v_res_2848_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2853_, lean_object* v_simpBody_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___x_2865_; 
lean_inc_ref(v_e_2853_);
v___x_2865_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2853_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v_00_u03b1_2867_; lean_object* v_u_2868_; lean_object* v_e_2869_; lean_object* v_h_2870_; lean_object* v_varDeps_2871_; lean_object* v_fType_2872_; lean_object* v___x_2873_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v_00_u03b1_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc_ref(v_00_u03b1_2867_);
v_u_2868_ = lean_ctor_get(v_a_2866_, 1);
lean_inc(v_u_2868_);
v_e_2869_ = lean_ctor_get(v_a_2866_, 2);
lean_inc_ref(v_e_2869_);
v_h_2870_ = lean_ctor_get(v_a_2866_, 3);
lean_inc_ref(v_h_2870_);
v_varDeps_2871_ = lean_ctor_get(v_a_2866_, 4);
lean_inc_ref(v_varDeps_2871_);
v_fType_2872_ = lean_ctor_get(v_a_2866_, 5);
lean_inc_ref_n(v_fType_2872_, 2);
lean_dec(v_a_2866_);
v___x_2873_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2872_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_argUnivs_2875_; lean_object* v_fnUnivs_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2944_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_argUnivs_2875_ = lean_ctor_get(v_a_2874_, 0);
v_fnUnivs_2876_ = lean_ctor_get(v_a_2874_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_a_2874_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2878_ = v_a_2874_;
v_isShared_2879_ = v_isSharedCheck_2944_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_fnUnivs_2876_);
lean_inc(v_argUnivs_2875_);
lean_dec(v_a_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2944_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; 
lean_inc_ref(v_e_2869_);
v___x_2880_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2869_, v_fType_2872_, v_fnUnivs_2876_, v_argUnivs_2875_, v_simpBody_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec_ref(v_argUnivs_2875_);
lean_dec_ref(v_fnUnivs_2876_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2935_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2935_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2935_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
if (lean_obj_tag(v_a_2881_) == 0)
{
uint8_t v_contextDependent_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
lean_del_object(v___x_2878_);
lean_dec_ref(v_varDeps_2871_);
lean_dec_ref(v_h_2870_);
lean_dec_ref(v_e_2869_);
lean_dec_ref(v_e_2853_);
v_contextDependent_2885_ = lean_ctor_get_uint8(v_a_2881_, 1);
lean_dec_ref_known(v_a_2881_, 0);
v___x_2886_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2885_);
v___x_2887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v_00_u03b1_2867_);
lean_ctor_set(v___x_2887_, 2, v_u_2868_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2887_);
v___x_2889_ = v___x_2883_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
else
{
lean_object* v_e_x27_2891_; lean_object* v_proof_2892_; uint8_t v_contextDependent_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2934_; 
lean_del_object(v___x_2883_);
v_e_x27_2891_ = lean_ctor_get(v_a_2881_, 0);
v_proof_2892_ = lean_ctor_get(v_a_2881_, 1);
v_contextDependent_2893_ = lean_ctor_get_uint8(v_a_2881_, sizeof(void*)*2 + 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_a_2881_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2895_ = v_a_2881_;
v_isShared_2896_ = v_isSharedCheck_2934_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_proof_2892_);
lean_inc(v_e_x27_2891_);
lean_dec(v_a_2881_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2934_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2897_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2898_ = lean_box(0);
lean_inc(v_u_2868_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 1);
lean_ctor_set(v___x_2878_, 1, v___x_2898_);
lean_ctor_set(v___x_2878_, 0, v_u_2868_);
v___x_2900_ = v___x_2878_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_u_2868_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_inc_ref(v___x_2900_);
v___x_2901_ = l_Lean_mkConst(v___x_2897_, v___x_2900_);
lean_inc_ref_n(v_e_x27_2891_, 2);
lean_inc_ref(v_e_2853_);
lean_inc_ref(v_00_u03b1_2867_);
lean_inc_ref(v___x_2901_);
v___x_2902_ = l_Lean_mkApp6(v___x_2901_, v_00_u03b1_2867_, v_e_2853_, v_e_2869_, v_e_x27_2891_, v_h_2870_, v_proof_2892_);
v___x_2903_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2891_, v_varDeps_2871_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2924_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2924_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2924_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; lean_object* v___x_2918_; 
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2900_);
v___x_2909_ = l_Lean_mkConst(v___x_2908_, v___x_2900_);
lean_inc_n(v_a_2904_, 2);
lean_inc_ref_n(v_e_x27_2891_, 2);
lean_inc_ref_n(v_00_u03b1_2867_, 3);
v___x_2910_ = l_Lean_mkApp3(v___x_2909_, v_00_u03b1_2867_, v_e_x27_2891_, v_a_2904_);
v___x_2911_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2912_ = l_Lean_mkConst(v___x_2911_, v___x_2900_);
v___x_2913_ = l_Lean_mkAppB(v___x_2912_, v_00_u03b1_2867_, v_e_x27_2891_);
v___x_2914_ = l_Lean_Meta_mkExpectedPropHint(v___x_2913_, v___x_2910_);
v___x_2915_ = l_Lean_mkApp6(v___x_2901_, v_00_u03b1_2867_, v_e_2853_, v_e_x27_2891_, v_a_2904_, v___x_2902_, v___x_2914_);
v___x_2916_ = 0;
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 1, v___x_2915_);
lean_ctor_set(v___x_2895_, 0, v_a_2904_);
v___x_2918_ = v___x_2895_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2904_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___x_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2923_, sizeof(void*)*2 + 1, v_contextDependent_2893_);
v___x_2918_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*2, v___x_2916_);
v___x_2919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v_00_u03b1_2867_);
lean_ctor_set(v___x_2919_, 2, v_u_2868_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2919_);
v___x_2921_ = v___x_2906_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
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
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v___x_2900_);
lean_del_object(v___x_2895_);
lean_dec_ref(v_e_x27_2891_);
lean_dec(v_u_2868_);
lean_dec_ref(v_00_u03b1_2867_);
lean_dec_ref(v_e_2853_);
v_a_2925_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2903_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2903_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
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
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_del_object(v___x_2878_);
lean_dec_ref(v_varDeps_2871_);
lean_dec_ref(v_h_2870_);
lean_dec_ref(v_e_2869_);
lean_dec(v_u_2868_);
lean_dec_ref(v_00_u03b1_2867_);
lean_dec_ref(v_e_2853_);
v_a_2936_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2880_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2880_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec_ref(v_fType_2872_);
lean_dec_ref(v_varDeps_2871_);
lean_dec_ref(v_h_2870_);
lean_dec_ref(v_e_2869_);
lean_dec(v_u_2868_);
lean_dec_ref(v_00_u03b1_2867_);
lean_dec_ref(v_simpBody_2854_);
lean_dec_ref(v_e_2853_);
v_a_2945_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2873_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2873_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_simpBody_2854_);
lean_dec_ref(v_e_2853_);
v_a_2953_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2865_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2865_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2853_ = stack[0].m_obj;
lean_object* v_simpBody_2854_ = stack[1].m_obj;
lean_object* v_a_2855_ = stack[2].m_obj;
lean_object* v_a_2856_ = stack[3].m_obj;
lean_object* v_a_2857_ = stack[4].m_obj;
lean_object* v_a_2858_ = stack[5].m_obj;
lean_object* v_a_2859_ = stack[6].m_obj;
lean_object* v_a_2860_ = stack[7].m_obj;
lean_object* v_a_2861_ = stack[8].m_obj;
lean_object* v_a_2862_ = stack[9].m_obj;
lean_object* v_a_2863_ = stack[10].m_obj;
lean_object* v_res_2961_;
v_res_2961_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2853_, v_simpBody_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
stack->m_obj
 = v_res_2961_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2962_, lean_object* v_simpBody_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2962_, v_simpBody_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
return v_res_2974_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2975_, lean_object* v_simpBody_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2975_, v_simpBody_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2996_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_result_2992_; lean_object* v___x_2994_; 
v_result_2992_ = lean_ctor_get(v_a_2988_, 0);
lean_inc_ref(v_result_2992_);
lean_dec(v_a_2988_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v_result_2992_);
v___x_2994_ = v___x_2990_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_result_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_a_2997_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2987_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2987_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2975_ = stack[0].m_obj;
lean_object* v_simpBody_2976_ = stack[1].m_obj;
lean_object* v_a_2977_ = stack[2].m_obj;
lean_object* v_a_2978_ = stack[3].m_obj;
lean_object* v_a_2979_ = stack[4].m_obj;
lean_object* v_a_2980_ = stack[5].m_obj;
lean_object* v_a_2981_ = stack[6].m_obj;
lean_object* v_a_2982_ = stack[7].m_obj;
lean_object* v_a_2983_ = stack[8].m_obj;
lean_object* v_a_2984_ = stack[9].m_obj;
lean_object* v_a_2985_ = stack[10].m_obj;
lean_object* v_res_3005_;
v_res_3005_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2975_, v_simpBody_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
stack->m_obj
 = v_res_3005_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_3006_, lean_object* v_simpBody_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_3006_, v_simpBody_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
return v_res_3018_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_3019_, lean_object* v_simpBody_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___x_3031_; 
lean_inc_ref(v_e_u2081_3019_);
v___x_3031_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_3019_, v_simpBody_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v_result_3033_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v_result_3033_ = lean_ctor_get(v_a_3032_, 0);
lean_inc_ref(v_result_3033_);
if (lean_obj_tag(v_result_3033_) == 0)
{
lean_object* v_00_u03b1_3034_; lean_object* v_u_3035_; uint8_t v_contextDependent_3036_; lean_object* v___x_3037_; 
v_00_u03b1_3034_ = lean_ctor_get(v_a_3032_, 1);
lean_inc_ref(v_00_u03b1_3034_);
v_u_3035_ = lean_ctor_get(v_a_3032_, 2);
lean_inc(v_u_3035_);
lean_dec(v_a_3032_);
v_contextDependent_3036_ = lean_ctor_get_uint8(v_result_3033_, 1);
lean_dec_ref_known(v_result_3033_, 0);
lean_inc_ref(v_e_u2081_3019_);
v___x_3037_ = l_Lean_Meta_zetaUnused(v_e_u2081_3019_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3058_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3058_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3058_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
size_t v___x_3042_; size_t v___x_3043_; uint8_t v___x_3044_; 
v___x_3042_ = lean_ptr_addr(v_e_u2081_3019_);
lean_dec_ref(v_e_u2081_3019_);
v___x_3043_ = lean_ptr_addr(v_a_3038_);
v___x_3044_ = lean_usize_dec_eq(v___x_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3045_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v_u_3035_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = l_Lean_mkConst(v___x_3045_, v___x_3047_);
lean_inc(v_a_3038_);
v___x_3049_ = l_Lean_mkAppB(v___x_3048_, v_00_u03b1_3034_, v_a_3038_);
v___x_3050_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3050_, 0, v_a_3038_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
lean_ctor_set_uint8(v___x_3050_, sizeof(void*)*2, v___x_3044_);
lean_ctor_set_uint8(v___x_3050_, sizeof(void*)*2 + 1, v_contextDependent_3036_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3050_);
v___x_3052_ = v___x_3040_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_dec(v_a_3038_);
lean_dec(v_u_3035_);
lean_dec_ref(v_00_u03b1_3034_);
v___x_3054_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_3036_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3054_);
v___x_3056_ = v___x_3040_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec(v_u_3035_);
lean_dec_ref(v_00_u03b1_3034_);
lean_dec_ref(v_e_u2081_3019_);
v_a_3059_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3037_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3037_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_00_u03b1_3067_; lean_object* v_u_3068_; lean_object* v_e_x27_3069_; lean_object* v_proof_3070_; uint8_t v_contextDependent_3071_; lean_object* v___x_3072_; 
v_00_u03b1_3067_ = lean_ctor_get(v_a_3032_, 1);
lean_inc_ref(v_00_u03b1_3067_);
v_u_3068_ = lean_ctor_get(v_a_3032_, 2);
lean_inc(v_u_3068_);
lean_dec(v_a_3032_);
v_e_x27_3069_ = lean_ctor_get(v_result_3033_, 0);
v_proof_3070_ = lean_ctor_get(v_result_3033_, 1);
v_contextDependent_3071_ = lean_ctor_get_uint8(v_result_3033_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_3069_);
v___x_3072_ = l_Lean_Meta_zetaUnused(v_e_x27_3069_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3103_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3103_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3103_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
size_t v___x_3077_; size_t v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = lean_ptr_addr(v_e_x27_3069_);
v___x_3078_ = lean_ptr_addr(v_a_3073_);
v___x_3079_ = lean_usize_dec_eq(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3097_; 
lean_inc_ref(v_proof_3070_);
lean_inc_ref(v_e_x27_3069_);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_result_3033_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; lean_object* v_unused_3099_; 
v_unused_3098_ = lean_ctor_get(v_result_3033_, 1);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_result_3033_, 0);
lean_dec(v_unused_3099_);
v___x_3081_ = v_result_3033_;
v_isShared_3082_ = v_isSharedCheck_3097_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v_result_3033_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3097_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_u_3068_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
lean_inc_ref(v___x_3085_);
v___x_3086_ = l_Lean_mkConst(v___x_3083_, v___x_3085_);
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3088_ = l_Lean_mkConst(v___x_3087_, v___x_3085_);
lean_inc_n(v_a_3073_, 2);
lean_inc_ref(v_00_u03b1_3067_);
v___x_3089_ = l_Lean_mkAppB(v___x_3088_, v_00_u03b1_3067_, v_a_3073_);
v___x_3090_ = l_Lean_mkApp6(v___x_3086_, v_00_u03b1_3067_, v_e_u2081_3019_, v_e_x27_3069_, v_a_3073_, v_proof_3070_, v___x_3089_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3090_);
lean_ctor_set(v___x_3081_, 0, v_a_3073_);
v___x_3092_ = v___x_3081_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3073_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_3090_);
lean_ctor_set_uint8(v_reuseFailAlloc_3096_, sizeof(void*)*2 + 1, v_contextDependent_3071_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*2, v___x_3079_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3092_);
v___x_3094_ = v___x_3075_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v_a_3073_);
lean_dec(v_u_3068_);
lean_dec_ref(v_00_u03b1_3067_);
lean_dec_ref(v_e_u2081_3019_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v_result_3033_);
v___x_3101_ = v___x_3075_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_result_3033_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_u_3068_);
lean_dec_ref(v_00_u03b1_3067_);
lean_dec_ref_known(v_result_3033_, 2);
lean_dec_ref(v_e_u2081_3019_);
v_a_3104_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3072_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3072_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v_e_u2081_3019_);
v_a_3112_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3031_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3031_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_3019_ = stack[0].m_obj;
lean_object* v_simpBody_3020_ = stack[1].m_obj;
lean_object* v_a_3021_ = stack[2].m_obj;
lean_object* v_a_3022_ = stack[3].m_obj;
lean_object* v_a_3023_ = stack[4].m_obj;
lean_object* v_a_3024_ = stack[5].m_obj;
lean_object* v_a_3025_ = stack[6].m_obj;
lean_object* v_a_3026_ = stack[7].m_obj;
lean_object* v_a_3027_ = stack[8].m_obj;
lean_object* v_a_3028_ = stack[9].m_obj;
lean_object* v_a_3029_ = stack[10].m_obj;
lean_object* v_res_3120_;
v_res_3120_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_3019_, v_simpBody_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
stack->m_obj
 = v_res_3120_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_3121_, lean_object* v_simpBody_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_3121_, v_simpBody_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
return v_res_3133_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_3134_, lean_object* v_e_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
uint8_t v___x_3146_; 
v___x_3146_ = l_Lean_Expr_letNondep_x21(v_e_3135_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec_ref(v_e_3135_);
lean_dec_ref(v_simpBody_3134_);
v___x_3147_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3147_, 0, v___x_3146_);
lean_ctor_set_uint8(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_3135_, v_simpBody_3134_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
return v___x_3149_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpLet_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_3134_ = stack[0].m_obj;
lean_object* v_e_3135_ = stack[1].m_obj;
lean_object* v_a_3136_ = stack[2].m_obj;
lean_object* v_a_3137_ = stack[3].m_obj;
lean_object* v_a_3138_ = stack[4].m_obj;
lean_object* v_a_3139_ = stack[5].m_obj;
lean_object* v_a_3140_ = stack[6].m_obj;
lean_object* v_a_3141_ = stack[7].m_obj;
lean_object* v_a_3142_ = stack[8].m_obj;
lean_object* v_a_3143_ = stack[9].m_obj;
lean_object* v_a_3144_ = stack[10].m_obj;
lean_object* v_res_3150_;
v_res_3150_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_3134_, v_e_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
stack->m_obj
 = v_res_3150_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_3151_, lean_object* v_e_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_3151_, v_e_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
return v_res_3163_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_3177_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_3176_, v_e_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
return v___x_3177_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3165_ = stack[0].m_obj;
lean_object* v_a_3166_ = stack[1].m_obj;
lean_object* v_a_3167_ = stack[2].m_obj;
lean_object* v_a_3168_ = stack[3].m_obj;
lean_object* v_a_3169_ = stack[4].m_obj;
lean_object* v_a_3170_ = stack[5].m_obj;
lean_object* v_a_3171_ = stack[6].m_obj;
lean_object* v_a_3172_ = stack[7].m_obj;
lean_object* v_a_3173_ = stack[8].m_obj;
lean_object* v_a_3174_ = stack[9].m_obj;
lean_object* v_res_3178_;
v_res_3178_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
stack->m_obj
 = v_res_3178_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
return v_res_3190_;
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
