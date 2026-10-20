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
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_192_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_171_, v_fvarIds_191_, v___x_194_, v___x_195_, v___x_188_);
lean_dec_ref(v_fvarIds_191_);
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
v___jp_172_:
{
uint8_t v___x_177_; 
v___x_177_ = lean_nat_dec_le(v___y_176_, v___y_173_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v___y_173_);
lean_inc(v___y_176_);
v___x_178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_171_, v___y_174_, v___y_175_, v___y_176_, v___y_176_);
lean_dec(v___y_176_);
lean_dec(v___y_174_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_171_, v___y_174_, v___y_175_, v___y_176_, v___y_173_);
lean_dec(v___y_173_);
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
v___y_173_ = v___x_186_;
v___y_174_ = v___x_183_;
v___y_175_ = v___y_182_;
v___y_176_ = v___x_186_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___x_186_;
v___y_174_ = v___x_183_;
v___y_175_ = v___y_182_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(lean_object* v_e_197_, lean_object* v_fvarIdToPos_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_e_197_, v_fvarIdToPos_198_);
lean_dec(v_fvarIdToPos_198_);
return v_res_199_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_200_, lean_object* v_k_201_, lean_object* v_t_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_201_, v_t_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_204_, lean_object* v_k_205_, lean_object* v_t_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_204_, v_k_205_, v_t_206_);
lean_dec(v_t_206_);
lean_dec(v_k_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_209_, lean_object* v_n_210_, lean_object* v_as_211_, lean_object* v_lo_212_, lean_object* v_hi_213_, lean_object* v_w_214_, lean_object* v_hlo_215_, lean_object* v_hhi_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_209_, v_n_210_, v_as_211_, v_lo_212_, v_hi_213_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_218_, lean_object* v_n_219_, lean_object* v_as_220_, lean_object* v_lo_221_, lean_object* v_hi_222_, lean_object* v_w_223_, lean_object* v_hlo_224_, lean_object* v_hhi_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_218_, v_n_219_, v_as_220_, v_lo_221_, v_hi_222_, v_w_223_, v_hlo_224_, v_hhi_225_);
lean_dec(v_hi_222_);
lean_dec(v_n_219_);
lean_dec(v_fvarIdToPos_218_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(lean_object* v_fvarIdToPos_227_, lean_object* v_n_228_, lean_object* v_lo_229_, lean_object* v_hi_230_, lean_object* v_hhi_231_, lean_object* v_pivot_232_, lean_object* v_as_233_, lean_object* v_i_234_, lean_object* v_k_235_, lean_object* v_ilo_236_, lean_object* v_ik_237_, lean_object* v_w_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_227_, v_hi_230_, v_pivot_232_, v_as_233_, v_i_234_, v_k_235_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(lean_object* v_fvarIdToPos_240_, lean_object* v_n_241_, lean_object* v_lo_242_, lean_object* v_hi_243_, lean_object* v_hhi_244_, lean_object* v_pivot_245_, lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_k_248_, lean_object* v_ilo_249_, lean_object* v_ik_250_, lean_object* v_w_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(v_fvarIdToPos_240_, v_n_241_, v_lo_242_, v_hi_243_, v_hhi_244_, v_pivot_245_, v_as_246_, v_i_247_, v_k_248_, v_ilo_249_, v_ik_250_, v_w_251_);
lean_dec(v_pivot_245_);
lean_dec(v_hi_243_);
lean_dec(v_lo_242_);
lean_dec(v_n_241_);
lean_dec(v_fvarIdToPos_240_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_253_, uint8_t v_bi_254_, lean_object* v_t_255_, lean_object* v_b_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___y_265_; lean_object* v___x_268_; uint8_t v_debug_269_; 
v___x_268_ = lean_st_ref_get(v___y_258_);
v_debug_269_ = lean_ctor_get_uint8(v___x_268_, sizeof(void*)*12);
lean_dec(v___x_268_);
if (v_debug_269_ == 0)
{
v___y_265_ = v___y_258_;
goto v___jp_264_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_255_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; 
lean_dec_ref_known(v___x_270_, 1);
v___x_271_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_dec_ref_known(v___x_271_, 1);
v___y_265_ = v___y_258_;
goto v___jp_264_;
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v_b_256_);
lean_dec_ref(v_t_255_);
lean_dec(v_x_253_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v_b_256_);
lean_dec_ref(v_t_255_);
lean_dec(v_x_253_);
v_a_280_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_270_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_270_);
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
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = l_Lean_Expr_forallE___override(v_x_253_, v_t_255_, v_b_256_, v_bi_254_);
v___x_267_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_266_, v___y_265_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_288_, lean_object* v_bi_289_, lean_object* v_t_290_, lean_object* v_b_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
uint8_t v_bi_boxed_299_; lean_object* v_res_300_; 
v_bi_boxed_299_ = lean_unbox(v_bi_289_);
v_res_300_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_288_, v_bi_boxed_299_, v_t_290_, v_b_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_304_, lean_object* v_i_305_, lean_object* v_00_u03b2_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_zero_314_; uint8_t v_isZero_315_; 
v_zero_314_ = lean_unsigned_to_nat(0u);
v_isZero_315_ = lean_nat_dec_eq(v_i_305_, v_zero_314_);
if (v_isZero_315_ == 1)
{
lean_object* v___x_316_; 
lean_dec(v_i_305_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v_00_u03b2_306_);
return v___x_316_;
}
else
{
lean_object* v_one_317_; lean_object* v_n_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_one_317_ = lean_unsigned_to_nat(1u);
v_n_318_ = lean_nat_sub(v_i_305_, v_one_317_);
lean_dec(v_i_305_);
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_320_ = 0;
v___x_321_ = lean_array_fget_borrowed(v_00_u03b1s_304_, v_n_318_);
lean_inc(v___x_321_);
v___x_322_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_319_, v___x_320_, v___x_321_, v_00_u03b2_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v_i_305_ = v_n_318_;
v_00_u03b2_306_ = v_a_323_;
goto _start;
}
else
{
lean_dec(v_n_318_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_325_, lean_object* v_i_326_, lean_object* v_00_u03b2_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_325_, v_i_326_, v_00_u03b2_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec_ref(v_00_u03b1s_325_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_336_, lean_object* v_i_337_, lean_object* v_00_u03b2_338_, lean_object* v_h_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_336_, v_i_337_, v_00_u03b2_338_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_348_, lean_object* v_i_349_, lean_object* v_00_u03b2_350_, lean_object* v_h_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_348_, v_i_349_, v_00_u03b2_350_, v_h_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec_ref(v_00_u03b1s_348_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_360_, lean_object* v_00_u03b2_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_array_get_size(v_00_u03b1s_360_);
v___x_370_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_360_, v___x_369_, v_00_u03b2_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_371_, lean_object* v_00_u03b2_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_371_, v_00_u03b2_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec_ref(v_00_u03b1s_371_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_381_, lean_object* v_subst_382_, size_t v_sz_383_, size_t v_i_384_, lean_object* v_bs_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_usize_dec_lt(v_i_384_, v_sz_383_);
if (v___x_386_ == 0)
{
return v_bs_385_;
}
else
{
lean_object* v___x_387_; lean_object* v_v_388_; lean_object* v___x_389_; lean_object* v_bs_x27_390_; lean_object* v___x_391_; lean_object* v___x_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v___x_387_ = l_Lean_instInhabitedExpr;
v_v_388_ = lean_array_uget(v_bs_385_, v_i_384_);
v___x_389_ = lean_unsigned_to_nat(0u);
v_bs_x27_390_ = lean_array_uset(v_bs_385_, v_i_384_, v___x_389_);
v___x_391_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_381_, v_v_388_);
lean_dec(v_v_388_);
v___x_392_ = lean_array_get_borrowed(v___x_387_, v_subst_382_, v___x_391_);
lean_dec(v___x_391_);
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_add(v_i_384_, v___x_393_);
lean_inc(v___x_392_);
v___x_395_ = lean_array_uset(v_bs_x27_390_, v_i_384_, v___x_392_);
v_i_384_ = v___x_394_;
v_bs_385_ = v___x_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_397_, lean_object* v_subst_398_, lean_object* v_sz_399_, lean_object* v_i_400_, lean_object* v_bs_401_){
_start:
{
size_t v_sz_boxed_402_; size_t v_i_boxed_403_; lean_object* v_res_404_; 
v_sz_boxed_402_ = lean_unbox_usize(v_sz_399_);
lean_dec(v_sz_399_);
v_i_boxed_403_ = lean_unbox_usize(v_i_400_);
lean_dec(v_i_400_);
v_res_404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_397_, v_subst_398_, v_sz_boxed_402_, v_i_boxed_403_, v_bs_401_);
lean_dec_ref(v_subst_398_);
lean_dec(v_fvarIdToPos_397_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_405_, size_t v_i_406_, lean_object* v_bs_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_usize_dec_lt(v_i_406_, v_sz_405_);
if (v___x_408_ == 0)
{
return v_bs_407_;
}
else
{
lean_object* v_v_409_; lean_object* v___x_410_; lean_object* v_bs_x27_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v_v_409_ = lean_array_uget(v_bs_407_, v_i_406_);
v___x_410_ = lean_unsigned_to_nat(0u);
v_bs_x27_411_ = lean_array_uset(v_bs_407_, v_i_406_, v___x_410_);
v___x_412_ = l_Lean_mkFVar(v_v_409_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_406_, v___x_413_);
v___x_415_ = lean_array_uset(v_bs_x27_411_, v_i_406_, v___x_412_);
v_i_406_ = v___x_414_;
v_bs_407_ = v___x_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_bs_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_421_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_420_, v_i_boxed_421_, v_bs_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
v___x_432_ = lean_apply_8(v_k_423_, v_b_426_, v___y_424_, v___y_425_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, lean_box(0));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_433_, v___y_434_, v___y_435_, v_b_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_443_, uint8_t v_bi_444_, lean_object* v_type_445_, lean_object* v_k_446_, uint8_t v_kind_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___f_455_; lean_object* v___x_456_; 
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_455_, 0, v_k_446_);
lean_closure_set(v___f_455_, 1, v___y_448_);
lean_closure_set(v___f_455_, 2, v___y_449_);
v___x_456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_443_, v_bi_444_, v_type_445_, v___f_455_, v_kind_447_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_456_) == 0)
{
return v___x_456_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_465_, lean_object* v_bi_466_, lean_object* v_type_467_, lean_object* v_k_468_, lean_object* v_kind_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v_bi_boxed_477_; uint8_t v_kind_boxed_478_; lean_object* v_res_479_; 
v_bi_boxed_477_ = lean_unbox(v_bi_466_);
v_kind_boxed_478_ = lean_unbox(v_kind_469_);
v_res_479_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_465_, v_bi_boxed_477_, v_type_467_, v_k_468_, v_kind_boxed_478_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_480_, lean_object* v_type_481_, lean_object* v_k_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = 0;
v___x_491_ = 0;
v___x_492_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_480_, v___x_490_, v_type_481_, v_k_482_, v___x_491_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_493_, lean_object* v_type_494_, lean_object* v_k_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_493_, v_type_494_, v_k_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_504_, lean_object* v_k_505_, lean_object* v_fallback_506_){
_start:
{
if (lean_obj_tag(v_t_504_) == 0)
{
lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v_l_509_; lean_object* v_r_510_; uint8_t v___x_511_; 
v_k_507_ = lean_ctor_get(v_t_504_, 1);
v_v_508_ = lean_ctor_get(v_t_504_, 2);
v_l_509_ = lean_ctor_get(v_t_504_, 3);
v_r_510_ = lean_ctor_get(v_t_504_, 4);
v___x_511_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_505_, v_k_507_);
switch(v___x_511_)
{
case 0:
{
v_t_504_ = v_l_509_;
goto _start;
}
case 1:
{
lean_inc(v_v_508_);
return v_v_508_;
}
default: 
{
v_t_504_ = v_r_510_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_506_);
return v_fallback_506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_514_, lean_object* v_k_515_, lean_object* v_fallback_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_514_, v_k_515_, v_fallback_516_);
lean_dec(v_fallback_516_);
lean_dec(v_k_515_);
lean_dec(v_t_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_518_, size_t v_sz_519_, size_t v_i_520_, lean_object* v_bs_521_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_lt(v_i_520_, v_sz_519_);
if (v___x_522_ == 0)
{
return v_bs_521_;
}
else
{
lean_object* v_v_523_; lean_object* v___x_524_; lean_object* v_bs_x27_525_; lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v_v_523_ = lean_array_uget(v_bs_521_, v_i_520_);
v___x_524_ = lean_unsigned_to_nat(0u);
v_bs_x27_525_ = lean_array_uset(v_bs_521_, v_i_520_, v___x_524_);
v___x_526_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_518_, v_v_523_, v___x_524_);
lean_dec(v_v_523_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_520_, v___x_527_);
v___x_529_ = lean_array_uset(v_bs_x27_525_, v_i_520_, v___x_526_);
v_i_520_ = v___x_528_;
v_bs_521_ = v___x_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_531_, lean_object* v_sz_532_, lean_object* v_i_533_, lean_object* v_bs_534_){
_start:
{
size_t v_sz_boxed_535_; size_t v_i_boxed_536_; lean_object* v_res_537_; 
v_sz_boxed_535_ = lean_unbox_usize(v_sz_532_);
lean_dec(v_sz_532_);
v_i_boxed_536_ = lean_unbox_usize(v_i_533_);
lean_dec(v_i_533_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_531_, v_sz_boxed_535_, v_i_boxed_536_, v_bs_534_);
lean_dec(v_fvarIdToPos_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_547_ = _args[0];
lean_object* v_subst_548_ = _args[1];
lean_object* v_sz_549_ = _args[2];
lean_object* v___x_550_ = _args[3];
lean_object* v_fvarIds_551_ = _args[4];
lean_object* v_x_552_ = _args[5];
lean_object* v_xs_553_ = _args[6];
lean_object* v_xs_x27_554_ = _args[7];
lean_object* v_args_555_ = _args[8];
lean_object* v_a_556_ = _args[9];
lean_object* v_types_557_ = _args[10];
lean_object* v_a_558_ = _args[11];
lean_object* v_varDeps_559_ = _args[12];
lean_object* v_varPos_560_ = _args[13];
lean_object* v_haveExpr_561_ = _args[14];
lean_object* v_body_562_ = _args[15];
lean_object* v_x_x27_563_ = _args[16];
lean_object* v___y_564_ = _args[17];
lean_object* v___y_565_ = _args[18];
lean_object* v___y_566_ = _args[19];
lean_object* v___y_567_ = _args[20];
lean_object* v___y_568_ = _args[21];
lean_object* v___y_569_ = _args[22];
lean_object* v___y_570_ = _args[23];
_start:
{
size_t v_sz_boxed_571_; size_t v___x_6407__boxed_572_; lean_object* v_res_573_; 
v_sz_boxed_571_ = lean_unbox_usize(v_sz_549_);
lean_dec(v_sz_549_);
v___x_6407__boxed_572_ = lean_unbox_usize(v___x_550_);
lean_dec(v___x_550_);
v_res_573_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_547_, v_subst_548_, v_sz_boxed_571_, v___x_6407__boxed_572_, v_fvarIds_551_, v_x_552_, v_xs_553_, v_xs_x27_554_, v_args_555_, v_a_556_, v_types_557_, v_a_558_, v_varDeps_559_, v_varPos_560_, v_haveExpr_561_, v_body_562_, v_x_x27_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_v_574_, lean_object* v_fvarIdToPos_575_, uint8_t v_nondep_576_, lean_object* v_t_577_, lean_object* v_subst_578_, lean_object* v_xs_579_, lean_object* v_xs_x27_580_, lean_object* v_args_581_, lean_object* v_types_582_, lean_object* v_varDeps_583_, lean_object* v_haveExpr_584_, lean_object* v_body_585_, lean_object* v_declName_586_, lean_object* v_x_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_fvarIds_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v_varPos_598_; lean_object* v_ys_599_; uint8_t v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; 
lean_inc_ref(v_v_574_);
v_fvarIds_595_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_574_, v_fvarIdToPos_575_);
v_sz_596_ = lean_array_size(v_fvarIds_595_);
v___x_597_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_595_, 2);
v_varPos_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_575_, v_sz_596_, v___x_597_, v_fvarIds_595_);
v_ys_599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_596_, v___x_597_, v_fvarIds_595_);
v___x_600_ = 0;
v___x_601_ = 1;
v___x_602_ = l_Lean_Meta_mkLambdaFVars(v_ys_599_, v_v_574_, v___x_600_, v_nondep_576_, v___x_600_, v_nondep_576_, v___x_601_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = l_Lean_Meta_mkForallFVars(v_ys_599_, v_t_577_, v___x_600_, v_nondep_576_, v_nondep_576_, v___x_601_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec_ref(v_ys_599_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = l_Lean_Meta_Sym_shareCommonInc(v_a_605_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___f_610_; lean_object* v___x_611_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc_n(v_a_607_, 2);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_box_usize(v_sz_596_);
v___x_609_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_610_, 0, v_fvarIdToPos_575_);
lean_closure_set(v___f_610_, 1, v_subst_578_);
lean_closure_set(v___f_610_, 2, v___x_608_);
lean_closure_set(v___f_610_, 3, v___x_609_);
lean_closure_set(v___f_610_, 4, v_fvarIds_595_);
lean_closure_set(v___f_610_, 5, v_x_587_);
lean_closure_set(v___f_610_, 6, v_xs_579_);
lean_closure_set(v___f_610_, 7, v_xs_x27_580_);
lean_closure_set(v___f_610_, 8, v_args_581_);
lean_closure_set(v___f_610_, 9, v_a_603_);
lean_closure_set(v___f_610_, 10, v_types_582_);
lean_closure_set(v___f_610_, 11, v_a_607_);
lean_closure_set(v___f_610_, 12, v_varDeps_583_);
lean_closure_set(v___f_610_, 13, v_varPos_598_);
lean_closure_set(v___f_610_, 14, v_haveExpr_584_);
lean_closure_set(v___f_610_, 15, v_body_585_);
v___x_611_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_586_, v_a_607_, v___f_610_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_611_;
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_603_);
lean_dec_ref(v_varPos_598_);
lean_dec_ref(v_fvarIds_595_);
lean_dec_ref(v_x_587_);
lean_dec(v_declName_586_);
lean_dec_ref(v_body_585_);
lean_dec_ref(v_haveExpr_584_);
lean_dec_ref(v_varDeps_583_);
lean_dec_ref(v_types_582_);
lean_dec_ref(v_args_581_);
lean_dec_ref(v_xs_x27_580_);
lean_dec_ref(v_xs_579_);
lean_dec_ref(v_subst_578_);
lean_dec(v_fvarIdToPos_575_);
v_a_612_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_606_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_606_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_a_603_);
lean_dec_ref(v_varPos_598_);
lean_dec_ref(v_fvarIds_595_);
lean_dec_ref(v_x_587_);
lean_dec(v_declName_586_);
lean_dec_ref(v_body_585_);
lean_dec_ref(v_haveExpr_584_);
lean_dec_ref(v_varDeps_583_);
lean_dec_ref(v_types_582_);
lean_dec_ref(v_args_581_);
lean_dec_ref(v_xs_x27_580_);
lean_dec_ref(v_xs_579_);
lean_dec_ref(v_subst_578_);
lean_dec(v_fvarIdToPos_575_);
v_a_620_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_604_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_604_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_ys_599_);
lean_dec_ref(v_varPos_598_);
lean_dec_ref(v_fvarIds_595_);
lean_dec_ref(v_x_587_);
lean_dec(v_declName_586_);
lean_dec_ref(v_body_585_);
lean_dec_ref(v_haveExpr_584_);
lean_dec_ref(v_varDeps_583_);
lean_dec_ref(v_types_582_);
lean_dec_ref(v_args_581_);
lean_dec_ref(v_xs_x27_580_);
lean_dec_ref(v_xs_579_);
lean_dec_ref(v_subst_578_);
lean_dec_ref(v_t_577_);
lean_dec(v_fvarIdToPos_575_);
v_a_628_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_602_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_602_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_v_636_ = _args[0];
lean_object* v_fvarIdToPos_637_ = _args[1];
lean_object* v_nondep_638_ = _args[2];
lean_object* v_t_639_ = _args[3];
lean_object* v_subst_640_ = _args[4];
lean_object* v_xs_641_ = _args[5];
lean_object* v_xs_x27_642_ = _args[6];
lean_object* v_args_643_ = _args[7];
lean_object* v_types_644_ = _args[8];
lean_object* v_varDeps_645_ = _args[9];
lean_object* v_haveExpr_646_ = _args[10];
lean_object* v_body_647_ = _args[11];
lean_object* v_declName_648_ = _args[12];
lean_object* v_x_649_ = _args[13];
lean_object* v___y_650_ = _args[14];
lean_object* v___y_651_ = _args[15];
lean_object* v___y_652_ = _args[16];
lean_object* v___y_653_ = _args[17];
lean_object* v___y_654_ = _args[18];
lean_object* v___y_655_ = _args[19];
lean_object* v___y_656_ = _args[20];
_start:
{
uint8_t v_nondep_6434__boxed_657_; lean_object* v_res_658_; 
v_nondep_6434__boxed_657_ = lean_unbox(v_nondep_638_);
v_res_658_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_v_636_, v_fvarIdToPos_637_, v_nondep_6434__boxed_657_, v_t_639_, v_subst_640_, v_xs_641_, v_xs_x27_642_, v_args_643_, v_types_644_, v_varDeps_645_, v_haveExpr_646_, v_body_647_, v_declName_648_, v_x_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_659_, lean_object* v_e_660_, lean_object* v_xs_661_, lean_object* v_xs_x27_662_, lean_object* v_args_663_, lean_object* v_subst_664_, lean_object* v_types_665_, lean_object* v_varDeps_666_, lean_object* v_fvarIdToPos_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; 
if (lean_obj_tag(v_e_660_) == 8)
{
uint8_t v_nondep_762_; 
v_nondep_762_ = lean_ctor_get_uint8(v_e_660_, sizeof(void*)*4 + 8);
if (v_nondep_762_ == 1)
{
lean_object* v_declName_763_; lean_object* v_type_764_; lean_object* v_value_765_; lean_object* v_body_766_; lean_object* v_t_767_; lean_object* v_v_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; 
v_declName_763_ = lean_ctor_get(v_e_660_, 0);
lean_inc_n(v_declName_763_, 2);
v_type_764_ = lean_ctor_get(v_e_660_, 1);
lean_inc_ref(v_type_764_);
v_value_765_ = lean_ctor_get(v_e_660_, 2);
lean_inc_ref(v_value_765_);
v_body_766_ = lean_ctor_get(v_e_660_, 3);
lean_inc_ref(v_body_766_);
lean_dec_ref_known(v_e_660_, 4);
v_t_767_ = lean_expr_instantiate_rev(v_type_764_, v_xs_661_);
lean_dec_ref(v_type_764_);
v_v_768_ = lean_expr_instantiate_rev(v_value_765_, v_xs_661_);
lean_dec_ref(v_value_765_);
v___x_769_ = lean_box(v_nondep_762_);
lean_inc_ref(v_t_767_);
v___f_770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 21, 13);
lean_closure_set(v___f_770_, 0, v_v_768_);
lean_closure_set(v___f_770_, 1, v_fvarIdToPos_667_);
lean_closure_set(v___f_770_, 2, v___x_769_);
lean_closure_set(v___f_770_, 3, v_t_767_);
lean_closure_set(v___f_770_, 4, v_subst_664_);
lean_closure_set(v___f_770_, 5, v_xs_661_);
lean_closure_set(v___f_770_, 6, v_xs_x27_662_);
lean_closure_set(v___f_770_, 7, v_args_663_);
lean_closure_set(v___f_770_, 8, v_types_665_);
lean_closure_set(v___f_770_, 9, v_varDeps_666_);
lean_closure_set(v___f_770_, 10, v_haveExpr_659_);
lean_closure_set(v___f_770_, 11, v_body_766_);
lean_closure_set(v___f_770_, 12, v_declName_763_);
v___x_771_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_763_, v_t_767_, v___f_770_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_771_;
}
else
{
lean_dec(v_fvarIdToPos_667_);
lean_dec_ref(v_xs_661_);
v___y_676_ = v_a_668_;
v___y_677_ = v_a_669_;
v___y_678_ = v_a_670_;
v___y_679_ = v_a_671_;
v___y_680_ = v_a_672_;
v___y_681_ = v_a_673_;
goto v___jp_675_;
}
}
else
{
lean_dec(v_fvarIdToPos_667_);
lean_dec_ref(v_xs_661_);
v___y_676_ = v_a_668_;
v___y_677_ = v_a_669_;
v___y_678_ = v_a_670_;
v___y_679_ = v_a_671_;
v___y_680_ = v_a_672_;
v___y_681_ = v_a_673_;
goto v___jp_675_;
}
v___jp_675_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_size(v_subst_664_);
v___x_684_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_660_, v___x_682_, v___x_683_, v_subst_664_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_n(v_a_685_, 2);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = l_Lean_Meta_Sym_inferType(v_a_685_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc_n(v_a_687_, 2);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_687_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
lean_inc(v_a_687_);
v___x_690_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_665_, v_a_687_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec_ref(v_types_665_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_662_, v_a_685_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = l_Lean_mkAppN(v_a_693_, v_args_663_);
lean_dec_ref(v_args_663_);
v___x_695_ = l_Lean_Meta_Sym_shareCommonInc(v___x_694_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_713_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_713_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_713_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_713_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_701_ = lean_box(0);
lean_inc(v_a_689_);
v___x_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_702_, 0, v_a_689_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
lean_inc_ref(v___x_702_);
v___x_703_ = l_Lean_mkConst(v___x_700_, v___x_702_);
lean_inc(v_a_696_);
lean_inc_ref(v_haveExpr_659_);
lean_inc_n(v_a_687_, 2);
v___x_704_ = l_Lean_mkApp3(v___x_703_, v_a_687_, v_haveExpr_659_, v_a_696_);
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_706_ = l_Lean_mkConst(v___x_705_, v___x_702_);
v___x_707_ = l_Lean_mkAppB(v___x_706_, v_a_687_, v_haveExpr_659_);
v___x_708_ = l_Lean_Meta_mkExpectedPropHint(v___x_707_, v___x_704_);
v___x_709_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_709_, 0, v_a_687_);
lean_ctor_set(v___x_709_, 1, v_a_689_);
lean_ctor_set(v___x_709_, 2, v_a_696_);
lean_ctor_set(v___x_709_, 3, v___x_708_);
lean_ctor_set(v___x_709_, 4, v_varDeps_666_);
lean_ctor_set(v___x_709_, 5, v_a_691_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_709_);
v___x_711_ = v___x_698_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_691_);
lean_dec(v_a_689_);
lean_dec(v_a_687_);
lean_dec_ref(v_varDeps_666_);
lean_dec_ref(v_haveExpr_659_);
v_a_714_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_695_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_695_);
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
lean_dec(v_a_691_);
lean_dec(v_a_689_);
lean_dec(v_a_687_);
lean_dec_ref(v_varDeps_666_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v_haveExpr_659_);
v_a_722_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_692_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_692_);
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
lean_dec(v_a_689_);
lean_dec(v_a_687_);
lean_dec(v_a_685_);
lean_dec_ref(v_varDeps_666_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v_xs_x27_662_);
lean_dec_ref(v_haveExpr_659_);
v_a_730_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_690_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_690_);
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
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_687_);
lean_dec(v_a_685_);
lean_dec_ref(v_varDeps_666_);
lean_dec_ref(v_types_665_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v_xs_x27_662_);
lean_dec_ref(v_haveExpr_659_);
v_a_738_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_688_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_688_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
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
lean_dec(v_a_685_);
lean_dec_ref(v_varDeps_666_);
lean_dec_ref(v_types_665_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v_xs_x27_662_);
lean_dec_ref(v_haveExpr_659_);
v_a_746_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_686_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_686_);
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
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_varDeps_666_);
lean_dec_ref(v_types_665_);
lean_dec_ref(v_args_663_);
lean_dec_ref(v_xs_x27_662_);
lean_dec_ref(v_haveExpr_659_);
v_a_754_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_684_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_684_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_772_, lean_object* v_subst_773_, size_t v_sz_774_, size_t v___x_775_, lean_object* v_fvarIds_776_, lean_object* v_x_777_, lean_object* v_xs_778_, lean_object* v_xs_x27_779_, lean_object* v_args_780_, lean_object* v_a_781_, lean_object* v_types_782_, lean_object* v_a_783_, lean_object* v_varDeps_784_, lean_object* v_varPos_785_, lean_object* v_haveExpr_786_, lean_object* v_body_787_, lean_object* v_x_x27_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_772_, v_subst_773_, v_sz_774_, v___x_775_, v_fvarIds_776_);
lean_inc_ref(v_x_x27_788_);
v___x_797_ = l_Lean_mkAppN(v_x_x27_788_, v___x_796_);
lean_dec_ref(v___x_796_);
v___x_798_ = l_Lean_Meta_Sym_shareCommonInc(v___x_797_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_Expr_fvarId_x21(v_x_777_);
v___x_801_ = lean_array_get_size(v_xs_778_);
v___x_802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_800_, v___x_801_, v_fvarIdToPos_772_);
v___x_803_ = lean_array_push(v_xs_778_, v_x_777_);
v___x_804_ = lean_array_push(v_xs_x27_779_, v_x_x27_788_);
v___x_805_ = lean_array_push(v_args_780_, v_a_781_);
v___x_806_ = lean_array_push(v_subst_773_, v_a_799_);
v___x_807_ = lean_array_push(v_types_782_, v_a_783_);
v___x_808_ = lean_array_push(v_varDeps_784_, v_varPos_785_);
v___x_809_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_786_, v_body_787_, v___x_803_, v___x_804_, v___x_805_, v___x_806_, v___x_807_, v___x_808_, v___x_802_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_x_x27_788_);
lean_dec_ref(v_body_787_);
lean_dec_ref(v_haveExpr_786_);
lean_dec_ref(v_varPos_785_);
lean_dec_ref(v_varDeps_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_types_782_);
lean_dec_ref(v_a_781_);
lean_dec_ref(v_args_780_);
lean_dec_ref(v_xs_x27_779_);
lean_dec_ref(v_xs_778_);
lean_dec_ref(v_x_777_);
lean_dec_ref(v_subst_773_);
lean_dec(v_fvarIdToPos_772_);
v_a_810_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_798_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_798_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_818_, lean_object* v_e_819_, lean_object* v_xs_820_, lean_object* v_xs_x27_821_, lean_object* v_args_822_, lean_object* v_subst_823_, lean_object* v_types_824_, lean_object* v_varDeps_825_, lean_object* v_fvarIdToPos_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_818_, v_e_819_, v_xs_820_, v_xs_x27_821_, v_args_822_, v_subst_823_, v_types_824_, v_varDeps_825_, v_fvarIdToPos_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_835_, lean_object* v_t_836_, lean_object* v_k_837_, lean_object* v_fallback_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_836_, v_k_837_, v_fallback_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_840_, lean_object* v_t_841_, lean_object* v_k_842_, lean_object* v_fallback_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_840_, v_t_841_, v_k_842_, v_fallback_843_);
lean_dec(v_fallback_843_);
lean_dec(v_k_842_);
lean_dec(v_t_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_845_, lean_object* v_name_846_, uint8_t v_bi_847_, lean_object* v_type_848_, lean_object* v_k_849_, uint8_t v_kind_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_846_, v_bi_847_, v_type_848_, v_k_849_, v_kind_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_859_, lean_object* v_name_860_, lean_object* v_bi_861_, lean_object* v_type_862_, lean_object* v_k_863_, lean_object* v_kind_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_bi_boxed_872_; uint8_t v_kind_boxed_873_; lean_object* v_res_874_; 
v_bi_boxed_872_ = lean_unbox(v_bi_861_);
v_kind_boxed_873_ = lean_unbox(v_kind_864_);
v_res_874_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_859_, v_name_860_, v_bi_boxed_872_, v_type_862_, v_k_863_, v_kind_boxed_873_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_875_, lean_object* v_name_876_, lean_object* v_type_877_, lean_object* v_k_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_876_, v_type_877_, v_k_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_887_, lean_object* v_name_888_, lean_object* v_type_889_, lean_object* v_k_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_887_, v_name_888_, v_type_889_, v_k_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_910_ = lean_box(1);
lean_inc_ref(v_haveExpr_901_);
v___x_911_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_901_, v_haveExpr_901_, v___x_909_, v___x_909_, v___x_909_, v___x_909_, v___x_909_, v___x_909_, v___x_910_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_921_, lean_object* v_n_922_){
_start:
{
lean_object* v_zero_923_; uint8_t v_isZero_924_; 
v_zero_923_ = lean_unsigned_to_nat(0u);
v_isZero_924_ = lean_nat_dec_eq(v_n_922_, v_zero_923_);
if (v_isZero_924_ == 1)
{
lean_dec(v_n_922_);
return v_type_921_;
}
else
{
lean_object* v_one_925_; lean_object* v_n_926_; lean_object* v___x_927_; 
v_one_925_ = lean_unsigned_to_nat(1u);
v_n_926_ = lean_nat_sub(v_n_922_, v_one_925_);
lean_dec(v_n_922_);
v___x_927_ = l_Lean_Expr_bindingBody_x21(v_type_921_);
lean_dec_ref(v_type_921_);
v_type_921_ = v___x_927_;
v_n_922_ = v_n_926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(lean_object* v_idx_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Lean_Expr_bvar___override(v_idx_929_);
v___x_932_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_931_, v___y_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_idx_933_, uint8_t v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v_idx_933_, v___y_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___boxed(lean_object* v_idx_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v___y_24940__boxed_942_; lean_object* v_res_943_; 
v___y_24940__boxed_942_ = lean_unbox(v___y_939_);
v_res_943_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(v_idx_938_, v___y_24940__boxed_942_, v___y_940_, v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_943_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0(void){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_HashMap_instInhabited___redArg();
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_msg_945_, uint8_t v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_1486__overap_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_949_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0);
v___f_950_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_950_, 0, v___x_949_);
v___f_951_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_951_, 0, v___f_950_);
v___f_952_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_952_, 0, v___f_951_);
v___x_1486__overap_953_ = lean_panic_fn_borrowed(v___f_952_, v_msg_945_);
lean_dec_ref(v___f_952_);
v___x_954_ = lean_box(v___y_946_);
lean_inc_ref(v___y_947_);
v___x_955_ = lean_apply_3(v___x_1486__overap_953_, v___x_954_, v___y_947_, v___y_948_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v___y_24953__boxed_960_; lean_object* v_res_961_; 
v___y_24953__boxed_960_ = lean_unbox(v___y_957_);
v_res_961_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_msg_956_, v___y_24953__boxed_960_, v___y_958_, v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_961_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_1948__overap_972_; lean_object* v___x_973_; 
v___x_971_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0);
v___x_1948__overap_972_ = lean_panic_fn_borrowed(v___x_971_, v_msg_963_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
v___x_973_ = lean_apply_7(v___x_1948__overap_972_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_msg_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object* v_x_983_, lean_object* v_t_984_, lean_object* v_v_985_, lean_object* v_b_986_, uint8_t v_nondep_987_, lean_object* v___y_988_, uint8_t v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___y_993_; lean_object* v___y_994_; 
if (v___y_989_ == 0)
{
v___y_993_ = v___y_988_;
v___y_994_ = v___y_991_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_984_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 2);
v___x_1018_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_985_, v___y_989_, v___y_990_, v_a_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 1);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 2);
v___x_1020_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_986_, v___y_989_, v___y_990_, v_a_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 2);
v___y_993_ = v___y_988_;
v___y_994_ = v_a_1021_;
goto v___jp_992_;
}
else
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v___y_988_);
lean_dec_ref(v_b_986_);
lean_dec_ref(v_v_985_);
lean_dec_ref(v_t_984_);
lean_dec(v_x_983_);
v_a_1022_ = lean_ctor_get(v___x_1020_, 0);
v_a_1023_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1020_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
lean_dec(v___x_1020_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1022_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v___y_988_);
lean_dec_ref(v_b_986_);
lean_dec_ref(v_v_985_);
lean_dec_ref(v_t_984_);
lean_dec(v_x_983_);
v_a_1031_ = lean_ctor_get(v___x_1018_, 0);
v_a_1032_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1018_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_inc(v_a_1031_);
lean_dec(v___x_1018_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1031_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec_ref(v___y_988_);
lean_dec_ref(v_b_986_);
lean_dec_ref(v_v_985_);
lean_dec_ref(v_t_984_);
lean_dec(v_x_983_);
v_a_1040_ = lean_ctor_get(v___x_1016_, 0);
v_a_1041_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1016_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_inc(v_a_1040_);
lean_dec(v___x_1016_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1040_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
v___jp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = l_Lean_Expr_letE___override(v_x_983_, v_t_984_, v_v_985_, v_b_986_, v_nondep_987_);
v___x_996_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_995_, v___y_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1006_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_a_998_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1000_ = v___x_996_;
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_997_);
lean_ctor_set(v___x_1002_, 1, v___y_993_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1002_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_a_998_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v___y_993_);
v_a_1007_ = lean_ctor_get(v___x_996_, 0);
v_a_1008_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_996_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_inc(v_a_1007_);
lean_dec(v___x_996_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1007_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object* v_x_1049_, lean_object* v_t_1050_, lean_object* v_v_1051_, lean_object* v_b_1052_, lean_object* v_nondep_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v_nondep_boxed_1058_; uint8_t v___y_25004__boxed_1059_; lean_object* v_res_1060_; 
v_nondep_boxed_1058_ = lean_unbox(v_nondep_1053_);
v___y_25004__boxed_1059_ = lean_unbox(v___y_1055_);
v_res_1060_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_x_1049_, v_t_1050_, v_v_1051_, v_b_1052_, v_nondep_boxed_1058_, v___y_1054_, v___y_25004__boxed_1059_, v___y_1056_, v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object* v_x_1061_, uint8_t v_bi_1062_, lean_object* v_t_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, uint8_t v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___y_1070_; lean_object* v___y_1071_; 
if (v___y_1066_ == 0)
{
v___y_1070_ = v___y_1065_;
v___y_1071_ = v___y_1068_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1063_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 1);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 2);
v___x_1095_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1064_, v___y_1066_, v___y_1067_, v_a_1094_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 1);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 2);
v___y_1070_ = v___y_1065_;
v___y_1071_ = v_a_1096_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_1097_; lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_t_1063_);
lean_dec(v_x_1061_);
v_a_1097_ = lean_ctor_get(v___x_1095_, 0);
v_a_1098_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1095_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_inc(v_a_1097_);
lean_dec(v___x_1095_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1097_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_t_1063_);
lean_dec(v_x_1061_);
v_a_1106_ = lean_ctor_get(v___x_1093_, 0);
v_a_1107_ = lean_ctor_get(v___x_1093_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1093_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_inc(v_a_1106_);
lean_dec(v___x_1093_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1106_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
v___jp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = l_Lean_Expr_lam___override(v_x_1061_, v_t_1063_, v_b_1064_, v_bi_1062_);
v___x_1073_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1072_, v___y_1071_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_a_1075_ = lean_ctor_get(v___x_1073_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v___x_1073_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_a_1074_);
lean_ctor_set(v___x_1079_, 1, v___y_1070_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v___y_1070_);
v_a_1084_ = lean_ctor_get(v___x_1073_, 0);
v_a_1085_ = lean_ctor_get(v___x_1073_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1073_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_inc(v_a_1084_);
lean_dec(v___x_1073_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1084_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object* v_x_1115_, lean_object* v_bi_1116_, lean_object* v_t_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v_bi_boxed_1123_; uint8_t v___y_25133__boxed_1124_; lean_object* v_res_1125_; 
v_bi_boxed_1123_ = lean_unbox(v_bi_1116_);
v___y_25133__boxed_1124_ = lean_unbox(v___y_1120_);
v_res_1125_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_x_1115_, v_bi_boxed_1123_, v_t_1117_, v_b_1118_, v___y_1119_, v___y_25133__boxed_1124_, v___y_1121_, v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object* v_x_1126_, uint8_t v_bi_1127_, lean_object* v_t_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_, uint8_t v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___y_1135_; lean_object* v___y_1136_; 
if (v___y_1131_ == 0)
{
v___y_1135_ = v___y_1130_;
v___y_1136_ = v___y_1133_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1128_, v___y_1131_, v___y_1132_, v___y_1133_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 1);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 2);
v___x_1160_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1129_, v___y_1131_, v___y_1132_, v_a_1159_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 2);
v___y_1135_ = v___y_1130_;
v___y_1136_ = v_a_1161_;
goto v___jp_1134_;
}
else
{
lean_object* v_a_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_b_1129_);
lean_dec_ref(v_t_1128_);
lean_dec(v_x_1126_);
v_a_1162_ = lean_ctor_get(v___x_1160_, 0);
v_a_1163_ = lean_ctor_get(v___x_1160_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1160_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_inc(v_a_1162_);
lean_dec(v___x_1160_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1162_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_b_1129_);
lean_dec_ref(v_t_1128_);
lean_dec(v_x_1126_);
v_a_1171_ = lean_ctor_get(v___x_1158_, 0);
v_a_1172_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1158_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1171_);
lean_dec(v___x_1158_);
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
v___jp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = l_Lean_Expr_forallE___override(v_x_1126_, v_t_1128_, v_b_1129_, v_bi_1127_);
v___x_1138_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1137_, v___y_1136_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1148_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_a_1140_ = lean_ctor_get(v___x_1138_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1142_ = v___x_1138_;
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_a_1139_);
lean_ctor_set(v___x_1144_, 1, v___y_1135_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_a_1140_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v___y_1135_);
v_a_1149_ = lean_ctor_get(v___x_1138_, 0);
v_a_1150_ = lean_ctor_get(v___x_1138_, 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1138_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_inc(v_a_1149_);
lean_dec(v___x_1138_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1149_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object* v_x_1180_, lean_object* v_bi_1181_, lean_object* v_t_1182_, lean_object* v_b_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v_bi_boxed_1188_; uint8_t v___y_25239__boxed_1189_; lean_object* v_res_1190_; 
v_bi_boxed_1188_ = lean_unbox(v_bi_1181_);
v___y_25239__boxed_1189_ = lean_unbox(v___y_1185_);
v_res_1190_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_x_1180_, v_bi_boxed_1188_, v_t_1182_, v_b_1183_, v___y_1184_, v___y_25239__boxed_1189_, v___y_1186_, v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object* v_f_1191_, lean_object* v_a_1192_, lean_object* v___y_1193_, uint8_t v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___y_1198_; lean_object* v___y_1199_; 
if (v___y_1194_ == 0)
{
v___y_1198_ = v___y_1193_;
v___y_1199_ = v___y_1196_;
goto v___jp_1197_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1191_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1223_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 1);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 2);
v___x_1223_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1192_, v___y_1194_, v___y_1195_, v_a_1222_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 1);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 2);
v___y_1198_ = v___y_1193_;
v___y_1199_ = v_a_1224_;
goto v___jp_1197_;
}
else
{
lean_object* v_a_1225_; lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_a_1192_);
lean_dec_ref(v_f_1191_);
v_a_1225_ = lean_ctor_get(v___x_1223_, 0);
v_a_1226_ = lean_ctor_get(v___x_1223_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1223_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_inc(v_a_1225_);
lean_dec(v___x_1223_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1225_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_a_1192_);
lean_dec_ref(v_f_1191_);
v_a_1234_ = lean_ctor_get(v___x_1221_, 0);
v_a_1235_ = lean_ctor_get(v___x_1221_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1221_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_inc(v_a_1234_);
lean_dec(v___x_1221_);
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
v___jp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = l_Lean_Expr_app___override(v_f_1191_, v_a_1192_);
v___x_1201_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1200_, v___y_1199_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_a_1203_ = lean_ctor_get(v___x_1201_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_a_1202_);
lean_ctor_set(v___x_1207_, 1, v___y_1198_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_a_1203_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v___y_1198_);
v_a_1212_ = lean_ctor_get(v___x_1201_, 0);
v_a_1213_ = lean_ctor_get(v___x_1201_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1201_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_inc(v_a_1212_);
lean_dec(v___x_1201_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1212_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object* v_f_1243_, lean_object* v_a_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v___y_25345__boxed_1249_; lean_object* v_res_1250_; 
v___y_25345__boxed_1249_ = lean_unbox(v___y_1246_);
v_res_1250_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_f_1243_, v_a_1244_, v___y_1245_, v___y_25345__boxed_1249_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object* v_d_1251_, lean_object* v_e_1252_, lean_object* v___y_1253_, uint8_t v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___y_1258_; lean_object* v___y_1259_; 
if (v___y_1254_ == 0)
{
v___y_1258_ = v___y_1253_;
v___y_1259_ = v___y_1256_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1252_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 2);
v___y_1258_ = v___y_1253_;
v___y_1259_ = v_a_1282_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1283_; lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_e_1252_);
lean_dec(v_d_1251_);
v_a_1283_ = lean_ctor_get(v___x_1281_, 0);
v_a_1284_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1281_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_inc(v_a_1283_);
lean_dec(v___x_1281_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1283_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = l_Lean_Expr_mdata___override(v_d_1251_, v_e_1252_);
v___x_1261_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1260_, v___y_1259_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_a_1263_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1261_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_a_1262_);
lean_ctor_set(v___x_1267_, 1, v___y_1258_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_a_1263_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v___y_1258_);
v_a_1272_ = lean_ctor_get(v___x_1261_, 0);
v_a_1273_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1261_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_inc(v_a_1272_);
lean_dec(v___x_1261_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1272_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object* v_d_1292_, lean_object* v_e_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___y_25451__boxed_1298_; lean_object* v_res_1299_; 
v___y_25451__boxed_1298_ = lean_unbox(v___y_1295_);
v_res_1299_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_d_1292_, v_e_1293_, v___y_1294_, v___y_25451__boxed_1298_, v___y_1296_, v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(lean_object* v_msg_1307_, lean_object* v___y_1308_, uint8_t v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___f_1312_; lean_object* v___f_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_24463__overap_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___f_1312_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0));
v___f_1313_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1));
v___f_1314_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2));
v___x_1315_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3));
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___f_1312_);
v___x_1317_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4));
v___x_1318_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5));
v___x_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1316_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v___f_1313_);
lean_ctor_set(v___x_1319_, 3, v___f_1314_);
lean_ctor_set(v___x_1319_, 4, v___x_1318_);
v___x_1320_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6));
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = l_ReaderT_instMonad___redArg(v___x_1321_);
v___x_1323_ = l_ReaderT_instMonad___redArg(v___x_1322_);
lean_inc_ref_n(v___x_1323_, 6);
v___f_1324_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1324_, 0, v___x_1323_);
v___f_1325_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1325_, 0, v___x_1323_);
v___f_1326_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1326_, 0, v___x_1323_);
v___f_1327_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1327_, 0, v___x_1323_);
v___x_1328_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1328_, 0, lean_box(0));
lean_closure_set(v___x_1328_, 1, lean_box(0));
lean_closure_set(v___x_1328_, 2, v___x_1323_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___f_1324_);
v___x_1330_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1330_, 0, lean_box(0));
lean_closure_set(v___x_1330_, 1, lean_box(0));
lean_closure_set(v___x_1330_, 2, v___x_1323_);
v___x_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
lean_ctor_set(v___x_1331_, 2, v___f_1325_);
lean_ctor_set(v___x_1331_, 3, v___f_1326_);
lean_ctor_set(v___x_1331_, 4, v___f_1327_);
v___x_1332_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1332_, 0, lean_box(0));
lean_closure_set(v___x_1332_, 1, lean_box(0));
lean_closure_set(v___x_1332_, 2, v___x_1323_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_instInhabitedExpr;
v___x_1335_ = l_instInhabitedOfMonad___redArg(v___x_1333_, v___x_1334_);
v___x_24463__overap_1336_ = lean_panic_fn_borrowed(v___x_1335_, v_msg_1307_);
lean_dec(v___x_1335_);
v___x_1337_ = lean_box(v___y_1309_);
lean_inc_ref(v___y_1310_);
v___x_1338_ = lean_apply_4(v___x_24463__overap_1336_, v___y_1308_, v___x_1337_, v___y_1310_, v___y_1311_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___boxed(lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___y_25548__boxed_1344_; lean_object* v_res_1345_; 
v___y_25548__boxed_1344_ = lean_unbox(v___y_1341_);
v_res_1345_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v_msg_1339_, v___y_1340_, v___y_25548__boxed_1344_, v___y_1342_, v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object* v_structName_1346_, lean_object* v_idx_1347_, lean_object* v_struct_1348_, lean_object* v___y_1349_, uint8_t v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___y_1354_; lean_object* v___y_1355_; 
if (v___y_1350_ == 0)
{
v___y_1354_ = v___y_1349_;
v___y_1355_ = v___y_1352_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1348_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 2);
v___y_1354_ = v___y_1349_;
v___y_1355_ = v_a_1378_;
goto v___jp_1353_;
}
else
{
lean_object* v_a_1379_; lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v___y_1349_);
lean_dec_ref(v_struct_1348_);
lean_dec(v_idx_1347_);
lean_dec(v_structName_1346_);
v_a_1379_ = lean_ctor_get(v___x_1377_, 0);
v_a_1380_ = lean_ctor_get(v___x_1377_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1377_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_inc(v_a_1379_);
lean_dec(v___x_1377_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
v___jp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = l_Lean_Expr_proj___override(v_structName_1346_, v_idx_1347_, v_struct_1348_);
v___x_1357_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1356_, v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1367_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_a_1359_ = lean_ctor_get(v___x_1357_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1361_ = v___x_1357_;
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_a_1358_);
lean_ctor_set(v___x_1363_, 1, v___y_1354_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_a_1359_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v___y_1354_);
v_a_1368_ = lean_ctor_get(v___x_1357_, 0);
v_a_1369_ = lean_ctor_get(v___x_1357_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1357_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_inc(v_a_1368_);
lean_dec(v___x_1357_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1368_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object* v_structName_1388_, lean_object* v_idx_1389_, lean_object* v_struct_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v___y_25619__boxed_1395_; lean_object* v_res_1396_; 
v___y_25619__boxed_1395_ = lean_unbox(v___y_1392_);
v_res_1396_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_structName_1388_, v_idx_1389_, v_struct_1390_, v___y_1391_, v___y_25619__boxed_1395_, v___y_1393_, v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
else
{
lean_object* v_key_1400_; lean_object* v_value_1401_; lean_object* v_tail_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v_key_1400_ = lean_ctor_get(v_x_1398_, 0);
v_value_1401_ = lean_ctor_get(v_x_1398_, 1);
v_tail_1402_ = lean_ctor_get(v_x_1398_, 2);
v_fst_1403_ = lean_ctor_get(v_key_1400_, 0);
v_snd_1404_ = lean_ctor_get(v_key_1400_, 1);
v_fst_1405_ = lean_ctor_get(v_a_1397_, 0);
v_snd_1406_ = lean_ctor_get(v_a_1397_, 1);
v___x_1407_ = lean_ptr_addr(v_fst_1403_);
v___x_1408_ = lean_ptr_addr(v_fst_1405_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
v_x_1398_ = v_tail_1402_;
goto _start;
}
else
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_eq(v_snd_1404_, v_snd_1406_);
if (v___x_1411_ == 0)
{
v_x_1398_ = v_tail_1402_;
goto _start;
}
else
{
lean_object* v___x_1413_; 
lean_inc(v_value_1401_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_value_1401_);
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1414_, v_x_1415_);
lean_dec(v_x_1415_);
lean_dec_ref(v_a_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(lean_object* v_m_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_buckets_1419_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; uint64_t v___x_1426_; uint64_t v___x_1427_; uint64_t v___x_1428_; uint64_t v___x_1429_; uint64_t v___x_1430_; uint64_t v_fold_1431_; uint64_t v___x_1432_; uint64_t v___x_1433_; uint64_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_buckets_1419_ = lean_ctor_get(v_m_1417_, 1);
v_fst_1420_ = lean_ctor_get(v_a_1418_, 0);
v_snd_1421_ = lean_ctor_get(v_a_1418_, 1);
v___x_1422_ = lean_array_get_size(v_buckets_1419_);
v___x_1423_ = lean_ptr_addr(v_fst_1420_);
v___x_1424_ = ((size_t)3ULL);
v___x_1425_ = lean_usize_shift_right(v___x_1423_, v___x_1424_);
v___x_1426_ = lean_usize_to_uint64(v___x_1425_);
v___x_1427_ = lean_uint64_of_nat(v_snd_1421_);
v___x_1428_ = lean_uint64_mix_hash(v___x_1426_, v___x_1427_);
v___x_1429_ = 32ULL;
v___x_1430_ = lean_uint64_shift_right(v___x_1428_, v___x_1429_);
v_fold_1431_ = lean_uint64_xor(v___x_1428_, v___x_1430_);
v___x_1432_ = 16ULL;
v___x_1433_ = lean_uint64_shift_right(v_fold_1431_, v___x_1432_);
v___x_1434_ = lean_uint64_xor(v_fold_1431_, v___x_1433_);
v___x_1435_ = lean_uint64_to_usize(v___x_1434_);
v___x_1436_ = lean_usize_of_nat(v___x_1422_);
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_sub(v___x_1436_, v___x_1437_);
v___x_1439_ = lean_usize_land(v___x_1435_, v___x_1438_);
v___x_1440_ = lean_array_uget_borrowed(v_buckets_1419_, v___x_1439_);
v___x_1441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1418_, v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1442_, v_a_1443_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v_m_1442_);
return v_res_1444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Array_instInhabited___redArg();
return v___x_1445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3));
v___x_1450_ = lean_unsigned_to_nat(12u);
v___x_1451_ = lean_unsigned_to_nat(234u);
v___x_1452_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2));
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1459_ = lean_unsigned_to_nat(67u);
v___x_1460_ = lean_unsigned_to_nat(35u);
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___x_1463_ = l_mkPanicMessageWithDecl(v___x_1462_, v___x_1461_, v___x_1460_, v___x_1459_, v___x_1458_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_n_1464_, lean_object* v_varDeps_1465_, lean_object* v_xs_1466_, lean_object* v_e_1467_, lean_object* v_offset_1468_, lean_object* v_a_1469_, uint8_t v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
switch(lean_obj_tag(v_e_1467_))
{
case 5:
{
lean_object* v_fn_1473_; lean_object* v_arg_1474_; lean_object* v___x_1475_; 
v_fn_1473_ = lean_ctor_get(v_e_1467_, 0);
v_arg_1474_ = lean_ctor_get(v_e_1467_, 1);
lean_inc(v_offset_1468_);
lean_inc_ref(v_fn_1473_);
v___x_1475_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_fn_1473_, v_offset_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_a_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; lean_object* v___x_1480_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v_a_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1475_, 2);
v_fst_1478_ = lean_ctor_get(v_a_1476_, 0);
lean_inc(v_fst_1478_);
v_snd_1479_ = lean_ctor_get(v_a_1476_, 1);
lean_inc(v_snd_1479_);
lean_dec(v_a_1476_);
lean_inc_ref(v_arg_1474_);
v___x_1480_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_arg_1474_, v_offset_1468_, v_snd_1479_, v_a_1470_, v_a_1471_, v_a_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1506_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_a_1482_ = lean_ctor_get(v___x_1480_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1484_ = v___x_1480_;
v_isShared_1485_ = v_isSharedCheck_1506_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1506_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1505_; 
v_fst_1486_ = lean_ctor_get(v_a_1481_, 0);
v_snd_1487_ = lean_ctor_get(v_a_1481_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_a_1481_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1489_ = v_a_1481_;
v_isShared_1490_ = v_isSharedCheck_1505_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_inc(v_fst_1486_);
lean_dec(v_a_1481_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1505_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
size_t v___x_1491_; size_t v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = lean_ptr_addr(v_fn_1473_);
v___x_1492_ = lean_ptr_addr(v_fst_1478_);
v___x_1493_ = lean_usize_dec_eq(v___x_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1489_);
lean_del_object(v___x_1484_);
lean_dec_ref_known(v_e_1467_, 2);
v___x_1494_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1478_, v_fst_1486_, v_snd_1487_, v_a_1470_, v_a_1471_, v_a_1482_);
return v___x_1494_;
}
else
{
size_t v___x_1495_; size_t v___x_1496_; uint8_t v___x_1497_; 
v___x_1495_ = lean_ptr_addr(v_arg_1474_);
v___x_1496_ = lean_ptr_addr(v_fst_1486_);
v___x_1497_ = lean_usize_dec_eq(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_del_object(v___x_1489_);
lean_del_object(v___x_1484_);
lean_dec_ref_known(v_e_1467_, 2);
v___x_1498_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1478_, v_fst_1486_, v_snd_1487_, v_a_1470_, v_a_1471_, v_a_1482_);
return v___x_1498_;
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_fst_1486_);
lean_dec(v_fst_1478_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_e_1467_);
v___x_1500_ = v___x_1489_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_e_1467_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_snd_1487_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1500_);
v___x_1502_ = v___x_1484_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_a_1482_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1478_);
lean_dec_ref_known(v_e_1467_, 2);
return v___x_1480_;
}
}
else
{
lean_dec_ref_known(v_e_1467_, 2);
lean_dec(v_offset_1468_);
return v___x_1475_;
}
}
case 6:
{
lean_object* v_binderName_1507_; lean_object* v_binderType_1508_; lean_object* v_body_1509_; uint8_t v_binderInfo_1510_; lean_object* v___x_1511_; 
v_binderName_1507_ = lean_ctor_get(v_e_1467_, 0);
v_binderType_1508_ = lean_ctor_get(v_e_1467_, 1);
v_body_1509_ = lean_ctor_get(v_e_1467_, 2);
v_binderInfo_1510_ = lean_ctor_get_uint8(v_e_1467_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1468_);
lean_inc_ref(v_binderType_1508_);
v___x_1511_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_binderType_1508_, v_offset_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v_a_1513_; lean_object* v_fst_1514_; lean_object* v_snd_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
v_a_1513_ = lean_ctor_get(v___x_1511_, 1);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1511_, 2);
v_fst_1514_ = lean_ctor_get(v_a_1512_, 0);
lean_inc(v_fst_1514_);
v_snd_1515_ = lean_ctor_get(v_a_1512_, 1);
lean_inc(v_snd_1515_);
lean_dec(v_a_1512_);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_offset_1468_, v___x_1516_);
lean_dec(v_offset_1468_);
lean_inc_ref(v_body_1509_);
v___x_1518_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_body_1509_, v___x_1517_, v_snd_1515_, v_a_1470_, v_a_1471_, v_a_1513_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1544_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_a_1520_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1544_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1544_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1543_; 
v_fst_1524_ = lean_ctor_get(v_a_1519_, 0);
v_snd_1525_ = lean_ctor_get(v_a_1519_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_a_1519_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1527_ = v_a_1519_;
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_inc(v_fst_1524_);
lean_dec(v_a_1519_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
size_t v___x_1529_; size_t v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_ptr_addr(v_binderType_1508_);
v___x_1530_ = lean_ptr_addr(v_fst_1514_);
v___x_1531_ = lean_usize_dec_eq(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_inc(v_binderName_1507_);
lean_del_object(v___x_1527_);
lean_del_object(v___x_1522_);
lean_dec_ref_known(v_e_1467_, 3);
v___x_1532_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1507_, v_binderInfo_1510_, v_fst_1514_, v_fst_1524_, v_snd_1525_, v_a_1470_, v_a_1471_, v_a_1520_);
return v___x_1532_;
}
else
{
size_t v___x_1533_; size_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_ptr_addr(v_body_1509_);
v___x_1534_ = lean_ptr_addr(v_fst_1524_);
v___x_1535_ = lean_usize_dec_eq(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; 
lean_inc(v_binderName_1507_);
lean_del_object(v___x_1527_);
lean_del_object(v___x_1522_);
lean_dec_ref_known(v_e_1467_, 3);
v___x_1536_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1507_, v_binderInfo_1510_, v_fst_1514_, v_fst_1524_, v_snd_1525_, v_a_1470_, v_a_1471_, v_a_1520_);
return v___x_1536_;
}
else
{
lean_object* v___x_1538_; 
lean_dec(v_fst_1524_);
lean_dec(v_fst_1514_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_e_1467_);
v___x_1538_ = v___x_1527_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_e_1467_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_snd_1525_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1538_);
v___x_1540_ = v___x_1522_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1520_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1514_);
lean_dec_ref_known(v_e_1467_, 3);
return v___x_1518_;
}
}
else
{
lean_dec_ref_known(v_e_1467_, 3);
lean_dec(v_offset_1468_);
return v___x_1511_;
}
}
case 7:
{
lean_object* v_binderName_1545_; lean_object* v_binderType_1546_; lean_object* v_body_1547_; uint8_t v_binderInfo_1548_; lean_object* v___x_1549_; 
v_binderName_1545_ = lean_ctor_get(v_e_1467_, 0);
v_binderType_1546_ = lean_ctor_get(v_e_1467_, 1);
v_body_1547_ = lean_ctor_get(v_e_1467_, 2);
v_binderInfo_1548_ = lean_ctor_get_uint8(v_e_1467_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1468_);
lean_inc_ref(v_binderType_1546_);
v___x_1549_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_binderType_1546_, v_offset_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_a_1551_; lean_object* v_fst_1552_; lean_object* v_snd_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
v_a_1551_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1549_, 2);
v_fst_1552_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_fst_1552_);
v_snd_1553_ = lean_ctor_get(v_a_1550_, 1);
lean_inc(v_snd_1553_);
lean_dec(v_a_1550_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_offset_1468_, v___x_1554_);
lean_dec(v_offset_1468_);
lean_inc_ref(v_body_1547_);
v___x_1556_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_body_1547_, v___x_1555_, v_snd_1553_, v_a_1470_, v_a_1471_, v_a_1551_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1582_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1582_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1582_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1581_; 
v_fst_1562_ = lean_ctor_get(v_a_1557_, 0);
v_snd_1563_ = lean_ctor_get(v_a_1557_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1565_ = v_a_1557_;
v_isShared_1566_ = v_isSharedCheck_1581_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_snd_1563_);
lean_inc(v_fst_1562_);
lean_dec(v_a_1557_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1581_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
size_t v___x_1567_; size_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = lean_ptr_addr(v_binderType_1546_);
v___x_1568_ = lean_ptr_addr(v_fst_1552_);
v___x_1569_ = lean_usize_dec_eq(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_inc(v_binderName_1545_);
lean_del_object(v___x_1565_);
lean_del_object(v___x_1560_);
lean_dec_ref_known(v_e_1467_, 3);
v___x_1570_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1545_, v_binderInfo_1548_, v_fst_1552_, v_fst_1562_, v_snd_1563_, v_a_1470_, v_a_1471_, v_a_1558_);
return v___x_1570_;
}
else
{
size_t v___x_1571_; size_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = lean_ptr_addr(v_body_1547_);
v___x_1572_ = lean_ptr_addr(v_fst_1562_);
v___x_1573_ = lean_usize_dec_eq(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_inc(v_binderName_1545_);
lean_del_object(v___x_1565_);
lean_del_object(v___x_1560_);
lean_dec_ref_known(v_e_1467_, 3);
v___x_1574_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1545_, v_binderInfo_1548_, v_fst_1552_, v_fst_1562_, v_snd_1563_, v_a_1470_, v_a_1471_, v_a_1558_);
return v___x_1574_;
}
else
{
lean_object* v___x_1576_; 
lean_dec(v_fst_1562_);
lean_dec(v_fst_1552_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_e_1467_);
v___x_1576_ = v___x_1565_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_e_1467_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_snd_1563_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1576_);
v___x_1578_ = v___x_1560_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_a_1558_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1552_);
lean_dec_ref_known(v_e_1467_, 3);
return v___x_1556_;
}
}
else
{
lean_dec_ref_known(v_e_1467_, 3);
lean_dec(v_offset_1468_);
return v___x_1549_;
}
}
case 8:
{
lean_object* v_declName_1583_; lean_object* v_type_1584_; lean_object* v_value_1585_; lean_object* v_body_1586_; uint8_t v_nondep_1587_; lean_object* v___x_1588_; 
v_declName_1583_ = lean_ctor_get(v_e_1467_, 0);
v_type_1584_ = lean_ctor_get(v_e_1467_, 1);
v_value_1585_ = lean_ctor_get(v_e_1467_, 2);
v_body_1586_ = lean_ctor_get(v_e_1467_, 3);
v_nondep_1587_ = lean_ctor_get_uint8(v_e_1467_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1468_);
lean_inc_ref(v_type_1584_);
v___x_1588_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_type_1584_, v_offset_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v_fst_1591_; lean_object* v_snd_1592_; lean_object* v___x_1593_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
v_a_1590_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1588_, 2);
v_fst_1591_ = lean_ctor_get(v_a_1589_, 0);
lean_inc(v_fst_1591_);
v_snd_1592_ = lean_ctor_get(v_a_1589_, 1);
lean_inc(v_snd_1592_);
lean_dec(v_a_1589_);
lean_inc(v_offset_1468_);
lean_inc_ref(v_value_1585_);
v___x_1593_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_value_1585_, v_offset_1468_, v_snd_1592_, v_a_1470_, v_a_1471_, v_a_1590_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
v_a_1595_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1593_, 2);
v_fst_1596_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_fst_1596_);
v_snd_1597_ = lean_ctor_get(v_a_1594_, 1);
lean_inc(v_snd_1597_);
lean_dec(v_a_1594_);
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_nat_add(v_offset_1468_, v___x_1598_);
lean_dec(v_offset_1468_);
lean_inc_ref(v_body_1586_);
v___x_1600_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_body_1586_, v___x_1599_, v_snd_1597_, v_a_1470_, v_a_1471_, v_a_1595_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1630_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_a_1602_ = lean_ctor_get(v___x_1600_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1604_ = v___x_1600_;
v_isShared_1605_ = v_isSharedCheck_1630_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1630_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1629_; 
v_fst_1606_ = lean_ctor_get(v_a_1601_, 0);
v_snd_1607_ = lean_ctor_get(v_a_1601_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_a_1601_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1609_ = v_a_1601_;
v_isShared_1610_ = v_isSharedCheck_1629_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_inc(v_fst_1606_);
lean_dec(v_a_1601_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1629_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
size_t v___x_1611_; size_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = lean_ptr_addr(v_type_1584_);
v___x_1612_ = lean_ptr_addr(v_fst_1591_);
v___x_1613_ = lean_usize_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc(v_declName_1583_);
lean_del_object(v___x_1609_);
lean_del_object(v___x_1604_);
lean_dec_ref_known(v_e_1467_, 4);
v___x_1614_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1583_, v_fst_1591_, v_fst_1596_, v_fst_1606_, v_nondep_1587_, v_snd_1607_, v_a_1470_, v_a_1471_, v_a_1602_);
return v___x_1614_;
}
else
{
size_t v___x_1615_; size_t v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_ptr_addr(v_value_1585_);
v___x_1616_ = lean_ptr_addr(v_fst_1596_);
v___x_1617_ = lean_usize_dec_eq(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_inc(v_declName_1583_);
lean_del_object(v___x_1609_);
lean_del_object(v___x_1604_);
lean_dec_ref_known(v_e_1467_, 4);
v___x_1618_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1583_, v_fst_1591_, v_fst_1596_, v_fst_1606_, v_nondep_1587_, v_snd_1607_, v_a_1470_, v_a_1471_, v_a_1602_);
return v___x_1618_;
}
else
{
size_t v___x_1619_; size_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_ptr_addr(v_body_1586_);
v___x_1620_ = lean_ptr_addr(v_fst_1606_);
v___x_1621_ = lean_usize_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_inc(v_declName_1583_);
lean_del_object(v___x_1609_);
lean_del_object(v___x_1604_);
lean_dec_ref_known(v_e_1467_, 4);
v___x_1622_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1583_, v_fst_1591_, v_fst_1596_, v_fst_1606_, v_nondep_1587_, v_snd_1607_, v_a_1470_, v_a_1471_, v_a_1602_);
return v___x_1622_;
}
else
{
lean_object* v___x_1624_; 
lean_dec(v_fst_1606_);
lean_dec(v_fst_1596_);
lean_dec(v_fst_1591_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_e_1467_);
v___x_1624_ = v___x_1609_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_e_1467_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_snd_1607_);
v___x_1624_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1624_);
v___x_1626_ = v___x_1604_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_a_1602_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
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
lean_dec(v_fst_1596_);
lean_dec(v_fst_1591_);
lean_dec_ref_known(v_e_1467_, 4);
return v___x_1600_;
}
}
else
{
lean_dec(v_fst_1591_);
lean_dec_ref_known(v_e_1467_, 4);
lean_dec(v_offset_1468_);
return v___x_1593_;
}
}
else
{
lean_dec_ref_known(v_e_1467_, 4);
lean_dec(v_offset_1468_);
return v___x_1588_;
}
}
case 10:
{
lean_object* v_data_1631_; lean_object* v_expr_1632_; lean_object* v___x_1633_; 
v_data_1631_ = lean_ctor_get(v_e_1467_, 0);
v_expr_1632_ = lean_ctor_get(v_e_1467_, 1);
lean_inc_ref(v_expr_1632_);
v___x_1633_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_expr_1632_, v_offset_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1655_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_a_1635_ = lean_ctor_get(v___x_1633_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1637_ = v___x_1633_;
v_isShared_1638_ = v_isSharedCheck_1655_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1655_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1654_; 
v_fst_1639_ = lean_ctor_get(v_a_1634_, 0);
v_snd_1640_ = lean_ctor_get(v_a_1634_, 1);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_a_1634_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1642_ = v_a_1634_;
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_snd_1640_);
lean_inc(v_fst_1639_);
lean_dec(v_a_1634_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
size_t v___x_1644_; size_t v___x_1645_; uint8_t v___x_1646_; 
v___x_1644_ = lean_ptr_addr(v_expr_1632_);
v___x_1645_ = lean_ptr_addr(v_fst_1639_);
v___x_1646_ = lean_usize_dec_eq(v___x_1644_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_inc(v_data_1631_);
lean_del_object(v___x_1642_);
lean_del_object(v___x_1637_);
lean_dec_ref_known(v_e_1467_, 2);
v___x_1647_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_data_1631_, v_fst_1639_, v_snd_1640_, v_a_1470_, v_a_1471_, v_a_1635_);
return v___x_1647_;
}
else
{
lean_object* v___x_1649_; 
lean_dec(v_fst_1639_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v_e_1467_);
v___x_1649_ = v___x_1642_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_e_1467_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_snd_1640_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1649_);
v___x_1651_ = v___x_1637_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1635_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1467_, 2);
return v___x_1633_;
}
}
case 11:
{
lean_object* v_typeName_1656_; lean_object* v_idx_1657_; lean_object* v_struct_1658_; lean_object* v___x_1659_; 
v_typeName_1656_ = lean_ctor_get(v_e_1467_, 0);
v_idx_1657_ = lean_ctor_get(v_e_1467_, 1);
v_struct_1658_ = lean_ctor_get(v_e_1467_, 2);
lean_inc_ref(v_struct_1658_);
v___x_1659_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1464_, v_varDeps_1465_, v_xs_1466_, v_struct_1658_, v_offset_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1681_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_a_1661_ = lean_ctor_get(v___x_1659_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1681_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1681_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_fst_1665_; lean_object* v_snd_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1680_; 
v_fst_1665_ = lean_ctor_get(v_a_1660_, 0);
v_snd_1666_ = lean_ctor_get(v_a_1660_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1668_ = v_a_1660_;
v_isShared_1669_ = v_isSharedCheck_1680_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_snd_1666_);
lean_inc(v_fst_1665_);
lean_dec(v_a_1660_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1680_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
size_t v___x_1670_; size_t v___x_1671_; uint8_t v___x_1672_; 
v___x_1670_ = lean_ptr_addr(v_struct_1658_);
v___x_1671_ = lean_ptr_addr(v_fst_1665_);
v___x_1672_ = lean_usize_dec_eq(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_inc(v_idx_1657_);
lean_inc(v_typeName_1656_);
lean_del_object(v___x_1668_);
lean_del_object(v___x_1663_);
lean_dec_ref_known(v_e_1467_, 3);
v___x_1673_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_typeName_1656_, v_idx_1657_, v_fst_1665_, v_snd_1666_, v_a_1470_, v_a_1471_, v_a_1661_);
return v___x_1673_;
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_fst_1665_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v_e_1467_);
v___x_1675_ = v___x_1668_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_e_1467_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_snd_1666_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1675_);
v___x_1677_ = v___x_1663_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_a_1661_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1467_, 3);
return v___x_1659_;
}
}
default: 
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v_offset_1468_);
lean_dec_ref(v_e_1467_);
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3);
v___x_1683_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v___x_1682_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(lean_object* v_n_1684_, lean_object* v_varDeps_1685_, lean_object* v_xs_1686_, lean_object* v_e_1687_, lean_object* v_offset_1688_, lean_object* v_a_1689_, uint8_t v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_key_1693_; lean_object* v_a_1695_; lean_object* v___x_1708_; 
lean_inc(v_offset_1688_);
lean_inc_ref(v_e_1687_);
v_key_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1693_, 0, v_e_1687_);
lean_ctor_set(v_key_1693_, 1, v_offset_1688_);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_a_1689_, v_key_1693_);
if (lean_obj_tag(v___x_1708_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref_known(v_key_1693_, 2);
lean_dec(v_offset_1688_);
lean_dec_ref(v_e_1687_);
v_val_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_val_1709_);
lean_ctor_set(v___x_1710_, 1, v_a_1689_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_a_1692_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
lean_dec(v___x_1708_);
v___x_1712_ = l_Lean_Expr_looseBVarRange(v_e_1687_);
v___x_1713_ = lean_nat_dec_le(v___x_1712_, v_offset_1688_);
lean_dec(v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_Expr_getAppFn(v_e_1687_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_deBruijnIndex_1715_; uint8_t v___x_1716_; 
v_deBruijnIndex_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_deBruijnIndex_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = lean_nat_dec_le(v_offset_1688_, v_deBruijnIndex_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_deBruijnIndex_1715_);
lean_dec(v_offset_1688_);
v___x_1717_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_nat_add(v_offset_1688_, v_n_1684_);
v___x_1719_ = lean_nat_dec_lt(v_deBruijnIndex_1715_, v___x_1718_);
lean_dec(v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec(v_offset_1688_);
lean_dec_ref(v_e_1687_);
v___x_1720_ = lean_nat_sub(v_deBruijnIndex_1715_, v_n_1684_);
lean_dec(v_deBruijnIndex_1715_);
v___x_1721_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1720_, v_a_1692_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
v_a_1723_ = lean_ctor_get(v___x_1721_, 1);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1721_, 2);
v___x_1724_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_a_1722_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1723_);
return v___x_1724_;
}
else
{
lean_object* v_a_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref_known(v_key_1693_, 2);
lean_dec_ref(v_a_1689_);
v_a_1725_ = lean_ctor_get(v___x_1721_, 0);
v_a_1726_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1721_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_inc(v_a_1725_);
lean_dec(v___x_1721_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_i_1738_; lean_object* v___x_1739_; lean_object* v_expectedNumArgs_1740_; lean_object* v_numArgs_1741_; uint8_t v___x_1742_; 
v___x_1734_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1735_ = lean_nat_sub(v_deBruijnIndex_1715_, v_offset_1688_);
lean_dec(v_deBruijnIndex_1715_);
v___x_1736_ = lean_nat_sub(v_n_1684_, v___x_1735_);
lean_dec(v___x_1735_);
v___x_1737_ = lean_unsigned_to_nat(1u);
v_i_1738_ = lean_nat_sub(v___x_1736_, v___x_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_array_get_borrowed(v___x_1734_, v_varDeps_1685_, v_i_1738_);
v_expectedNumArgs_1740_ = lean_array_get_size(v___x_1739_);
v_numArgs_1741_ = l_Lean_Expr_getAppNumArgs(v_e_1687_);
v___x_1742_ = lean_nat_dec_lt(v_expectedNumArgs_1740_, v_numArgs_1741_);
if (v___x_1742_ == 0)
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_eq(v_numArgs_1741_, v_expectedNumArgs_1740_);
lean_dec(v_numArgs_1741_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v_i_1738_);
v___x_1744_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1745_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1744_, v_a_1690_, v_a_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
if (lean_obj_tag(v_a_1746_) == 1)
{
lean_object* v_a_1747_; lean_object* v_val_1748_; lean_object* v___x_1749_; 
lean_inc_ref(v_a_1746_);
lean_dec(v_offset_1688_);
lean_dec_ref(v_e_1687_);
v_a_1747_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1745_, 2);
v_val_1748_ = lean_ctor_get(v_a_1746_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v_a_1746_, 1);
v___x_1749_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_val_1748_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1747_);
return v___x_1749_;
}
else
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1745_, 2);
v_a_1695_ = v_a_1750_;
goto v___jp_1694_;
}
}
else
{
lean_object* v_a_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref_known(v_key_1693_, 2);
lean_dec_ref(v_a_1689_);
lean_dec(v_offset_1688_);
lean_dec_ref(v_e_1687_);
v_a_1751_ = lean_ctor_get(v___x_1745_, 0);
v_a_1752_ = lean_ctor_get(v___x_1745_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1745_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_inc(v_a_1751_);
lean_dec(v___x_1745_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1751_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_offset_1688_);
lean_dec_ref(v_e_1687_);
v___x_1760_ = lean_array_fget_borrowed(v_xs_1686_, v_i_1738_);
lean_dec(v_i_1738_);
lean_inc(v___x_1760_);
v___x_1761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v___x_1760_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1761_;
}
}
else
{
lean_dec(v_numArgs_1741_);
lean_dec(v_i_1738_);
v_a_1695_ = v_a_1692_;
goto v___jp_1694_;
}
}
}
}
else
{
lean_dec_ref(v___x_1714_);
v_a_1695_ = v_a_1692_;
goto v___jp_1694_;
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v_offset_1688_);
v___x_1762_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1762_;
}
}
v___jp_1694_:
{
switch(lean_obj_tag(v_e_1687_))
{
case 9:
{
lean_object* v___x_1696_; 
lean_dec(v_offset_1688_);
v___x_1696_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
return v___x_1696_;
}
case 2:
{
lean_object* v___x_1697_; 
lean_dec(v_offset_1688_);
v___x_1697_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
return v___x_1697_;
}
case 0:
{
lean_object* v___x_1698_; 
lean_dec(v_offset_1688_);
v___x_1698_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
return v___x_1698_;
}
case 1:
{
lean_object* v___x_1699_; 
lean_dec(v_offset_1688_);
v___x_1699_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
return v___x_1699_;
}
case 4:
{
lean_object* v___x_1700_; 
lean_dec(v_offset_1688_);
v___x_1700_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
return v___x_1700_;
}
case 3:
{
lean_object* v___x_1701_; 
lean_dec(v_offset_1688_);
v___x_1701_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_e_1687_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
return v___x_1701_;
}
default: 
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1684_, v_varDeps_1685_, v_xs_1686_, v_e_1687_, v_offset_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1695_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v_a_1704_; lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1707_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
v_a_1704_ = lean_ctor_get(v___x_1702_, 1);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1702_, 2);
v_fst_1705_ = lean_ctor_get(v_a_1703_, 0);
lean_inc(v_fst_1705_);
v_snd_1706_ = lean_ctor_get(v_a_1703_, 1);
lean_inc(v_snd_1706_);
lean_dec(v_a_1703_);
v___x_1707_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1693_, v_fst_1705_, v_snd_1706_, v_a_1690_, v_a_1691_, v_a_1704_);
return v___x_1707_;
}
else
{
lean_dec_ref_known(v_key_1693_, 2);
return v___x_1702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___boxed(lean_object* v_n_1763_, lean_object* v_varDeps_1764_, lean_object* v_xs_1765_, lean_object* v_e_1766_, lean_object* v_offset_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
uint8_t v_a_boxed_1772_; lean_object* v_res_1773_; 
v_a_boxed_1772_ = lean_unbox(v_a_1769_);
v_res_1773_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1763_, v_varDeps_1764_, v_xs_1765_, v_e_1766_, v_offset_1767_, v_a_1768_, v_a_boxed_1772_, v_a_1770_, v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec_ref(v_xs_1765_);
lean_dec_ref(v_varDeps_1764_);
lean_dec(v_n_1763_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_n_1774_, lean_object* v_varDeps_1775_, lean_object* v_xs_1776_, lean_object* v_e_1777_, lean_object* v_offset_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
uint8_t v_a_boxed_1783_; lean_object* v_res_1784_; 
v_a_boxed_1783_ = lean_unbox(v_a_1780_);
v_res_1784_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1774_, v_varDeps_1775_, v_xs_1776_, v_e_1777_, v_offset_1778_, v_a_1779_, v_a_boxed_1783_, v_a_1781_, v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec_ref(v_xs_1776_);
lean_dec_ref(v_varDeps_1775_);
lean_dec(v_n_1774_);
return v_res_1784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = lean_unsigned_to_nat(16u);
v___x_1787_ = lean_mk_array(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object* v_e_1791_, lean_object* v_n_1792_, lean_object* v_varDeps_1793_, lean_object* v_xs_1794_, uint8_t v_debug_1795_, lean_object* v___x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v_a_1801_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1829_ = l_Lean_Expr_looseBVarRange(v_e_1791_);
v___x_1830_ = lean_nat_dec_le(v___x_1829_, v___x_1799_);
lean_dec(v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Expr_getAppFn(v_e_1791_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_deBruijnIndex_1832_; uint8_t v___x_1833_; 
v_deBruijnIndex_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_deBruijnIndex_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = lean_nat_dec_le(v___x_1799_, v_deBruijnIndex_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec(v_deBruijnIndex_1832_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_e_1791_);
lean_ctor_set(v___x_1834_, 1, v___y_1798_);
return v___x_1834_;
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_nat_dec_lt(v_deBruijnIndex_1832_, v_n_1792_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v_e_1791_);
v___x_1836_ = lean_nat_sub(v_deBruijnIndex_1832_, v_n_1792_);
lean_dec(v_deBruijnIndex_1832_);
v___x_1837_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1836_, v___y_1798_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v_i_1840_; lean_object* v___x_1841_; lean_object* v_expectedNumArgs_1842_; lean_object* v_numArgs_1843_; uint8_t v___x_1844_; 
v___x_1838_ = lean_nat_sub(v_n_1792_, v_deBruijnIndex_1832_);
lean_dec(v_deBruijnIndex_1832_);
v___x_1839_ = lean_unsigned_to_nat(1u);
v_i_1840_ = lean_nat_sub(v___x_1838_, v___x_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_array_get_borrowed(v___x_1796_, v_varDeps_1793_, v_i_1840_);
v_expectedNumArgs_1842_ = lean_array_get_size(v___x_1841_);
v_numArgs_1843_ = l_Lean_Expr_getAppNumArgs(v_e_1791_);
v___x_1844_ = lean_nat_dec_lt(v_expectedNumArgs_1842_, v_numArgs_1843_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_eq(v_numArgs_1843_, v_expectedNumArgs_1842_);
lean_dec(v_numArgs_1843_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec(v_i_1840_);
v___x_1846_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1847_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1846_, v_debug_1795_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
if (lean_obj_tag(v_a_1848_) == 1)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
lean_inc_ref(v_a_1848_);
lean_dec_ref(v_e_1791_);
v_a_1849_ = lean_ctor_get(v___x_1847_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1847_, 0);
lean_dec(v_unused_1858_);
v___x_1851_ = v___x_1847_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1847_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_val_1853_; lean_object* v___x_1855_; 
v_val_1853_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v_a_1848_, 1);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v_val_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_val_1853_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_a_1849_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; 
v_a_1859_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1847_, 2);
v_a_1801_ = v_a_1859_;
goto v___jp_1800_;
}
}
else
{
lean_object* v_a_1860_; lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_e_1791_);
v_a_1860_ = lean_ctor_get(v___x_1847_, 0);
v_a_1861_ = lean_ctor_get(v___x_1847_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1847_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_inc(v_a_1860_);
lean_dec(v___x_1847_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1860_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v_e_1791_);
v___x_1869_ = lean_array_fget_borrowed(v_xs_1794_, v_i_1840_);
lean_dec(v_i_1840_);
lean_inc(v___x_1869_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v___y_1798_);
return v___x_1870_;
}
}
else
{
lean_dec(v_numArgs_1843_);
lean_dec(v_i_1840_);
v_a_1801_ = v___y_1798_;
goto v___jp_1800_;
}
}
}
}
else
{
lean_dec_ref(v___x_1831_);
v_a_1801_ = v___y_1798_;
goto v___jp_1800_;
}
}
else
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_e_1791_);
lean_ctor_set(v___x_1871_, 1, v___y_1798_);
return v___x_1871_;
}
v___jp_1800_:
{
switch(lean_obj_tag(v_e_1791_))
{
case 9:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v_e_1791_);
lean_ctor_set(v___x_1802_, 1, v_a_1801_);
return v___x_1802_;
}
case 2:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_e_1791_);
lean_ctor_set(v___x_1803_, 1, v_a_1801_);
return v___x_1803_;
}
case 0:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_e_1791_);
lean_ctor_set(v___x_1804_, 1, v_a_1801_);
return v___x_1804_;
}
case 1:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_e_1791_);
lean_ctor_set(v___x_1805_, 1, v_a_1801_);
return v___x_1805_;
}
case 4:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_e_1791_);
lean_ctor_set(v___x_1806_, 1, v_a_1801_);
return v___x_1806_;
}
case 3:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_e_1791_);
lean_ctor_set(v___x_1807_, 1, v_a_1801_);
return v___x_1807_;
}
default: 
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1);
v___x_1809_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1792_, v_varDeps_1793_, v_xs_1794_, v_e_1791_, v___x_1799_, v___x_1808_, v_debug_1795_, v___y_1797_, v_a_1801_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_a_1811_ = lean_ctor_get(v___x_1809_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v___x_1809_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_fst_1815_; lean_object* v___x_1817_; 
v_fst_1815_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_fst_1815_);
lean_dec(v_a_1810_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v_fst_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_fst_1815_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1811_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1820_ = lean_ctor_get(v___x_1809_, 0);
v_a_1821_ = lean_ctor_get(v___x_1809_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1809_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_inc(v_a_1820_);
lean_dec(v___x_1809_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1820_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object* v_e_1872_, lean_object* v_n_1873_, lean_object* v_varDeps_1874_, lean_object* v_xs_1875_, lean_object* v_debug_1876_, lean_object* v___x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v_debug_boxed_1880_; lean_object* v_res_1881_; 
v_debug_boxed_1880_ = lean_unbox(v_debug_1876_);
v_res_1881_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(v_e_1872_, v_n_1873_, v_varDeps_1874_, v_xs_1875_, v_debug_boxed_1880_, v___x_1877_, v___y_1878_, v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v___x_1877_);
lean_dec_ref(v_xs_1875_);
lean_dec_ref(v_varDeps_1874_);
lean_dec(v_n_1873_);
return v_res_1881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1885_ = lean_unsigned_to_nat(16u);
v___x_1886_ = lean_unsigned_to_nat(62u);
v___x_1887_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1));
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0));
v___x_1889_ = l_mkPanicMessageWithDecl(v___x_1888_, v___x_1887_, v___x_1886_, v___x_1885_, v___x_1884_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1890_, lean_object* v_xs_1891_, lean_object* v_varDeps_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_n_1901_; lean_object* v___x_1902_; uint8_t v_debug_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; lean_object* v_env_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1900_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v_n_1901_ = lean_array_get_size(v_xs_1891_);
v___x_1902_ = lean_st_ref_get(v_a_1894_);
v_debug_1903_ = lean_ctor_get_uint8(v___x_1902_, sizeof(void*)*12);
lean_dec(v___x_1902_);
v___x_1904_ = lean_box(v_debug_1903_);
v___f_1905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1905_, 0, v_e_1890_);
lean_closure_set(v___f_1905_, 1, v_n_1901_);
lean_closure_set(v___f_1905_, 2, v_varDeps_1892_);
lean_closure_set(v___f_1905_, 3, v_xs_1891_);
lean_closure_set(v___f_1905_, 4, v___x_1904_);
lean_closure_set(v___f_1905_, 5, v___x_1900_);
v___x_1906_ = lean_st_ref_get(v_a_1898_);
v_env_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_ref(v_env_1907_);
lean_dec(v___x_1906_);
v___x_1908_ = 0;
v___x_1909_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1909_, 0, v_env_1907_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*1, v___x_1908_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*1 + 1, v___x_1908_);
v___x_1910_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1905_, v___x_1909_, v_a_1894_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1921_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
if (lean_obj_tag(v_a_1911_) == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref_known(v_a_1911_, 1);
lean_del_object(v___x_1913_);
v___x_1915_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2);
v___x_1916_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_1915_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
return v___x_1916_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v_a_1911_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v_a_1911_, 1);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v_a_1917_);
v___x_1919_ = v___x_1913_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1910_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1910_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1930_, lean_object* v_xs_1931_, lean_object* v_varDeps_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1930_, v_xs_1931_, v_varDeps_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_1941_, lean_object* v_m_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1942_, v_a_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1945_, lean_object* v_m_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(v_00_u03b2_1945_, v_m_1946_, v_a_1947_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_m_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_1949_, lean_object* v_a_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1953_, lean_object* v_a_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_1953_, v_a_1954_, v_x_1955_);
lean_dec(v_x_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1957_, lean_object* v_type_1958_, lean_object* v_val_1959_, lean_object* v_k_1960_, uint8_t v_nondep_1961_, uint8_t v_kind_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___f_1970_; lean_object* v___x_1971_; 
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1970_, 0, v_k_1960_);
lean_closure_set(v___f_1970_, 1, v___y_1963_);
lean_closure_set(v___f_1970_, 2, v___y_1964_);
v___x_1971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1957_, v_type_1958_, v_val_1959_, v___f_1970_, v_nondep_1961_, v_kind_1962_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1971_) == 0)
{
return v___x_1971_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1980_, lean_object* v_type_1981_, lean_object* v_val_1982_, lean_object* v_k_1983_, lean_object* v_nondep_1984_, lean_object* v_kind_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_nondep_boxed_1993_; uint8_t v_kind_boxed_1994_; lean_object* v_res_1995_; 
v_nondep_boxed_1993_ = lean_unbox(v_nondep_1984_);
v_kind_boxed_1994_ = lean_unbox(v_kind_1985_);
v_res_1995_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1980_, v_type_1981_, v_val_1982_, v_k_1983_, v_nondep_boxed_1993_, v_kind_boxed_1994_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1996_, lean_object* v_name_1997_, lean_object* v_type_1998_, lean_object* v_val_1999_, lean_object* v_k_2000_, uint8_t v_nondep_2001_, uint8_t v_kind_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1997_, v_type_1998_, v_val_1999_, v_k_2000_, v_nondep_2001_, v_kind_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_name_2012_, lean_object* v_type_2013_, lean_object* v_val_2014_, lean_object* v_k_2015_, lean_object* v_nondep_2016_, lean_object* v_kind_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v_nondep_boxed_2025_; uint8_t v_kind_boxed_2026_; lean_object* v_res_2027_; 
v_nondep_boxed_2025_ = lean_unbox(v_nondep_2016_);
v_kind_boxed_2026_ = lean_unbox(v_kind_2017_);
v_res_2027_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_2011_, v_name_2012_, v_type_2013_, v_val_2014_, v_k_2015_, v_nondep_boxed_2025_, v_kind_boxed_2026_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_bs_2031_){
_start:
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2032_ == 0)
{
return v_bs_2031_;
}
else
{
lean_object* v___x_2033_; lean_object* v_v_2034_; lean_object* v___x_2035_; lean_object* v_bs_x27_2036_; lean_object* v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2033_ = l_Lean_instInhabitedExpr;
v_v_2034_ = lean_array_uget(v_bs_2031_, v_i_2030_);
v___x_2035_ = lean_unsigned_to_nat(0u);
v_bs_x27_2036_ = lean_array_uset(v_bs_2031_, v_i_2030_, v___x_2035_);
v___x_2037_ = lean_array_get_borrowed(v___x_2033_, v_xs_2028_, v_v_2034_);
lean_dec(v_v_2034_);
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = lean_usize_add(v_i_2030_, v___x_2038_);
lean_inc(v___x_2037_);
v___x_2040_ = lean_array_uset(v_bs_x27_2036_, v_i_2030_, v___x_2037_);
v_i_2030_ = v___x_2039_;
v_bs_2031_ = v___x_2040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_2042_, lean_object* v_sz_2043_, lean_object* v_i_2044_, lean_object* v_bs_2045_){
_start:
{
size_t v_sz_boxed_2046_; size_t v_i_boxed_2047_; lean_object* v_res_2048_; 
v_sz_boxed_2046_ = lean_unbox_usize(v_sz_2043_);
lean_dec(v_sz_2043_);
v_i_boxed_2047_ = lean_unbox_usize(v_i_2044_);
lean_dec(v_i_2044_);
v_res_2048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2042_, v_sz_boxed_2046_, v_i_boxed_2047_, v_bs_2045_);
lean_dec_ref(v_xs_2042_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_2049_, lean_object* v_i_2050_, lean_object* v_varDeps_2051_, lean_object* v_args_2052_, lean_object* v_body_2053_, lean_object* v_x_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_2049_, v_i_2050_, v_varDeps_2051_, v_args_2052_, v_body_2053_, v_x_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_i_2050_);
return v_res_2062_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2064_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2065_ = lean_unsigned_to_nat(30u);
v___x_2066_ = lean_unsigned_to_nat(254u);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_2068_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2069_ = l_mkPanicMessageWithDecl(v___x_2068_, v___x_2067_, v___x_2066_, v___x_2065_, v___x_2064_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_2070_, lean_object* v_args_2071_, lean_object* v_f_2072_, lean_object* v_xs_2073_, lean_object* v_i_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = lean_array_get_size(v_args_2071_);
v___x_2083_ = lean_nat_dec_lt(v_i_2074_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec(v_i_2074_);
lean_dec_ref(v_args_2071_);
lean_inc_ref(v_xs_2073_);
v___x_2084_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_f_2072_, v_xs_2073_, v_varDeps_2070_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = 1;
v___x_2087_ = l_Lean_Meta_mkLetFVars(v_xs_2073_, v_a_2085_, v___x_2083_, v___x_2083_, v___x_2086_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec_ref(v_xs_2073_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Meta_Sym_shareCommonInc(v_a_2088_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2089_;
}
else
{
return v___x_2087_;
}
}
else
{
lean_dec_ref(v_xs_2073_);
return v___x_2084_;
}
}
else
{
if (lean_obj_tag(v_f_2072_) == 6)
{
lean_object* v_binderName_2090_; lean_object* v_binderType_2091_; lean_object* v_body_2092_; lean_object* v___f_2093_; lean_object* v_varPos_2094_; size_t v_sz_2095_; size_t v___x_2096_; lean_object* v_ys_2097_; lean_object* v___x_2098_; lean_object* v_type_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_binderName_2090_ = lean_ctor_get(v_f_2072_, 0);
lean_inc(v_binderName_2090_);
v_binderType_2091_ = lean_ctor_get(v_f_2072_, 1);
lean_inc_ref(v_binderType_2091_);
v_body_2092_ = lean_ctor_get(v_f_2072_, 2);
lean_inc_ref(v_body_2092_);
lean_dec_ref_known(v_f_2072_, 3);
lean_inc_ref(v_args_2071_);
lean_inc_ref(v_varDeps_2070_);
lean_inc(v_i_2074_);
lean_inc_ref(v_xs_2073_);
v___f_2093_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2093_, 0, v_xs_2073_);
lean_closure_set(v___f_2093_, 1, v_i_2074_);
lean_closure_set(v___f_2093_, 2, v_varDeps_2070_);
lean_closure_set(v___f_2093_, 3, v_args_2071_);
lean_closure_set(v___f_2093_, 4, v_body_2092_);
v_varPos_2094_ = lean_array_fget(v_varDeps_2070_, v_i_2074_);
lean_dec_ref(v_varDeps_2070_);
v_sz_2095_ = lean_array_size(v_varPos_2094_);
v___x_2096_ = ((size_t)0ULL);
lean_inc(v_varPos_2094_);
v_ys_2097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2073_, v_sz_2095_, v___x_2096_, v_varPos_2094_);
lean_dec_ref(v_xs_2073_);
v___x_2098_ = lean_array_get_size(v_varPos_2094_);
lean_dec(v_varPos_2094_);
v_type_2099_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_2091_, v___x_2098_);
v___x_2100_ = lean_array_fget(v_args_2071_, v_i_2074_);
lean_dec(v_i_2074_);
lean_dec_ref(v_args_2071_);
v___x_2101_ = l_Lean_Expr_beta(v___x_2100_, v_ys_2097_);
v___x_2102_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2101_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = 0;
v___x_2105_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_2090_, v_type_2099_, v_a_2103_, v___f_2093_, v___x_2083_, v___x_2104_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2105_;
}
else
{
lean_dec_ref(v_type_2099_);
lean_dec_ref(v___f_2093_);
lean_dec(v_binderName_2090_);
return v___x_2102_;
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec(v_i_2074_);
lean_dec_ref(v_xs_2073_);
lean_dec_ref(v_f_2072_);
lean_dec_ref(v_args_2071_);
lean_dec_ref(v_varDeps_2070_);
v___x_2106_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_2107_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2106_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_2108_, lean_object* v_i_2109_, lean_object* v_varDeps_2110_, lean_object* v_args_2111_, lean_object* v_body_2112_, lean_object* v_x_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_Sym_shareCommonInc(v_x_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = lean_array_push(v_xs_2108_, v_a_2122_);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_add(v_i_2109_, v___x_2124_);
v___x_2126_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2110_, v_args_2111_, v_body_2112_, v___x_2123_, v___x_2125_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2126_;
}
else
{
lean_dec_ref(v_body_2112_);
lean_dec_ref(v_args_2111_);
lean_dec_ref(v_varDeps_2110_);
lean_dec_ref(v_xs_2108_);
return v___x_2121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_2127_, lean_object* v_args_2128_, lean_object* v_f_2129_, lean_object* v_xs_2130_, lean_object* v_i_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2127_, v_args_2128_, v_f_2129_, v_xs_2130_, v_i_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_2140_, lean_object* v_args_2141_, lean_object* v___h_2142_, lean_object* v_f_2143_, lean_object* v_xs_2144_, lean_object* v_i_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2140_, v_args_2141_, v_f_2143_, v_xs_2144_, v_i_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_2154_, lean_object* v_args_2155_, lean_object* v___h_2156_, lean_object* v_f_2157_, lean_object* v_xs_2158_, lean_object* v_i_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2154_, v_args_2155_, v___h_2156_, v_f_2157_, v_xs_2158_, v_i_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
return v_res_2167_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2170_ = lean_unsigned_to_nat(40u);
v___x_2171_ = lean_unsigned_to_nat(251u);
v___x_2172_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_2173_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2174_ = l_mkPanicMessageWithDecl(v___x_2173_, v___x_2172_, v___x_2171_, v___x_2170_, v___x_2169_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
if (lean_obj_tag(v_x_2176_) == 5)
{
lean_object* v_fn_2186_; lean_object* v_arg_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_fn_2186_ = lean_ctor_get(v_x_2176_, 0);
lean_inc_ref(v_fn_2186_);
v_arg_2187_ = lean_ctor_get(v_x_2176_, 1);
lean_inc_ref(v_arg_2187_);
lean_dec_ref_known(v_x_2176_, 2);
v___x_2188_ = lean_array_set(v_x_2177_, v_x_2178_, v_arg_2187_);
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = lean_nat_sub(v_x_2178_, v___x_2189_);
lean_dec(v_x_2178_);
v_x_2176_ = v_fn_2186_;
v_x_2177_ = v___x_2188_;
v_x_2178_ = v___x_2190_;
goto _start;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
lean_dec(v_x_2178_);
v___x_2192_ = lean_array_get_size(v_x_2177_);
v___x_2193_ = lean_array_get_size(v_varDeps_2175_);
v___x_2194_ = lean_nat_dec_eq(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v_x_2177_);
lean_dec_ref(v_x_2176_);
lean_dec_ref(v_varDeps_2175_);
v___x_2195_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2196_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2195_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2199_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2175_, v_x_2177_, v_x_2176_, v___x_2198_, v___x_2197_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2200_, v_x_2201_, v_x_2202_, v_x_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2212_; lean_object* v_dummy_2213_; 
v___x_2212_ = lean_box(0);
v_dummy_2213_ = l_Lean_Expr_sort___override(v___x_2212_);
return v_dummy_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2214_, lean_object* v_varDeps_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_dummy_2223_; lean_object* v_nargs_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_dummy_2223_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2224_ = l_Lean_Expr_getAppNumArgs(v_e_2214_);
lean_inc(v_nargs_2224_);
v___x_2225_ = lean_mk_array(v_nargs_2224_, v_dummy_2223_);
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_sub(v_nargs_2224_, v___x_2226_);
lean_dec(v_nargs_2224_);
v___x_2228_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2215_, v_e_2214_, v___x_2225_, v___x_2227_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2229_, lean_object* v_varDeps_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2229_, v_varDeps_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_snd_2242_; lean_object* v_fst_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2276_; 
v_snd_2242_ = lean_ctor_get(v_a_2240_, 1);
v_fst_2243_ = lean_ctor_get(v_a_2240_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2245_ = v_a_2240_;
v_isShared_2246_ = v_isSharedCheck_2276_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_snd_2242_);
lean_inc(v_fst_2243_);
lean_dec(v_a_2240_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2276_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_fst_2247_; lean_object* v_snd_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2275_; 
v_fst_2247_ = lean_ctor_get(v_snd_2242_, 0);
v_snd_2248_ = lean_ctor_get(v_snd_2242_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_snd_2242_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2250_ = v_snd_2242_;
v_isShared_2251_ = v_isSharedCheck_2275_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_snd_2248_);
lean_inc(v_fst_2247_);
lean_dec(v_snd_2242_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2275_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_nat_dec_lt(v___x_2252_, v_fst_2247_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2255_; 
if (v_isShared_2251_ == 0)
{
v___x_2255_ = v___x_2250_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_fst_2247_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_snd_2248_);
v___x_2255_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2257_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2255_);
v___x_2257_ = v___x_2245_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_fst_2243_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_sub(v_fst_2247_, v___x_2262_);
lean_dec(v_fst_2247_);
v___x_2264_ = lean_array_get_borrowed(v___x_2261_, v_argUnivs_2239_, v___x_2263_);
lean_inc(v___x_2264_);
v___x_2265_ = l_Lean_mkLevelIMax_x27(v___x_2264_, v_fst_2243_);
v___x_2266_ = l_Lean_Level_normalize(v___x_2265_);
lean_dec(v___x_2265_);
lean_inc(v___x_2266_);
v___x_2267_ = lean_array_push(v_snd_2248_, v___x_2266_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v___x_2267_);
lean_ctor_set(v___x_2250_, 0, v___x_2263_);
v___x_2269_ = v___x_2250_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2269_);
lean_ctor_set(v___x_2245_, 0, v___x_2266_);
v___x_2271_ = v___x_2245_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
v_a_2240_ = v___x_2271_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2277_, lean_object* v_a_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2277_, v_a_2278_);
lean_dec_ref(v_argUnivs_2277_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2283_, lean_object* v_argUnivs_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
if (lean_obj_tag(v_type_2283_) == 7)
{
lean_object* v_binderType_2292_; lean_object* v_body_2293_; lean_object* v___x_2294_; 
v_binderType_2292_ = lean_ctor_get(v_type_2283_, 1);
lean_inc_ref(v_binderType_2292_);
v_body_2293_ = lean_ctor_get(v_type_2283_, 2);
lean_inc_ref(v_body_2293_);
lean_dec_ref_known(v_type_2283_, 3);
v___x_2294_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2292_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = lean_array_push(v_argUnivs_2284_, v_a_2295_);
v_type_2283_ = v_body_2293_;
v_argUnivs_2284_ = v___x_2296_;
goto _start;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_body_2293_);
lean_dec_ref(v_argUnivs_2284_);
v_a_2298_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2294_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2294_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2283_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_array_get_size(v_argUnivs_2284_);
v___x_2309_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_a_2307_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2284_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2331_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2331_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2331_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_snd_2317_; lean_object* v_snd_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2329_; 
v_snd_2317_ = lean_ctor_get(v_a_2313_, 1);
lean_inc(v_snd_2317_);
lean_dec(v_a_2313_);
v_snd_2318_ = lean_ctor_get(v_snd_2317_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_snd_2317_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v_snd_2317_, 0);
lean_dec(v_unused_2330_);
v___x_2320_ = v_snd_2317_;
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_snd_2318_);
lean_dec(v_snd_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = l_Array_reverse___redArg(v_snd_2318_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2322_);
lean_ctor_set(v___x_2320_, 0, v_argUnivs_2284_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_argUnivs_2284_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2324_);
v___x_2326_ = v___x_2315_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_argUnivs_2284_);
v_a_2332_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2312_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2312_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
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
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_argUnivs_2284_);
v_a_2340_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2306_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2306_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2348_, lean_object* v_argUnivs_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2348_, v_argUnivs_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2358_, lean_object* v_inst_2359_, lean_object* v_a_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2358_, v_a_2360_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2369_, lean_object* v_inst_2370_, lean_object* v_a_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2369_, v_inst_2370_, v_a_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v_argUnivs_2369_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2389_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2380_, v___x_2388_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2399_, lean_object* v_argUnivs_2400_, lean_object* v_declName_2401_, lean_object* v_fType_2402_, lean_object* v_i_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v_00_u03b1_2406_; lean_object* v_00_u03b2_2407_; lean_object* v_u_2408_; lean_object* v_v_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2405_ = lean_box(0);
v_00_u03b1_2406_ = l_Lean_Expr_bindingDomain_x21(v_fType_2402_);
v_00_u03b2_2407_ = l_Lean_Expr_bindingBody_x21(v_fType_2402_);
v_u_2408_ = lean_array_get_borrowed(v___x_2405_, v_argUnivs_2400_, v_i_2403_);
v_v_2409_ = lean_array_get_borrowed(v___x_2405_, v_fnUnivs_2399_, v_i_2403_);
v___x_2410_ = lean_box(0);
lean_inc(v_v_2409_);
v___x_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_v_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
lean_inc(v_u_2408_);
v___x_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2412_, 0, v_u_2408_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_mkConst(v_declName_2401_, v___x_2412_);
v___x_2414_ = l_Lean_mkAppB(v___x_2413_, v_00_u03b1_2406_, v_00_u03b2_2407_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2416_, lean_object* v_argUnivs_2417_, lean_object* v_declName_2418_, lean_object* v_fType_2419_, lean_object* v_i_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2416_, v_argUnivs_2417_, v_declName_2418_, v_fType_2419_, v_i_2420_);
lean_dec(v_i_2420_);
lean_dec_ref(v_fType_2419_);
lean_dec_ref(v_argUnivs_2417_);
lean_dec_ref(v_fnUnivs_2416_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2423_, lean_object* v_argUnivs_2424_, lean_object* v_declName_2425_, lean_object* v_fType_2426_, lean_object* v_i_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2423_, v_argUnivs_2424_, v_declName_2425_, v_fType_2426_, v_i_2427_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2436_, lean_object* v_argUnivs_2437_, lean_object* v_declName_2438_, lean_object* v_fType_2439_, lean_object* v_i_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2436_, v_argUnivs_2437_, v_declName_2438_, v_fType_2439_, v_i_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_i_2440_);
lean_dec_ref(v_fType_2439_);
lean_dec_ref(v_argUnivs_2437_);
lean_dec_ref(v_fnUnivs_2436_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2449_, lean_object* v_a_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___y_2459_; lean_object* v___x_2462_; uint8_t v_debug_2463_; 
v___x_2462_ = lean_st_ref_get(v___y_2452_);
v_debug_2463_ = lean_ctor_get_uint8(v___x_2462_, sizeof(void*)*12);
lean_dec(v___x_2462_);
if (v_debug_2463_ == 0)
{
v___y_2459_ = v___y_2452_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2449_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v___x_2465_; 
lean_dec_ref_known(v___x_2464_, 1);
v___x_2465_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_dec_ref_known(v___x_2465_, 1);
v___y_2459_ = v___y_2452_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_f_2449_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_f_2449_);
v_a_2474_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2464_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2464_);
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
v___jp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = l_Lean_Expr_app___override(v_f_2449_, v_a_2450_);
v___x_2461_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2460_, v___y_2459_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2482_, lean_object* v_a_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2482_, v_a_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2492_, lean_object* v_a_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2492_, v_a_2493_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2505_, lean_object* v_a_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2505_, v_a_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
return v_res_2517_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_15220__overap_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15220__overap_2531_ = lean_panic_fn_borrowed(v___x_2530_, v_msg_2519_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
v___x_2532_ = lean_apply_10(v___x_15220__overap_2531_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
return v_res_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2556_ = lean_unsigned_to_nat(11u);
v___x_2557_ = lean_unsigned_to_nat(346u);
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2559_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2560_ = l_mkPanicMessageWithDecl(v___x_2559_, v___x_2558_, v___x_2557_, v___x_2556_, v___x_2555_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2561_, lean_object* v_fnUnivs_2562_, lean_object* v_argUnivs_2563_, lean_object* v_simpBody_2564_, lean_object* v_e_2565_, lean_object* v_i_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
switch(lean_obj_tag(v_e_2565_))
{
case 5:
{
lean_object* v_fn_2577_; lean_object* v_arg_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_fn_2577_ = lean_ctor_get(v_e_2565_, 0);
lean_inc_ref_n(v_fn_2577_, 2);
v_arg_2578_ = lean_ctor_get(v_e_2565_, 1);
lean_inc_ref(v_arg_2578_);
lean_dec_ref_known(v_e_2565_, 2);
v___x_2579_ = lean_unsigned_to_nat(1u);
v___x_2580_ = lean_nat_sub(v_i_2566_, v___x_2579_);
v___x_2581_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2561_, v_fnUnivs_2562_, v_argUnivs_2563_, v_simpBody_2564_, v_fn_2577_, v___x_2580_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2702_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2702_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2702_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v_fst_2586_; lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2701_; 
v_fst_2586_ = lean_ctor_get(v_a_2582_, 0);
v_snd_2587_ = lean_ctor_get(v_a_2582_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_a_2582_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2589_ = v_a_2582_;
v_isShared_2590_ = v_isSharedCheck_2701_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_inc(v_fst_2586_);
lean_dec(v_a_2582_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2701_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_r_2592_; lean_object* v___x_2600_; 
lean_inc(v_a_2575_);
lean_inc_ref(v_a_2574_);
lean_inc(v_a_2573_);
lean_inc_ref(v_a_2572_);
lean_inc(v_a_2571_);
lean_inc_ref(v_a_2570_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc_ref(v_arg_2578_);
v___x_2600_ = lean_sym_simp(v_arg_2578_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; uint8_t v___y_2603_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
if (lean_obj_tag(v_fst_2586_) == 0)
{
if (lean_obj_tag(v_a_2601_) == 0)
{
uint8_t v_contextDependent_2605_; 
lean_dec_ref(v_arg_2578_);
lean_dec_ref(v_fn_2577_);
v_contextDependent_2605_ = lean_ctor_get_uint8(v_fst_2586_, 1);
lean_dec_ref_known(v_fst_2586_, 0);
if (v_contextDependent_2605_ == 0)
{
uint8_t v_contextDependent_2606_; 
v_contextDependent_2606_ = lean_ctor_get_uint8(v_a_2601_, 1);
lean_dec_ref_known(v_a_2601_, 0);
v___y_2603_ = v_contextDependent_2606_;
goto v___jp_2602_;
}
else
{
lean_dec_ref_known(v_a_2601_, 0);
v___y_2603_ = v_contextDependent_2605_;
goto v___jp_2602_;
}
}
else
{
uint8_t v_contextDependent_2607_; lean_object* v_e_x27_2608_; lean_object* v_proof_2609_; uint8_t v_contextDependent_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2634_; 
v_contextDependent_2607_ = lean_ctor_get_uint8(v_fst_2586_, 1);
lean_dec_ref_known(v_fst_2586_, 0);
v_e_x27_2608_ = lean_ctor_get(v_a_2601_, 0);
v_proof_2609_ = lean_ctor_get(v_a_2601_, 1);
v_contextDependent_2610_ = lean_ctor_get_uint8(v_a_2601_, sizeof(void*)*2 + 1);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_a_2601_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2612_ = v_a_2601_;
v_isShared_2613_ = v_isSharedCheck_2634_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_proof_2609_);
lean_inc(v_e_x27_2608_);
lean_dec(v_a_2601_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2634_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; 
lean_inc_ref(v_e_x27_2608_);
lean_inc_ref(v_fn_2577_);
v___x_2614_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2577_, v_e_x27_2608_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_a_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; uint8_t v___y_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2617_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2562_, v_argUnivs_2563_, v___x_2616_, v_snd_2587_, v_i_2566_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = l_Lean_mkApp4(v_a_2618_, v_arg_2578_, v_e_x27_2608_, v_fn_2577_, v_proof_2609_);
v___x_2620_ = 0;
if (v_contextDependent_2607_ == 0)
{
v___y_2622_ = v_contextDependent_2610_;
goto v___jp_2621_;
}
else
{
v___y_2622_ = v_contextDependent_2607_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 1, v___x_2619_);
lean_ctor_set(v___x_2612_, 0, v_a_2615_);
v___x_2624_ = v___x_2612_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2615_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*2, v___x_2620_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*2 + 1, v___y_2622_);
v_r_2592_ = v___x_2624_;
goto v___jp_2591_;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_del_object(v___x_2612_);
lean_dec_ref(v_proof_2609_);
lean_dec_ref(v_e_x27_2608_);
lean_del_object(v___x_2589_);
lean_dec(v_snd_2587_);
lean_del_object(v___x_2584_);
lean_dec_ref(v_arg_2578_);
lean_dec_ref(v_fn_2577_);
v_a_2626_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2614_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2614_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2601_) == 0)
{
lean_object* v_e_x27_2635_; lean_object* v_proof_2636_; uint8_t v_contextDependent_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2662_; 
v_e_x27_2635_ = lean_ctor_get(v_fst_2586_, 0);
v_proof_2636_ = lean_ctor_get(v_fst_2586_, 1);
v_contextDependent_2637_ = lean_ctor_get_uint8(v_fst_2586_, sizeof(void*)*2 + 1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_fst_2586_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2639_ = v_fst_2586_;
v_isShared_2640_ = v_isSharedCheck_2662_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_proof_2636_);
lean_inc(v_e_x27_2635_);
lean_dec(v_fst_2586_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2662_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
uint8_t v_contextDependent_2641_; lean_object* v___x_2642_; 
v_contextDependent_2641_ = lean_ctor_get_uint8(v_a_2601_, 1);
lean_dec_ref_known(v_a_2601_, 0);
lean_inc_ref(v_arg_2578_);
lean_inc_ref(v_e_x27_2635_);
v___x_2642_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2635_, v_arg_2578_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; uint8_t v___y_2650_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2645_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2562_, v_argUnivs_2563_, v___x_2644_, v_snd_2587_, v_i_2566_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = l_Lean_mkApp4(v_a_2646_, v_fn_2577_, v_e_x27_2635_, v_proof_2636_, v_arg_2578_);
v___x_2648_ = 0;
if (v_contextDependent_2637_ == 0)
{
v___y_2650_ = v_contextDependent_2641_;
goto v___jp_2649_;
}
else
{
v___y_2650_ = v_contextDependent_2637_;
goto v___jp_2649_;
}
v___jp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v___x_2647_);
lean_ctor_set(v___x_2639_, 0, v_a_2643_);
v___x_2652_ = v___x_2639_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2643_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*2, v___x_2648_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*2 + 1, v___y_2650_);
v_r_2592_ = v___x_2652_;
goto v___jp_2591_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_del_object(v___x_2639_);
lean_dec_ref(v_proof_2636_);
lean_dec_ref(v_e_x27_2635_);
lean_del_object(v___x_2589_);
lean_dec(v_snd_2587_);
lean_del_object(v___x_2584_);
lean_dec_ref(v_arg_2578_);
lean_dec_ref(v_fn_2577_);
v_a_2654_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2642_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2642_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2663_; lean_object* v_proof_2664_; uint8_t v_contextDependent_2665_; lean_object* v_e_x27_2666_; lean_object* v_proof_2667_; uint8_t v_contextDependent_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2692_; 
v_e_x27_2663_ = lean_ctor_get(v_fst_2586_, 0);
lean_inc_ref(v_e_x27_2663_);
v_proof_2664_ = lean_ctor_get(v_fst_2586_, 1);
lean_inc_ref(v_proof_2664_);
v_contextDependent_2665_ = lean_ctor_get_uint8(v_fst_2586_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2586_, 2);
v_e_x27_2666_ = lean_ctor_get(v_a_2601_, 0);
v_proof_2667_ = lean_ctor_get(v_a_2601_, 1);
v_contextDependent_2668_ = lean_ctor_get_uint8(v_a_2601_, sizeof(void*)*2 + 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2601_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2670_ = v_a_2601_;
v_isShared_2671_ = v_isSharedCheck_2692_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_proof_2667_);
lean_inc(v_e_x27_2666_);
lean_dec(v_a_2601_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2692_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; 
lean_inc_ref(v_e_x27_2666_);
lean_inc_ref(v_e_x27_2663_);
v___x_2672_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2663_, v_e_x27_2666_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_a_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; uint8_t v___y_2680_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2675_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2562_, v_argUnivs_2563_, v___x_2674_, v_snd_2587_, v_i_2566_);
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v___x_2677_ = l_Lean_mkApp6(v_a_2676_, v_fn_2577_, v_e_x27_2663_, v_arg_2578_, v_e_x27_2666_, v_proof_2664_, v_proof_2667_);
v___x_2678_ = 0;
if (v_contextDependent_2665_ == 0)
{
v___y_2680_ = v_contextDependent_2668_;
goto v___jp_2679_;
}
else
{
v___y_2680_ = v_contextDependent_2665_;
goto v___jp_2679_;
}
v___jp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2677_);
lean_ctor_set(v___x_2670_, 0, v_a_2673_);
v___x_2682_ = v___x_2670_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2673_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*2, v___x_2678_);
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*2 + 1, v___y_2680_);
v_r_2592_ = v___x_2682_;
goto v___jp_2591_;
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2670_);
lean_dec_ref(v_proof_2667_);
lean_dec_ref(v_e_x27_2666_);
lean_dec_ref(v_proof_2664_);
lean_dec_ref(v_e_x27_2663_);
lean_del_object(v___x_2589_);
lean_dec(v_snd_2587_);
lean_del_object(v___x_2584_);
lean_dec_ref(v_arg_2578_);
lean_dec_ref(v_fn_2577_);
v_a_2684_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2672_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2672_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
v___jp_2602_:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2603_);
v_r_2592_ = v___x_2604_;
goto v___jp_2591_;
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_del_object(v___x_2589_);
lean_dec(v_snd_2587_);
lean_dec(v_fst_2586_);
lean_del_object(v___x_2584_);
lean_dec_ref(v_arg_2578_);
lean_dec_ref(v_fn_2577_);
v_a_2693_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2600_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2600_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_Expr_bindingBody_x21(v_snd_2587_);
lean_dec(v_snd_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v___x_2593_);
lean_ctor_set(v___x_2589_, 0, v_r_2592_);
v___x_2595_ = v___x_2589_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_r_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2595_);
v___x_2597_ = v___x_2584_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2578_);
lean_dec_ref(v_fn_2577_);
return v___x_2581_;
}
}
case 6:
{
lean_object* v___x_2703_; 
lean_inc(v_a_2575_);
lean_inc_ref(v_a_2574_);
lean_inc(v_a_2573_);
lean_inc_ref(v_a_2572_);
lean_inc(v_a_2571_);
lean_inc_ref(v_a_2570_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
v___x_2703_ = lean_apply_11(v_simpBody_2564_, v_e_2565_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, lean_box(0));
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2704_);
lean_ctor_set(v___x_2708_, 1, v_fType_2561_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_fType_2561_);
v_a_2713_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2703_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2703_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
default: 
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v_e_2565_);
lean_dec_ref(v_simpBody_2564_);
lean_dec_ref(v_fType_2561_);
v___x_2721_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2722_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2721_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2723_, lean_object* v_fnUnivs_2724_, lean_object* v_argUnivs_2725_, lean_object* v_simpBody_2726_, lean_object* v_e_2727_, lean_object* v_i_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2723_, v_fnUnivs_2724_, v_argUnivs_2725_, v_simpBody_2726_, v_e_2727_, v_i_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec(v_i_2728_);
lean_dec_ref(v_argUnivs_2725_);
lean_dec_ref(v_fnUnivs_2724_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2740_, lean_object* v_fType_2741_, lean_object* v_fnUnivs_2742_, lean_object* v_argUnivs_2743_, lean_object* v_simpBody_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_numArgs_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_numArgs_2755_ = lean_array_get_size(v_argUnivs_2743_);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_sub(v_numArgs_2755_, v___x_2756_);
v___x_2758_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2741_, v_fnUnivs_2742_, v_argUnivs_2743_, v_simpBody_2744_, v_e_2740_, v___x_2757_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
lean_dec(v___x_2757_);
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
lean_object* v_fst_2763_; lean_object* v___x_2765_; 
v_fst_2763_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_fst_2763_);
lean_dec(v_a_2759_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_fst_2763_);
v___x_2765_ = v___x_2761_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_fst_2763_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2776_, lean_object* v_fType_2777_, lean_object* v_fnUnivs_2778_, lean_object* v_argUnivs_2779_, lean_object* v_simpBody_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2776_, v_fType_2777_, v_fnUnivs_2778_, v_argUnivs_2779_, v_simpBody_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_argUnivs_2779_);
lean_dec_ref(v_fnUnivs_2778_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2796_, lean_object* v_simpBody_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; 
lean_inc_ref(v_e_2796_);
v___x_2808_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2796_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v_00_u03b1_2810_; lean_object* v_u_2811_; lean_object* v_e_2812_; lean_object* v_h_2813_; lean_object* v_varDeps_2814_; lean_object* v_fType_2815_; lean_object* v___x_2816_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v_00_u03b1_2810_ = lean_ctor_get(v_a_2809_, 0);
lean_inc_ref(v_00_u03b1_2810_);
v_u_2811_ = lean_ctor_get(v_a_2809_, 1);
lean_inc(v_u_2811_);
v_e_2812_ = lean_ctor_get(v_a_2809_, 2);
lean_inc_ref(v_e_2812_);
v_h_2813_ = lean_ctor_get(v_a_2809_, 3);
lean_inc_ref(v_h_2813_);
v_varDeps_2814_ = lean_ctor_get(v_a_2809_, 4);
lean_inc_ref(v_varDeps_2814_);
v_fType_2815_ = lean_ctor_get(v_a_2809_, 5);
lean_inc_ref_n(v_fType_2815_, 2);
lean_dec(v_a_2809_);
v___x_2816_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2815_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v_argUnivs_2818_; lean_object* v_fnUnivs_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2887_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v_argUnivs_2818_ = lean_ctor_get(v_a_2817_, 0);
v_fnUnivs_2819_ = lean_ctor_get(v_a_2817_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_a_2817_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2821_ = v_a_2817_;
v_isShared_2822_ = v_isSharedCheck_2887_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_fnUnivs_2819_);
lean_inc(v_argUnivs_2818_);
lean_dec(v_a_2817_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2887_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; 
lean_inc_ref(v_e_2812_);
v___x_2823_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2812_, v_fType_2815_, v_fnUnivs_2819_, v_argUnivs_2818_, v_simpBody_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec_ref(v_argUnivs_2818_);
lean_dec_ref(v_fnUnivs_2819_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2878_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2878_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2878_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
if (lean_obj_tag(v_a_2824_) == 0)
{
uint8_t v_contextDependent_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_del_object(v___x_2821_);
lean_dec_ref(v_varDeps_2814_);
lean_dec_ref(v_h_2813_);
lean_dec_ref(v_e_2812_);
lean_dec_ref(v_e_2796_);
v_contextDependent_2828_ = lean_ctor_get_uint8(v_a_2824_, 1);
lean_dec_ref_known(v_a_2824_, 0);
v___x_2829_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2828_);
v___x_2830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v_00_u03b1_2810_);
lean_ctor_set(v___x_2830_, 2, v_u_2811_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2830_);
v___x_2832_ = v___x_2826_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v_e_x27_2834_; lean_object* v_proof_2835_; uint8_t v_contextDependent_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2877_; 
lean_del_object(v___x_2826_);
v_e_x27_2834_ = lean_ctor_get(v_a_2824_, 0);
v_proof_2835_ = lean_ctor_get(v_a_2824_, 1);
v_contextDependent_2836_ = lean_ctor_get_uint8(v_a_2824_, sizeof(void*)*2 + 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_a_2824_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2838_ = v_a_2824_;
v_isShared_2839_ = v_isSharedCheck_2877_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_proof_2835_);
lean_inc(v_e_x27_2834_);
lean_dec(v_a_2824_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2877_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2841_ = lean_box(0);
lean_inc(v_u_2811_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 1);
lean_ctor_set(v___x_2821_, 1, v___x_2841_);
lean_ctor_set(v___x_2821_, 0, v_u_2811_);
v___x_2843_ = v___x_2821_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_u_2811_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_inc_ref(v___x_2843_);
v___x_2844_ = l_Lean_mkConst(v___x_2840_, v___x_2843_);
lean_inc_ref_n(v_e_x27_2834_, 2);
lean_inc_ref(v_e_2796_);
lean_inc_ref(v_00_u03b1_2810_);
lean_inc_ref(v___x_2844_);
v___x_2845_ = l_Lean_mkApp6(v___x_2844_, v_00_u03b1_2810_, v_e_2796_, v_e_2812_, v_e_x27_2834_, v_h_2813_, v_proof_2835_);
v___x_2846_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2834_, v_varDeps_2814_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2867_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2867_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2867_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2861_; 
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2843_);
v___x_2852_ = l_Lean_mkConst(v___x_2851_, v___x_2843_);
lean_inc_n(v_a_2847_, 2);
lean_inc_ref_n(v_e_x27_2834_, 2);
lean_inc_ref_n(v_00_u03b1_2810_, 3);
v___x_2853_ = l_Lean_mkApp3(v___x_2852_, v_00_u03b1_2810_, v_e_x27_2834_, v_a_2847_);
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2855_ = l_Lean_mkConst(v___x_2854_, v___x_2843_);
v___x_2856_ = l_Lean_mkAppB(v___x_2855_, v_00_u03b1_2810_, v_e_x27_2834_);
v___x_2857_ = l_Lean_Meta_mkExpectedPropHint(v___x_2856_, v___x_2853_);
v___x_2858_ = l_Lean_mkApp6(v___x_2844_, v_00_u03b1_2810_, v_e_2796_, v_e_x27_2834_, v_a_2847_, v___x_2845_, v___x_2857_);
v___x_2859_ = 0;
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2858_);
lean_ctor_set(v___x_2838_, 0, v_a_2847_);
v___x_2861_ = v___x_2838_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2847_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v___x_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2866_, sizeof(void*)*2 + 1, v_contextDependent_2836_);
v___x_2861_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*2, v___x_2859_);
v___x_2862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v_00_u03b1_2810_);
lean_ctor_set(v___x_2862_, 2, v_u_2811_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2862_);
v___x_2864_ = v___x_2849_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v___x_2845_);
lean_dec_ref(v___x_2844_);
lean_dec_ref(v___x_2843_);
lean_del_object(v___x_2838_);
lean_dec_ref(v_e_x27_2834_);
lean_dec(v_u_2811_);
lean_dec_ref(v_00_u03b1_2810_);
lean_dec_ref(v_e_2796_);
v_a_2868_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2846_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2846_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
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
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_del_object(v___x_2821_);
lean_dec_ref(v_varDeps_2814_);
lean_dec_ref(v_h_2813_);
lean_dec_ref(v_e_2812_);
lean_dec(v_u_2811_);
lean_dec_ref(v_00_u03b1_2810_);
lean_dec_ref(v_e_2796_);
v_a_2879_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2823_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2823_);
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
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v_fType_2815_);
lean_dec_ref(v_varDeps_2814_);
lean_dec_ref(v_h_2813_);
lean_dec_ref(v_e_2812_);
lean_dec(v_u_2811_);
lean_dec_ref(v_00_u03b1_2810_);
lean_dec_ref(v_simpBody_2797_);
lean_dec_ref(v_e_2796_);
v_a_2888_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2816_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2816_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v_simpBody_2797_);
lean_dec_ref(v_e_2796_);
v_a_2896_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2808_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2808_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2904_, lean_object* v_simpBody_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2904_, v_simpBody_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2917_, lean_object* v_simpBody_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2917_, v_simpBody_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2938_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2938_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2938_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_result_2934_; lean_object* v___x_2936_; 
v_result_2934_ = lean_ctor_get(v_a_2930_, 0);
lean_inc_ref(v_result_2934_);
lean_dec(v_a_2930_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v_result_2934_);
v___x_2936_ = v___x_2932_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_result_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2929_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2929_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2947_, lean_object* v_simpBody_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2947_, v_simpBody_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2960_, lean_object* v_simpBody_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___x_2972_; 
lean_inc_ref(v_e_u2081_2960_);
v___x_2972_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2960_, v_simpBody_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v_result_2974_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v_result_2974_ = lean_ctor_get(v_a_2973_, 0);
lean_inc_ref(v_result_2974_);
if (lean_obj_tag(v_result_2974_) == 0)
{
lean_object* v_00_u03b1_2975_; lean_object* v_u_2976_; uint8_t v_contextDependent_2977_; lean_object* v___x_2978_; 
v_00_u03b1_2975_ = lean_ctor_get(v_a_2973_, 1);
lean_inc_ref(v_00_u03b1_2975_);
v_u_2976_ = lean_ctor_get(v_a_2973_, 2);
lean_inc(v_u_2976_);
lean_dec(v_a_2973_);
v_contextDependent_2977_ = lean_ctor_get_uint8(v_result_2974_, 1);
lean_dec_ref_known(v_result_2974_, 0);
lean_inc_ref(v_e_u2081_2960_);
v___x_2978_ = l_Lean_Meta_zetaUnused(v_e_u2081_2960_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2999_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2999_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2999_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
size_t v___x_2983_; size_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2983_ = lean_ptr_addr(v_e_u2081_2960_);
lean_dec_ref(v_e_u2081_2960_);
v___x_2984_ = lean_ptr_addr(v_a_2979_);
v___x_2985_ = lean_usize_dec_eq(v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2986_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2987_ = lean_box(0);
v___x_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_u_2976_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_mkConst(v___x_2986_, v___x_2988_);
lean_inc(v_a_2979_);
v___x_2990_ = l_Lean_mkAppB(v___x_2989_, v_00_u03b1_2975_, v_a_2979_);
v___x_2991_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2991_, 0, v_a_2979_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*2, v___x_2985_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*2 + 1, v_contextDependent_2977_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2991_);
v___x_2993_ = v___x_2981_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_dec(v_a_2979_);
lean_dec(v_u_2976_);
lean_dec_ref(v_00_u03b1_2975_);
v___x_2995_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2977_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2995_);
v___x_2997_ = v___x_2981_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec(v_u_2976_);
lean_dec_ref(v_00_u03b1_2975_);
lean_dec_ref(v_e_u2081_2960_);
v_a_3000_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2978_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2978_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
else
{
lean_object* v_00_u03b1_3008_; lean_object* v_u_3009_; lean_object* v_e_x27_3010_; lean_object* v_proof_3011_; uint8_t v_contextDependent_3012_; lean_object* v___x_3013_; 
v_00_u03b1_3008_ = lean_ctor_get(v_a_2973_, 1);
lean_inc_ref(v_00_u03b1_3008_);
v_u_3009_ = lean_ctor_get(v_a_2973_, 2);
lean_inc(v_u_3009_);
lean_dec(v_a_2973_);
v_e_x27_3010_ = lean_ctor_get(v_result_2974_, 0);
v_proof_3011_ = lean_ctor_get(v_result_2974_, 1);
v_contextDependent_3012_ = lean_ctor_get_uint8(v_result_2974_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_3010_);
v___x_3013_ = l_Lean_Meta_zetaUnused(v_e_x27_3010_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3044_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3044_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3044_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
size_t v___x_3018_; size_t v___x_3019_; uint8_t v___x_3020_; 
v___x_3018_ = lean_ptr_addr(v_e_x27_3010_);
v___x_3019_ = lean_ptr_addr(v_a_3014_);
v___x_3020_ = lean_usize_dec_eq(v___x_3018_, v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3038_; 
lean_inc_ref(v_proof_3011_);
lean_inc_ref(v_e_x27_3010_);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_result_2974_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; lean_object* v_unused_3040_; 
v_unused_3039_ = lean_ctor_get(v_result_2974_, 1);
lean_dec(v_unused_3039_);
v_unused_3040_ = lean_ctor_get(v_result_2974_, 0);
lean_dec(v_unused_3040_);
v___x_3022_ = v_result_2974_;
v_isShared_3023_ = v_isSharedCheck_3038_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v_result_2974_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3038_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3024_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_u_3009_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
lean_inc_ref(v___x_3026_);
v___x_3027_ = l_Lean_mkConst(v___x_3024_, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3029_ = l_Lean_mkConst(v___x_3028_, v___x_3026_);
lean_inc_n(v_a_3014_, 2);
lean_inc_ref(v_00_u03b1_3008_);
v___x_3030_ = l_Lean_mkAppB(v___x_3029_, v_00_u03b1_3008_, v_a_3014_);
v___x_3031_ = l_Lean_mkApp6(v___x_3027_, v_00_u03b1_3008_, v_e_u2081_2960_, v_e_x27_3010_, v_a_3014_, v_proof_3011_, v___x_3030_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3031_);
lean_ctor_set(v___x_3022_, 0, v_a_3014_);
v___x_3033_ = v___x_3022_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3014_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3031_);
lean_ctor_set_uint8(v_reuseFailAlloc_3037_, sizeof(void*)*2 + 1, v_contextDependent_3012_);
v___x_3033_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3035_; 
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*2, v___x_3020_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3033_);
v___x_3035_ = v___x_3016_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v___x_3042_; 
lean_dec(v_a_3014_);
lean_dec(v_u_3009_);
lean_dec_ref(v_00_u03b1_3008_);
lean_dec_ref(v_e_u2081_2960_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v_result_2974_);
v___x_3042_ = v___x_3016_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_result_2974_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_u_3009_);
lean_dec_ref(v_00_u03b1_3008_);
lean_dec_ref_known(v_result_2974_, 2);
lean_dec_ref(v_e_u2081_2960_);
v_a_3045_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3013_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3013_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_e_u2081_2960_);
v_a_3053_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2972_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2972_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_3061_, lean_object* v_simpBody_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_3061_, v_simpBody_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_3074_, lean_object* v_e_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
uint8_t v___x_3086_; 
v___x_3086_ = l_Lean_Expr_letNondep_x21(v_e_3075_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref(v_e_3075_);
lean_dec_ref(v_simpBody_3074_);
v___x_3087_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3087_, 0, v___x_3086_);
lean_ctor_set_uint8(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_3075_, v_simpBody_3074_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_3090_, lean_object* v_e_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_3090_, v_e_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_3116_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_3115_, v_e_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec_ref(v_a_3119_);
lean_dec(v_a_3118_);
return v_res_3128_;
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
