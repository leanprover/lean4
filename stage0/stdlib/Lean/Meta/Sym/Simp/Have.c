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
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0));
v___x_161_ = lean_box(1);
v___x_162_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_161_, v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_163_, lean_object* v_fvarIdToPos_164_){
_start:
{
lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___x_173_; lean_object* v___y_175_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_s_183_; lean_object* v_fvarIds_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0));
v___x_182_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v_s_183_ = l_Lean_collectFVars(v___x_182_, v_e_163_);
v_fvarIds_184_ = lean_ctor_get(v_s_183_, 2);
lean_inc_ref(v_fvarIds_184_);
lean_dec_ref(v_s_183_);
v___x_185_ = lean_array_get_size(v_fvarIds_184_);
v___x_186_ = lean_nat_dec_lt(v___x_173_, v___x_185_);
if (v___x_186_ == 0)
{
lean_dec_ref(v_fvarIds_184_);
v___y_175_ = v___x_181_;
goto v___jp_174_;
}
else
{
size_t v___x_187_; size_t v___x_188_; lean_object* v___x_189_; 
v___x_187_ = ((size_t)0ULL);
v___x_188_ = lean_usize_of_nat(v___x_185_);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_164_, v_fvarIds_184_, v___x_187_, v___x_188_, v___x_181_);
lean_dec_ref(v_fvarIds_184_);
v___y_175_ = v___x_189_;
goto v___jp_174_;
}
v___jp_165_:
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_le(v___y_169_, v___y_167_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_dec(v___y_167_);
lean_inc(v___y_169_);
v___x_171_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_164_, v___y_168_, v___y_166_, v___y_169_, v___y_169_);
lean_dec(v___y_169_);
lean_dec(v___y_168_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_164_, v___y_168_, v___y_166_, v___y_169_, v___y_167_);
lean_dec(v___y_167_);
lean_dec(v___y_168_);
return v___x_172_;
}
}
v___jp_174_:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_array_get_size(v___y_175_);
v___x_177_ = lean_nat_dec_eq(v___x_176_, v___x_173_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_sub(v___x_176_, v___x_178_);
v___x_180_ = lean_nat_dec_le(v___x_173_, v___x_179_);
if (v___x_180_ == 0)
{
lean_inc(v___x_179_);
v___y_166_ = v___y_175_;
v___y_167_ = v___x_179_;
v___y_168_ = v___x_176_;
v___y_169_ = v___x_179_;
goto v___jp_165_;
}
else
{
v___y_166_ = v___y_175_;
v___y_167_ = v___x_179_;
v___y_168_ = v___x_176_;
v___y_169_ = v___x_173_;
goto v___jp_165_;
}
}
else
{
return v___y_175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(lean_object* v_e_190_, lean_object* v_fvarIdToPos_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_e_190_, v_fvarIdToPos_191_);
lean_dec(v_fvarIdToPos_191_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_193_, lean_object* v_k_194_, lean_object* v_t_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_194_, v_t_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_197_, lean_object* v_k_198_, lean_object* v_t_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_197_, v_k_198_, v_t_199_);
lean_dec(v_t_199_);
lean_dec(v_k_198_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_202_, lean_object* v_n_203_, lean_object* v_as_204_, lean_object* v_lo_205_, lean_object* v_hi_206_, lean_object* v_w_207_, lean_object* v_hlo_208_, lean_object* v_hhi_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_202_, v_n_203_, v_as_204_, v_lo_205_, v_hi_206_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_211_, lean_object* v_n_212_, lean_object* v_as_213_, lean_object* v_lo_214_, lean_object* v_hi_215_, lean_object* v_w_216_, lean_object* v_hlo_217_, lean_object* v_hhi_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_211_, v_n_212_, v_as_213_, v_lo_214_, v_hi_215_, v_w_216_, v_hlo_217_, v_hhi_218_);
lean_dec(v_hi_215_);
lean_dec(v_n_212_);
lean_dec(v_fvarIdToPos_211_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(lean_object* v_fvarIdToPos_220_, lean_object* v_n_221_, lean_object* v_lo_222_, lean_object* v_hi_223_, lean_object* v_hhi_224_, lean_object* v_pivot_225_, lean_object* v_as_226_, lean_object* v_i_227_, lean_object* v_k_228_, lean_object* v_ilo_229_, lean_object* v_ik_230_, lean_object* v_w_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_220_, v_hi_223_, v_pivot_225_, v_as_226_, v_i_227_, v_k_228_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(lean_object* v_fvarIdToPos_233_, lean_object* v_n_234_, lean_object* v_lo_235_, lean_object* v_hi_236_, lean_object* v_hhi_237_, lean_object* v_pivot_238_, lean_object* v_as_239_, lean_object* v_i_240_, lean_object* v_k_241_, lean_object* v_ilo_242_, lean_object* v_ik_243_, lean_object* v_w_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(v_fvarIdToPos_233_, v_n_234_, v_lo_235_, v_hi_236_, v_hhi_237_, v_pivot_238_, v_as_239_, v_i_240_, v_k_241_, v_ilo_242_, v_ik_243_, v_w_244_);
lean_dec(v_pivot_238_);
lean_dec(v_hi_236_);
lean_dec(v_lo_235_);
lean_dec(v_n_234_);
lean_dec(v_fvarIdToPos_233_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_246_, uint8_t v_bi_247_, lean_object* v_t_248_, lean_object* v_b_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___y_258_; lean_object* v___x_261_; uint8_t v_debug_262_; 
v___x_261_ = lean_st_ref_get(v___y_251_);
v_debug_262_ = lean_ctor_get_uint8(v___x_261_, sizeof(void*)*12);
lean_dec(v___x_261_);
if (v_debug_262_ == 0)
{
v___y_258_ = v___y_251_;
goto v___jp_257_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_248_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_264_; 
lean_dec_ref_known(v___x_263_, 1);
v___x_264_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_dec_ref_known(v___x_264_, 1);
v___y_258_ = v___y_251_;
goto v___jp_257_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v_b_249_);
lean_dec_ref(v_t_248_);
lean_dec(v_x_246_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_b_249_);
lean_dec_ref(v_t_248_);
lean_dec(v_x_246_);
v_a_273_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_263_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = l_Lean_Expr_forallE___override(v_x_246_, v_t_248_, v_b_249_, v_bi_247_);
v___x_260_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_259_, v___y_258_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_281_, lean_object* v_bi_282_, lean_object* v_t_283_, lean_object* v_b_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_bi_boxed_292_; lean_object* v_res_293_; 
v_bi_boxed_292_ = lean_unbox(v_bi_282_);
v_res_293_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_281_, v_bi_boxed_292_, v_t_283_, v_b_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_297_, lean_object* v_i_298_, lean_object* v_00_u03b2_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_zero_307_; uint8_t v_isZero_308_; 
v_zero_307_ = lean_unsigned_to_nat(0u);
v_isZero_308_ = lean_nat_dec_eq(v_i_298_, v_zero_307_);
if (v_isZero_308_ == 1)
{
lean_object* v___x_309_; 
lean_dec(v_i_298_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v_00_u03b2_299_);
return v___x_309_;
}
else
{
lean_object* v_one_310_; lean_object* v_n_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_one_310_ = lean_unsigned_to_nat(1u);
v_n_311_ = lean_nat_sub(v_i_298_, v_one_310_);
lean_dec(v_i_298_);
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_313_ = 0;
v___x_314_ = lean_array_fget_borrowed(v_00_u03b1s_297_, v_n_311_);
lean_inc(v___x_314_);
v___x_315_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_312_, v___x_313_, v___x_314_, v_00_u03b2_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v_i_298_ = v_n_311_;
v_00_u03b2_299_ = v_a_316_;
goto _start;
}
else
{
lean_dec(v_n_311_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_318_, lean_object* v_i_319_, lean_object* v_00_u03b2_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_318_, v_i_319_, v_00_u03b2_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec_ref(v_00_u03b1s_318_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_329_, lean_object* v_i_330_, lean_object* v_00_u03b2_331_, lean_object* v_h_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_329_, v_i_330_, v_00_u03b2_331_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_341_, lean_object* v_i_342_, lean_object* v_00_u03b2_343_, lean_object* v_h_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_341_, v_i_342_, v_00_u03b2_343_, v_h_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec_ref(v_00_u03b1s_341_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_353_, lean_object* v_00_u03b2_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_array_get_size(v_00_u03b1s_353_);
v___x_363_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_353_, v___x_362_, v_00_u03b2_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_364_, lean_object* v_00_u03b2_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_364_, v_00_u03b2_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_00_u03b1s_364_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_374_, lean_object* v_subst_375_, size_t v_sz_376_, size_t v_i_377_, lean_object* v_bs_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_lt(v_i_377_, v_sz_376_);
if (v___x_379_ == 0)
{
return v_bs_378_;
}
else
{
lean_object* v___x_380_; lean_object* v_v_381_; lean_object* v___x_382_; lean_object* v_bs_x27_383_; lean_object* v___x_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v___x_380_ = l_Lean_instInhabitedExpr;
v_v_381_ = lean_array_uget(v_bs_378_, v_i_377_);
v___x_382_ = lean_unsigned_to_nat(0u);
v_bs_x27_383_ = lean_array_uset(v_bs_378_, v_i_377_, v___x_382_);
v___x_384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_374_, v_v_381_);
lean_dec(v_v_381_);
v___x_385_ = lean_array_get_borrowed(v___x_380_, v_subst_375_, v___x_384_);
lean_dec(v___x_384_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_add(v_i_377_, v___x_386_);
lean_inc(v___x_385_);
v___x_388_ = lean_array_uset(v_bs_x27_383_, v_i_377_, v___x_385_);
v_i_377_ = v___x_387_;
v_bs_378_ = v___x_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_390_, lean_object* v_subst_391_, lean_object* v_sz_392_, lean_object* v_i_393_, lean_object* v_bs_394_){
_start:
{
size_t v_sz_boxed_395_; size_t v_i_boxed_396_; lean_object* v_res_397_; 
v_sz_boxed_395_ = lean_unbox_usize(v_sz_392_);
lean_dec(v_sz_392_);
v_i_boxed_396_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_390_, v_subst_391_, v_sz_boxed_395_, v_i_boxed_396_, v_bs_394_);
lean_dec_ref(v_subst_391_);
lean_dec(v_fvarIdToPos_390_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_398_, size_t v_i_399_, lean_object* v_bs_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = lean_usize_dec_lt(v_i_399_, v_sz_398_);
if (v___x_401_ == 0)
{
return v_bs_400_;
}
else
{
lean_object* v_v_402_; lean_object* v___x_403_; lean_object* v_bs_x27_404_; lean_object* v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_v_402_ = lean_array_uget(v_bs_400_, v_i_399_);
v___x_403_ = lean_unsigned_to_nat(0u);
v_bs_x27_404_ = lean_array_uset(v_bs_400_, v_i_399_, v___x_403_);
v___x_405_ = l_Lean_mkFVar(v_v_402_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_399_, v___x_406_);
v___x_408_ = lean_array_uset(v_bs_x27_404_, v_i_399_, v___x_405_);
v_i_399_ = v___x_407_;
v_bs_400_ = v___x_408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_410_, lean_object* v_i_411_, lean_object* v_bs_412_){
_start:
{
size_t v_sz_boxed_413_; size_t v_i_boxed_414_; lean_object* v_res_415_; 
v_sz_boxed_413_ = lean_unbox_usize(v_sz_410_);
lean_dec(v_sz_410_);
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_413_, v_i_boxed_414_, v_bs_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
v___x_425_ = lean_apply_8(v_k_416_, v_b_419_, v___y_417_, v___y_418_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, lean_box(0));
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v_b_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_426_, v___y_427_, v___y_428_, v_b_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_436_, uint8_t v_bi_437_, lean_object* v_type_438_, lean_object* v_k_439_, uint8_t v_kind_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; 
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_448_, 0, v_k_439_);
lean_closure_set(v___f_448_, 1, v___y_441_);
lean_closure_set(v___f_448_, 2, v___y_442_);
v___x_449_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_436_, v_bi_437_, v_type_438_, v___f_448_, v_kind_440_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_449_) == 0)
{
return v___x_449_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_458_, lean_object* v_bi_459_, lean_object* v_type_460_, lean_object* v_k_461_, lean_object* v_kind_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
uint8_t v_bi_boxed_470_; uint8_t v_kind_boxed_471_; lean_object* v_res_472_; 
v_bi_boxed_470_ = lean_unbox(v_bi_459_);
v_kind_boxed_471_ = lean_unbox(v_kind_462_);
v_res_472_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_458_, v_bi_boxed_470_, v_type_460_, v_k_461_, v_kind_boxed_471_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_473_, lean_object* v_type_474_, lean_object* v_k_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = 0;
v___x_484_ = 0;
v___x_485_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_473_, v___x_483_, v_type_474_, v_k_475_, v___x_484_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_486_, lean_object* v_type_487_, lean_object* v_k_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_486_, v_type_487_, v_k_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_497_, lean_object* v_k_498_, lean_object* v_fallback_499_){
_start:
{
if (lean_obj_tag(v_t_497_) == 0)
{
lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v_l_502_; lean_object* v_r_503_; uint8_t v___x_504_; 
v_k_500_ = lean_ctor_get(v_t_497_, 1);
v_v_501_ = lean_ctor_get(v_t_497_, 2);
v_l_502_ = lean_ctor_get(v_t_497_, 3);
v_r_503_ = lean_ctor_get(v_t_497_, 4);
v___x_504_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_498_, v_k_500_);
switch(v___x_504_)
{
case 0:
{
v_t_497_ = v_l_502_;
goto _start;
}
case 1:
{
lean_inc(v_v_501_);
return v_v_501_;
}
default: 
{
v_t_497_ = v_r_503_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_499_);
return v_fallback_499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_507_, lean_object* v_k_508_, lean_object* v_fallback_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_507_, v_k_508_, v_fallback_509_);
lean_dec(v_fallback_509_);
lean_dec(v_k_508_);
lean_dec(v_t_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_511_, size_t v_sz_512_, size_t v_i_513_, lean_object* v_bs_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_513_, v_sz_512_);
if (v___x_515_ == 0)
{
return v_bs_514_;
}
else
{
lean_object* v_v_516_; lean_object* v___x_517_; lean_object* v_bs_x27_518_; lean_object* v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v_v_516_ = lean_array_uget(v_bs_514_, v_i_513_);
v___x_517_ = lean_unsigned_to_nat(0u);
v_bs_x27_518_ = lean_array_uset(v_bs_514_, v_i_513_, v___x_517_);
v___x_519_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_511_, v_v_516_, v___x_517_);
lean_dec(v_v_516_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_add(v_i_513_, v___x_520_);
v___x_522_ = lean_array_uset(v_bs_x27_518_, v_i_513_, v___x_519_);
v_i_513_ = v___x_521_;
v_bs_514_ = v___x_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_524_, lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_bs_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_524_, v_sz_boxed_528_, v_i_boxed_529_, v_bs_527_);
lean_dec(v_fvarIdToPos_524_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_540_ = _args[0];
lean_object* v_subst_541_ = _args[1];
lean_object* v_sz_542_ = _args[2];
lean_object* v___x_543_ = _args[3];
lean_object* v_fvarIds_544_ = _args[4];
lean_object* v_x_545_ = _args[5];
lean_object* v_xs_546_ = _args[6];
lean_object* v_xs_x27_547_ = _args[7];
lean_object* v_args_548_ = _args[8];
lean_object* v_a_549_ = _args[9];
lean_object* v_types_550_ = _args[10];
lean_object* v_a_551_ = _args[11];
lean_object* v_varDeps_552_ = _args[12];
lean_object* v_varPos_553_ = _args[13];
lean_object* v_haveExpr_554_ = _args[14];
lean_object* v_body_555_ = _args[15];
lean_object* v_x_x27_556_ = _args[16];
lean_object* v___y_557_ = _args[17];
lean_object* v___y_558_ = _args[18];
lean_object* v___y_559_ = _args[19];
lean_object* v___y_560_ = _args[20];
lean_object* v___y_561_ = _args[21];
lean_object* v___y_562_ = _args[22];
lean_object* v___y_563_ = _args[23];
_start:
{
size_t v_sz_boxed_564_; size_t v___x_6407__boxed_565_; lean_object* v_res_566_; 
v_sz_boxed_564_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v___x_6407__boxed_565_ = lean_unbox_usize(v___x_543_);
lean_dec(v___x_543_);
v_res_566_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_540_, v_subst_541_, v_sz_boxed_564_, v___x_6407__boxed_565_, v_fvarIds_544_, v_x_545_, v_xs_546_, v_xs_x27_547_, v_args_548_, v_a_549_, v_types_550_, v_a_551_, v_varDeps_552_, v_varPos_553_, v_haveExpr_554_, v_body_555_, v_x_x27_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_v_567_, lean_object* v_fvarIdToPos_568_, uint8_t v_nondep_569_, lean_object* v_t_570_, lean_object* v_subst_571_, lean_object* v_xs_572_, lean_object* v_xs_x27_573_, lean_object* v_args_574_, lean_object* v_types_575_, lean_object* v_varDeps_576_, lean_object* v_haveExpr_577_, lean_object* v_body_578_, lean_object* v_declName_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_fvarIds_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v_varPos_591_; lean_object* v_ys_592_; uint8_t v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; 
lean_inc_ref(v_v_567_);
v_fvarIds_588_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_567_, v_fvarIdToPos_568_);
v_sz_589_ = lean_array_size(v_fvarIds_588_);
v___x_590_ = ((size_t)0ULL);
lean_inc_ref_n(v_fvarIds_588_, 2);
v_varPos_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_568_, v_sz_589_, v___x_590_, v_fvarIds_588_);
v_ys_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_589_, v___x_590_, v_fvarIds_588_);
v___x_593_ = 0;
v___x_594_ = 1;
v___x_595_ = l_Lean_Meta_mkLambdaFVars(v_ys_592_, v_v_567_, v___x_593_, v_nondep_569_, v___x_593_, v_nondep_569_, v___x_594_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = l_Lean_Meta_mkForallFVars(v_ys_592_, v_t_570_, v___x_593_, v_nondep_569_, v_nondep_569_, v___x_594_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec_ref(v_ys_592_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l_Lean_Meta_Sym_shareCommonInc(v_a_598_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc_n(v_a_600_, 2);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_box_usize(v_sz_589_);
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
v___f_603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_603_, 0, v_fvarIdToPos_568_);
lean_closure_set(v___f_603_, 1, v_subst_571_);
lean_closure_set(v___f_603_, 2, v___x_601_);
lean_closure_set(v___f_603_, 3, v___x_602_);
lean_closure_set(v___f_603_, 4, v_fvarIds_588_);
lean_closure_set(v___f_603_, 5, v_x_580_);
lean_closure_set(v___f_603_, 6, v_xs_572_);
lean_closure_set(v___f_603_, 7, v_xs_x27_573_);
lean_closure_set(v___f_603_, 8, v_args_574_);
lean_closure_set(v___f_603_, 9, v_a_596_);
lean_closure_set(v___f_603_, 10, v_types_575_);
lean_closure_set(v___f_603_, 11, v_a_600_);
lean_closure_set(v___f_603_, 12, v_varDeps_576_);
lean_closure_set(v___f_603_, 13, v_varPos_591_);
lean_closure_set(v___f_603_, 14, v_haveExpr_577_);
lean_closure_set(v___f_603_, 15, v_body_578_);
v___x_604_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_579_, v_a_600_, v___f_603_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_604_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_a_596_);
lean_dec_ref(v_varPos_591_);
lean_dec_ref(v_fvarIds_588_);
lean_dec_ref(v_x_580_);
lean_dec(v_declName_579_);
lean_dec_ref(v_body_578_);
lean_dec_ref(v_haveExpr_577_);
lean_dec_ref(v_varDeps_576_);
lean_dec_ref(v_types_575_);
lean_dec_ref(v_args_574_);
lean_dec_ref(v_xs_x27_573_);
lean_dec_ref(v_xs_572_);
lean_dec_ref(v_subst_571_);
lean_dec(v_fvarIdToPos_568_);
v_a_605_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_599_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_599_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_596_);
lean_dec_ref(v_varPos_591_);
lean_dec_ref(v_fvarIds_588_);
lean_dec_ref(v_x_580_);
lean_dec(v_declName_579_);
lean_dec_ref(v_body_578_);
lean_dec_ref(v_haveExpr_577_);
lean_dec_ref(v_varDeps_576_);
lean_dec_ref(v_types_575_);
lean_dec_ref(v_args_574_);
lean_dec_ref(v_xs_x27_573_);
lean_dec_ref(v_xs_572_);
lean_dec_ref(v_subst_571_);
lean_dec(v_fvarIdToPos_568_);
v_a_613_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_597_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_597_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_ys_592_);
lean_dec_ref(v_varPos_591_);
lean_dec_ref(v_fvarIds_588_);
lean_dec_ref(v_x_580_);
lean_dec(v_declName_579_);
lean_dec_ref(v_body_578_);
lean_dec_ref(v_haveExpr_577_);
lean_dec_ref(v_varDeps_576_);
lean_dec_ref(v_types_575_);
lean_dec_ref(v_args_574_);
lean_dec_ref(v_xs_x27_573_);
lean_dec_ref(v_xs_572_);
lean_dec_ref(v_subst_571_);
lean_dec_ref(v_t_570_);
lean_dec(v_fvarIdToPos_568_);
v_a_621_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_595_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_595_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_v_629_ = _args[0];
lean_object* v_fvarIdToPos_630_ = _args[1];
lean_object* v_nondep_631_ = _args[2];
lean_object* v_t_632_ = _args[3];
lean_object* v_subst_633_ = _args[4];
lean_object* v_xs_634_ = _args[5];
lean_object* v_xs_x27_635_ = _args[6];
lean_object* v_args_636_ = _args[7];
lean_object* v_types_637_ = _args[8];
lean_object* v_varDeps_638_ = _args[9];
lean_object* v_haveExpr_639_ = _args[10];
lean_object* v_body_640_ = _args[11];
lean_object* v_declName_641_ = _args[12];
lean_object* v_x_642_ = _args[13];
lean_object* v___y_643_ = _args[14];
lean_object* v___y_644_ = _args[15];
lean_object* v___y_645_ = _args[16];
lean_object* v___y_646_ = _args[17];
lean_object* v___y_647_ = _args[18];
lean_object* v___y_648_ = _args[19];
lean_object* v___y_649_ = _args[20];
_start:
{
uint8_t v_nondep_6434__boxed_650_; lean_object* v_res_651_; 
v_nondep_6434__boxed_650_ = lean_unbox(v_nondep_631_);
v_res_651_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_v_629_, v_fvarIdToPos_630_, v_nondep_6434__boxed_650_, v_t_632_, v_subst_633_, v_xs_634_, v_xs_x27_635_, v_args_636_, v_types_637_, v_varDeps_638_, v_haveExpr_639_, v_body_640_, v_declName_641_, v_x_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_652_, lean_object* v_e_653_, lean_object* v_xs_654_, lean_object* v_xs_x27_655_, lean_object* v_args_656_, lean_object* v_subst_657_, lean_object* v_types_658_, lean_object* v_varDeps_659_, lean_object* v_fvarIdToPos_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; 
if (lean_obj_tag(v_e_653_) == 8)
{
uint8_t v_nondep_755_; 
v_nondep_755_ = lean_ctor_get_uint8(v_e_653_, sizeof(void*)*4 + 8);
if (v_nondep_755_ == 1)
{
lean_object* v_declName_756_; lean_object* v_type_757_; lean_object* v_value_758_; lean_object* v_body_759_; lean_object* v_t_760_; lean_object* v_v_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v_declName_756_ = lean_ctor_get(v_e_653_, 0);
lean_inc_n(v_declName_756_, 2);
v_type_757_ = lean_ctor_get(v_e_653_, 1);
lean_inc_ref(v_type_757_);
v_value_758_ = lean_ctor_get(v_e_653_, 2);
lean_inc_ref(v_value_758_);
v_body_759_ = lean_ctor_get(v_e_653_, 3);
lean_inc_ref(v_body_759_);
lean_dec_ref_known(v_e_653_, 4);
v_t_760_ = lean_expr_instantiate_rev(v_type_757_, v_xs_654_);
lean_dec_ref(v_type_757_);
v_v_761_ = lean_expr_instantiate_rev(v_value_758_, v_xs_654_);
lean_dec_ref(v_value_758_);
v___x_762_ = lean_box(v_nondep_755_);
lean_inc_ref(v_t_760_);
v___f_763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 21, 13);
lean_closure_set(v___f_763_, 0, v_v_761_);
lean_closure_set(v___f_763_, 1, v_fvarIdToPos_660_);
lean_closure_set(v___f_763_, 2, v___x_762_);
lean_closure_set(v___f_763_, 3, v_t_760_);
lean_closure_set(v___f_763_, 4, v_subst_657_);
lean_closure_set(v___f_763_, 5, v_xs_654_);
lean_closure_set(v___f_763_, 6, v_xs_x27_655_);
lean_closure_set(v___f_763_, 7, v_args_656_);
lean_closure_set(v___f_763_, 8, v_types_658_);
lean_closure_set(v___f_763_, 9, v_varDeps_659_);
lean_closure_set(v___f_763_, 10, v_haveExpr_652_);
lean_closure_set(v___f_763_, 11, v_body_759_);
lean_closure_set(v___f_763_, 12, v_declName_756_);
v___x_764_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_756_, v_t_760_, v___f_763_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
return v___x_764_;
}
else
{
lean_dec(v_fvarIdToPos_660_);
lean_dec_ref(v_xs_654_);
v___y_669_ = v_a_661_;
v___y_670_ = v_a_662_;
v___y_671_ = v_a_663_;
v___y_672_ = v_a_664_;
v___y_673_ = v_a_665_;
v___y_674_ = v_a_666_;
goto v___jp_668_;
}
}
else
{
lean_dec(v_fvarIdToPos_660_);
lean_dec_ref(v_xs_654_);
v___y_669_ = v_a_661_;
v___y_670_ = v_a_662_;
v___y_671_ = v_a_663_;
v___y_672_ = v_a_664_;
v___y_673_ = v_a_665_;
v___y_674_ = v_a_666_;
goto v___jp_668_;
}
v___jp_668_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_size(v_subst_657_);
v___x_677_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_653_, v___x_675_, v___x_676_, v_subst_657_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_n(v_a_678_, 2);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = l_Lean_Meta_Sym_inferType(v_a_678_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_n(v_a_680_, 2);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_680_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
lean_inc(v_a_680_);
v___x_683_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_658_, v_a_680_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec_ref(v_types_658_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_655_, v_a_678_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = l_Lean_mkAppN(v_a_686_, v_args_656_);
lean_dec_ref(v_args_656_);
v___x_688_ = l_Lean_Meta_Sym_shareCommonInc(v___x_687_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_706_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_706_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_706_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_706_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_694_ = lean_box(0);
lean_inc(v_a_682_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v_a_682_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
lean_inc_ref(v___x_695_);
v___x_696_ = l_Lean_mkConst(v___x_693_, v___x_695_);
lean_inc(v_a_689_);
lean_inc_ref(v_haveExpr_652_);
lean_inc_n(v_a_680_, 2);
v___x_697_ = l_Lean_mkApp3(v___x_696_, v_a_680_, v_haveExpr_652_, v_a_689_);
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_699_ = l_Lean_mkConst(v___x_698_, v___x_695_);
v___x_700_ = l_Lean_mkAppB(v___x_699_, v_a_680_, v_haveExpr_652_);
v___x_701_ = l_Lean_Meta_mkExpectedPropHint(v___x_700_, v___x_697_);
v___x_702_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_702_, 0, v_a_680_);
lean_ctor_set(v___x_702_, 1, v_a_682_);
lean_ctor_set(v___x_702_, 2, v_a_689_);
lean_ctor_set(v___x_702_, 3, v___x_701_);
lean_ctor_set(v___x_702_, 4, v_varDeps_659_);
lean_ctor_set(v___x_702_, 5, v_a_684_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_702_);
v___x_704_ = v___x_691_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_a_684_);
lean_dec(v_a_682_);
lean_dec(v_a_680_);
lean_dec_ref(v_varDeps_659_);
lean_dec_ref(v_haveExpr_652_);
v_a_707_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_688_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_688_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_a_684_);
lean_dec(v_a_682_);
lean_dec(v_a_680_);
lean_dec_ref(v_varDeps_659_);
lean_dec_ref(v_args_656_);
lean_dec_ref(v_haveExpr_652_);
v_a_715_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_685_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_685_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_682_);
lean_dec(v_a_680_);
lean_dec(v_a_678_);
lean_dec_ref(v_varDeps_659_);
lean_dec_ref(v_args_656_);
lean_dec_ref(v_xs_x27_655_);
lean_dec_ref(v_haveExpr_652_);
v_a_723_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_683_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_683_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_680_);
lean_dec(v_a_678_);
lean_dec_ref(v_varDeps_659_);
lean_dec_ref(v_types_658_);
lean_dec_ref(v_args_656_);
lean_dec_ref(v_xs_x27_655_);
lean_dec_ref(v_haveExpr_652_);
v_a_731_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_681_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_681_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_a_678_);
lean_dec_ref(v_varDeps_659_);
lean_dec_ref(v_types_658_);
lean_dec_ref(v_args_656_);
lean_dec_ref(v_xs_x27_655_);
lean_dec_ref(v_haveExpr_652_);
v_a_739_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_679_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_679_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_varDeps_659_);
lean_dec_ref(v_types_658_);
lean_dec_ref(v_args_656_);
lean_dec_ref(v_xs_x27_655_);
lean_dec_ref(v_haveExpr_652_);
v_a_747_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_677_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_677_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_765_, lean_object* v_subst_766_, size_t v_sz_767_, size_t v___x_768_, lean_object* v_fvarIds_769_, lean_object* v_x_770_, lean_object* v_xs_771_, lean_object* v_xs_x27_772_, lean_object* v_args_773_, lean_object* v_a_774_, lean_object* v_types_775_, lean_object* v_a_776_, lean_object* v_varDeps_777_, lean_object* v_varPos_778_, lean_object* v_haveExpr_779_, lean_object* v_body_780_, lean_object* v_x_x27_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_765_, v_subst_766_, v_sz_767_, v___x_768_, v_fvarIds_769_);
lean_inc_ref(v_x_x27_781_);
v___x_790_ = l_Lean_mkAppN(v_x_x27_781_, v___x_789_);
lean_dec_ref(v___x_789_);
v___x_791_ = l_Lean_Meta_Sym_shareCommonInc(v___x_790_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_Expr_fvarId_x21(v_x_770_);
v___x_794_ = lean_array_get_size(v_xs_771_);
v___x_795_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_793_, v___x_794_, v_fvarIdToPos_765_);
v___x_796_ = lean_array_push(v_xs_771_, v_x_770_);
v___x_797_ = lean_array_push(v_xs_x27_772_, v_x_x27_781_);
v___x_798_ = lean_array_push(v_args_773_, v_a_774_);
v___x_799_ = lean_array_push(v_subst_766_, v_a_792_);
v___x_800_ = lean_array_push(v_types_775_, v_a_776_);
v___x_801_ = lean_array_push(v_varDeps_777_, v_varPos_778_);
v___x_802_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_779_, v_body_780_, v___x_796_, v___x_797_, v___x_798_, v___x_799_, v___x_800_, v___x_801_, v___x_795_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_802_;
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v_x_x27_781_);
lean_dec_ref(v_body_780_);
lean_dec_ref(v_haveExpr_779_);
lean_dec_ref(v_varPos_778_);
lean_dec_ref(v_varDeps_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_types_775_);
lean_dec_ref(v_a_774_);
lean_dec_ref(v_args_773_);
lean_dec_ref(v_xs_x27_772_);
lean_dec_ref(v_xs_771_);
lean_dec_ref(v_x_770_);
lean_dec_ref(v_subst_766_);
lean_dec(v_fvarIdToPos_765_);
v_a_803_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_791_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_791_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_811_, lean_object* v_e_812_, lean_object* v_xs_813_, lean_object* v_xs_x27_814_, lean_object* v_args_815_, lean_object* v_subst_816_, lean_object* v_types_817_, lean_object* v_varDeps_818_, lean_object* v_fvarIdToPos_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_811_, v_e_812_, v_xs_813_, v_xs_x27_814_, v_args_815_, v_subst_816_, v_types_817_, v_varDeps_818_, v_fvarIdToPos_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_828_, lean_object* v_t_829_, lean_object* v_k_830_, lean_object* v_fallback_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_829_, v_k_830_, v_fallback_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_833_, lean_object* v_t_834_, lean_object* v_k_835_, lean_object* v_fallback_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_833_, v_t_834_, v_k_835_, v_fallback_836_);
lean_dec(v_fallback_836_);
lean_dec(v_k_835_);
lean_dec(v_t_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_838_, lean_object* v_name_839_, uint8_t v_bi_840_, lean_object* v_type_841_, lean_object* v_k_842_, uint8_t v_kind_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_839_, v_bi_840_, v_type_841_, v_k_842_, v_kind_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_852_, lean_object* v_name_853_, lean_object* v_bi_854_, lean_object* v_type_855_, lean_object* v_k_856_, lean_object* v_kind_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v_bi_boxed_865_; uint8_t v_kind_boxed_866_; lean_object* v_res_867_; 
v_bi_boxed_865_ = lean_unbox(v_bi_854_);
v_kind_boxed_866_ = lean_unbox(v_kind_857_);
v_res_867_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_852_, v_name_853_, v_bi_boxed_865_, v_type_855_, v_k_856_, v_kind_boxed_866_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_868_, lean_object* v_name_869_, lean_object* v_type_870_, lean_object* v_k_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_869_, v_type_870_, v_k_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_880_, lean_object* v_name_881_, lean_object* v_type_882_, lean_object* v_k_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_880_, v_name_881_, v_type_882_, v_k_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_903_ = lean_box(1);
lean_inc_ref(v_haveExpr_894_);
v___x_904_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_894_, v_haveExpr_894_, v___x_902_, v___x_902_, v___x_902_, v___x_902_, v___x_902_, v___x_902_, v___x_903_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_914_, lean_object* v_n_915_){
_start:
{
lean_object* v_zero_916_; uint8_t v_isZero_917_; 
v_zero_916_ = lean_unsigned_to_nat(0u);
v_isZero_917_ = lean_nat_dec_eq(v_n_915_, v_zero_916_);
if (v_isZero_917_ == 1)
{
lean_dec(v_n_915_);
return v_type_914_;
}
else
{
lean_object* v_one_918_; lean_object* v_n_919_; lean_object* v___x_920_; 
v_one_918_ = lean_unsigned_to_nat(1u);
v_n_919_ = lean_nat_sub(v_n_915_, v_one_918_);
lean_dec(v_n_915_);
v___x_920_ = l_Lean_Expr_bindingBody_x21(v_type_914_);
lean_dec_ref(v_type_914_);
v_type_914_ = v___x_920_;
v_n_915_ = v_n_919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(lean_object* v_idx_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = l_Lean_Expr_bvar___override(v_idx_922_);
v___x_925_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_924_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_idx_926_, uint8_t v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v_idx_926_, v___y_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___boxed(lean_object* v_idx_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v___y_24940__boxed_935_; lean_object* v_res_936_; 
v___y_24940__boxed_935_ = lean_unbox(v___y_932_);
v_res_936_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(v_idx_931_, v___y_24940__boxed_935_, v___y_933_, v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0(void){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_HashMap_instInhabited___redArg();
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_msg_938_, uint8_t v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___x_1486__overap_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_942_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___closed__0);
v___f_943_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_943_, 0, v___x_942_);
v___f_944_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_944_, 0, v___f_943_);
v___f_945_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_945_, 0, v___f_944_);
v___x_1486__overap_946_ = lean_panic_fn_borrowed(v___f_945_, v_msg_938_);
lean_dec_ref(v___f_945_);
v___x_947_ = lean_box(v___y_939_);
lean_inc_ref(v___y_940_);
v___x_948_ = lean_apply_3(v___x_1486__overap_946_, v___x_947_, v___y_940_, v___y_941_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
uint8_t v___y_24953__boxed_953_; lean_object* v_res_954_; 
v___y_24953__boxed_953_ = lean_unbox(v___y_950_);
v_res_954_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_msg_949_, v___y_24953__boxed_953_, v___y_951_, v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_954_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0(void){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_1948__overap_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0);
v___x_1948__overap_965_ = lean_panic_fn_borrowed(v___x_964_, v_msg_956_);
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
v___x_966_ = lean_apply_7(v___x_1948__overap_965_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, lean_box(0));
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(lean_object* v_x_976_, lean_object* v_t_977_, lean_object* v_v_978_, lean_object* v_b_979_, uint8_t v_nondep_980_, lean_object* v___y_981_, uint8_t v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___y_986_; lean_object* v___y_987_; 
if (v___y_982_ == 0)
{
v___y_986_ = v___y_981_;
v___y_987_ = v___y_984_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_977_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 1);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 2);
v___x_1011_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_978_, v___y_982_, v___y_983_, v_a_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 2);
v___x_1013_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_979_, v___y_982_, v___y_983_, v_a_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 1);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 2);
v___y_986_ = v___y_981_;
v___y_987_ = v_a_1014_;
goto v___jp_985_;
}
else
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___y_981_);
lean_dec_ref(v_b_979_);
lean_dec_ref(v_v_978_);
lean_dec_ref(v_t_977_);
lean_dec(v_x_976_);
v_a_1015_ = lean_ctor_get(v___x_1013_, 0);
v_a_1016_ = lean_ctor_get(v___x_1013_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1013_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_inc(v_a_1015_);
lean_dec(v___x_1013_);
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
else
{
lean_object* v_a_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref(v___y_981_);
lean_dec_ref(v_b_979_);
lean_dec_ref(v_v_978_);
lean_dec_ref(v_t_977_);
lean_dec(v_x_976_);
v_a_1024_ = lean_ctor_get(v___x_1011_, 0);
v_a_1025_ = lean_ctor_get(v___x_1011_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1011_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_inc(v_a_1024_);
lean_dec(v___x_1011_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1024_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v___y_981_);
lean_dec_ref(v_b_979_);
lean_dec_ref(v_v_978_);
lean_dec_ref(v_t_977_);
lean_dec(v_x_976_);
v_a_1033_ = lean_ctor_get(v___x_1009_, 0);
v_a_1034_ = lean_ctor_get(v___x_1009_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1009_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_inc(v_a_1033_);
lean_dec(v___x_1009_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1033_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
v___jp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l_Lean_Expr_letE___override(v_x_976_, v_t_977_, v_v_978_, v_b_979_, v_nondep_980_);
v___x_989_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_988_, v___y_987_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_a_991_ = lean_ctor_get(v___x_989_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_a_990_);
lean_ctor_set(v___x_995_, 1, v___y_986_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_a_991_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v___y_986_);
v_a_1000_ = lean_ctor_get(v___x_989_, 0);
v_a_1001_ = lean_ctor_get(v___x_989_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_989_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_inc(v_a_1000_);
lean_dec(v___x_989_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6___boxed(lean_object* v_x_1042_, lean_object* v_t_1043_, lean_object* v_v_1044_, lean_object* v_b_1045_, lean_object* v_nondep_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_nondep_boxed_1051_; uint8_t v___y_25004__boxed_1052_; lean_object* v_res_1053_; 
v_nondep_boxed_1051_ = lean_unbox(v_nondep_1046_);
v___y_25004__boxed_1052_ = lean_unbox(v___y_1048_);
v_res_1053_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_x_1042_, v_t_1043_, v_v_1044_, v_b_1045_, v_nondep_boxed_1051_, v___y_1047_, v___y_25004__boxed_1052_, v___y_1049_, v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(lean_object* v_x_1054_, uint8_t v_bi_1055_, lean_object* v_t_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, uint8_t v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___y_1063_; lean_object* v___y_1064_; 
if (v___y_1059_ == 0)
{
v___y_1063_ = v___y_1058_;
v___y_1064_ = v___y_1061_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1056_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 1);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 2);
v___x_1088_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1057_, v___y_1059_, v___y_1060_, v_a_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 1);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 2);
v___y_1063_ = v___y_1058_;
v___y_1064_ = v_a_1089_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_b_1057_);
lean_dec_ref(v_t_1056_);
lean_dec(v_x_1054_);
v_a_1090_ = lean_ctor_get(v___x_1088_, 0);
v_a_1091_ = lean_ctor_get(v___x_1088_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1088_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_inc(v_a_1090_);
lean_dec(v___x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_b_1057_);
lean_dec_ref(v_t_1056_);
lean_dec(v_x_1054_);
v_a_1099_ = lean_ctor_get(v___x_1086_, 0);
v_a_1100_ = lean_ctor_get(v___x_1086_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1086_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_inc(v_a_1099_);
lean_dec(v___x_1086_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1099_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = l_Lean_Expr_lam___override(v_x_1054_, v_t_1056_, v_b_1057_, v_bi_1055_);
v___x_1066_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1065_, v___y_1064_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_a_1068_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_a_1067_);
lean_ctor_set(v___x_1072_, 1, v___y_1063_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_a_1068_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___y_1063_);
v_a_1077_ = lean_ctor_get(v___x_1066_, 0);
v_a_1078_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1066_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_inc(v_a_1077_);
lean_dec(v___x_1066_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4___boxed(lean_object* v_x_1108_, lean_object* v_bi_1109_, lean_object* v_t_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v_bi_boxed_1116_; uint8_t v___y_25133__boxed_1117_; lean_object* v_res_1118_; 
v_bi_boxed_1116_ = lean_unbox(v_bi_1109_);
v___y_25133__boxed_1117_ = lean_unbox(v___y_1113_);
v_res_1118_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_x_1108_, v_bi_boxed_1116_, v_t_1110_, v_b_1111_, v___y_1112_, v___y_25133__boxed_1117_, v___y_1114_, v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(lean_object* v_x_1119_, uint8_t v_bi_1120_, lean_object* v_t_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_, uint8_t v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___y_1128_; lean_object* v___y_1129_; 
if (v___y_1124_ == 0)
{
v___y_1128_ = v___y_1123_;
v___y_1129_ = v___y_1126_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1121_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 2);
v___x_1153_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1122_, v___y_1124_, v___y_1125_, v_a_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 2);
v___y_1128_ = v___y_1123_;
v___y_1129_ = v_a_1154_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_1155_; lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v___y_1123_);
lean_dec_ref(v_b_1122_);
lean_dec_ref(v_t_1121_);
lean_dec(v_x_1119_);
v_a_1155_ = lean_ctor_get(v___x_1153_, 0);
v_a_1156_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1153_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_inc(v_a_1155_);
lean_dec(v___x_1153_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1155_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v___y_1123_);
lean_dec_ref(v_b_1122_);
lean_dec_ref(v_t_1121_);
lean_dec(v_x_1119_);
v_a_1164_ = lean_ctor_get(v___x_1151_, 0);
v_a_1165_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1151_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_inc(v_a_1164_);
lean_dec(v___x_1151_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
v___jp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = l_Lean_Expr_forallE___override(v_x_1119_, v_t_1121_, v_b_1122_, v_bi_1120_);
v___x_1131_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1130_, v___y_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_a_1133_ = lean_ctor_get(v___x_1131_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1132_);
lean_ctor_set(v___x_1137_, 1, v___y_1128_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_a_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v___y_1128_);
v_a_1142_ = lean_ctor_get(v___x_1131_, 0);
v_a_1143_ = lean_ctor_get(v___x_1131_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1131_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_inc(v_a_1142_);
lean_dec(v___x_1131_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5___boxed(lean_object* v_x_1173_, lean_object* v_bi_1174_, lean_object* v_t_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_bi_boxed_1181_; uint8_t v___y_25239__boxed_1182_; lean_object* v_res_1183_; 
v_bi_boxed_1181_ = lean_unbox(v_bi_1174_);
v___y_25239__boxed_1182_ = lean_unbox(v___y_1178_);
v_res_1183_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_x_1173_, v_bi_boxed_1181_, v_t_1175_, v_b_1176_, v___y_1177_, v___y_25239__boxed_1182_, v___y_1179_, v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(lean_object* v_f_1184_, lean_object* v_a_1185_, lean_object* v___y_1186_, uint8_t v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___y_1191_; lean_object* v___y_1192_; 
if (v___y_1187_ == 0)
{
v___y_1191_ = v___y_1186_;
v___y_1192_ = v___y_1189_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1184_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 2);
v___x_1216_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1185_, v___y_1187_, v___y_1188_, v_a_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 2);
v___y_1191_ = v___y_1186_;
v___y_1192_ = v_a_1217_;
goto v___jp_1190_;
}
else
{
lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_a_1185_);
lean_dec_ref(v_f_1184_);
v_a_1218_ = lean_ctor_get(v___x_1216_, 0);
v_a_1219_ = lean_ctor_get(v___x_1216_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1216_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_inc(v_a_1218_);
lean_dec(v___x_1216_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1218_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_a_1185_);
lean_dec_ref(v_f_1184_);
v_a_1227_ = lean_ctor_get(v___x_1214_, 0);
v_a_1228_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1214_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_inc(v_a_1227_);
lean_dec(v___x_1214_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1227_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
v___jp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_Expr_app___override(v_f_1184_, v_a_1185_);
v___x_1194_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1193_, v___y_1192_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1204_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_a_1196_ = lean_ctor_get(v___x_1194_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1198_ = v___x_1194_;
v_isShared_1199_ = v_isSharedCheck_1204_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1204_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_a_1195_);
lean_ctor_set(v___x_1200_, 1, v___y_1191_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1200_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_a_1196_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v___y_1191_);
v_a_1205_ = lean_ctor_get(v___x_1194_, 0);
v_a_1206_ = lean_ctor_get(v___x_1194_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1194_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_inc(v_a_1205_);
lean_dec(v___x_1194_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3___boxed(lean_object* v_f_1236_, lean_object* v_a_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v___y_25345__boxed_1242_; lean_object* v_res_1243_; 
v___y_25345__boxed_1242_ = lean_unbox(v___y_1239_);
v_res_1243_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_f_1236_, v_a_1237_, v___y_1238_, v___y_25345__boxed_1242_, v___y_1240_, v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(lean_object* v_d_1244_, lean_object* v_e_1245_, lean_object* v___y_1246_, uint8_t v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___y_1251_; lean_object* v___y_1252_; 
if (v___y_1247_ == 0)
{
v___y_1251_ = v___y_1246_;
v___y_1252_ = v___y_1249_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1245_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 2);
v___y_1251_ = v___y_1246_;
v___y_1252_ = v_a_1275_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1276_; lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_e_1245_);
lean_dec(v_d_1244_);
v_a_1276_ = lean_ctor_get(v___x_1274_, 0);
v_a_1277_ = lean_ctor_get(v___x_1274_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1274_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_inc(v_a_1276_);
lean_dec(v___x_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1276_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
v___jp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lean_Expr_mdata___override(v_d_1244_, v_e_1245_);
v___x_1254_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1253_, v___y_1252_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1264_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_a_1256_ = lean_ctor_get(v___x_1254_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1258_ = v___x_1254_;
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1255_);
lean_ctor_set(v___x_1260_, 1, v___y_1251_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1260_);
v___x_1262_ = v___x_1258_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_a_1256_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v___y_1251_);
v_a_1265_ = lean_ctor_get(v___x_1254_, 0);
v_a_1266_ = lean_ctor_get(v___x_1254_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1254_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_inc(v_a_1265_);
lean_dec(v___x_1254_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1265_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7___boxed(lean_object* v_d_1285_, lean_object* v_e_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v___y_25451__boxed_1291_; lean_object* v_res_1292_; 
v___y_25451__boxed_1291_ = lean_unbox(v___y_1288_);
v_res_1292_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_d_1285_, v_e_1286_, v___y_1287_, v___y_25451__boxed_1291_, v___y_1289_, v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(lean_object* v_msg_1300_, lean_object* v___y_1301_, uint8_t v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___f_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_24463__overap_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___f_1305_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__0));
v___f_1306_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__1));
v___f_1307_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__2));
v___x_1308_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__3));
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___f_1305_);
v___x_1310_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__4));
v___x_1311_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__5));
v___x_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1309_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___f_1306_);
lean_ctor_set(v___x_1312_, 3, v___f_1307_);
lean_ctor_set(v___x_1312_, 4, v___x_1311_);
v___x_1313_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___closed__6));
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_ReaderT_instMonad___redArg(v___x_1314_);
v___x_1316_ = l_ReaderT_instMonad___redArg(v___x_1315_);
lean_inc_ref_n(v___x_1316_, 6);
v___f_1317_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1317_, 0, v___x_1316_);
v___f_1318_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1318_, 0, v___x_1316_);
v___f_1319_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1319_, 0, v___x_1316_);
v___f_1320_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1320_, 0, v___x_1316_);
v___x_1321_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, lean_box(0));
lean_closure_set(v___x_1321_, 2, v___x_1316_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___f_1317_);
v___x_1323_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, lean_box(0));
lean_closure_set(v___x_1323_, 2, v___x_1316_);
v___x_1324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
lean_ctor_set(v___x_1324_, 2, v___f_1318_);
lean_ctor_set(v___x_1324_, 3, v___f_1319_);
lean_ctor_set(v___x_1324_, 4, v___f_1320_);
v___x_1325_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1325_, 0, lean_box(0));
lean_closure_set(v___x_1325_, 1, lean_box(0));
lean_closure_set(v___x_1325_, 2, v___x_1316_);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = l_Lean_instInhabitedExpr;
v___x_1328_ = l_instInhabitedOfMonad___redArg(v___x_1326_, v___x_1327_);
v___x_24463__overap_1329_ = lean_panic_fn_borrowed(v___x_1328_, v_msg_1300_);
lean_dec(v___x_1328_);
v___x_1330_ = lean_box(v___y_1302_);
lean_inc_ref(v___y_1303_);
v___x_1331_ = lean_apply_4(v___x_24463__overap_1329_, v___y_1301_, v___x_1330_, v___y_1303_, v___y_1304_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9___boxed(lean_object* v_msg_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___y_25548__boxed_1337_; lean_object* v_res_1338_; 
v___y_25548__boxed_1337_ = lean_unbox(v___y_1334_);
v_res_1338_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v_msg_1332_, v___y_1333_, v___y_25548__boxed_1337_, v___y_1335_, v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(lean_object* v_structName_1339_, lean_object* v_idx_1340_, lean_object* v_struct_1341_, lean_object* v___y_1342_, uint8_t v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___y_1347_; lean_object* v___y_1348_; 
if (v___y_1343_ == 0)
{
v___y_1347_ = v___y_1342_;
v___y_1348_ = v___y_1345_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_1341_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 1);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 2);
v___y_1347_ = v___y_1342_;
v___y_1348_ = v_a_1371_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1372_; lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v___y_1342_);
lean_dec_ref(v_struct_1341_);
lean_dec(v_idx_1340_);
lean_dec(v_structName_1339_);
v_a_1372_ = lean_ctor_get(v___x_1370_, 0);
v_a_1373_ = lean_ctor_get(v___x_1370_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1370_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_inc(v_a_1372_);
lean_dec(v___x_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1372_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
v___jp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = l_Lean_Expr_proj___override(v_structName_1339_, v_idx_1340_, v_struct_1341_);
v___x_1350_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1349_, v___y_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_a_1352_ = lean_ctor_get(v___x_1350_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1350_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_a_1351_);
lean_ctor_set(v___x_1356_, 1, v___y_1347_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_a_1352_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v___y_1347_);
v_a_1361_ = lean_ctor_get(v___x_1350_, 0);
v_a_1362_ = lean_ctor_get(v___x_1350_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1350_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_inc(v_a_1361_);
lean_dec(v___x_1350_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1361_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8___boxed(lean_object* v_structName_1381_, lean_object* v_idx_1382_, lean_object* v_struct_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v___y_25619__boxed_1388_; lean_object* v_res_1389_; 
v___y_25619__boxed_1388_ = lean_unbox(v___y_1385_);
v_res_1389_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_structName_1381_, v_idx_1382_, v_struct_1383_, v___y_1384_, v___y_25619__boxed_1388_, v___y_1386_, v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_box(0);
return v___x_1392_;
}
else
{
lean_object* v_key_1393_; lean_object* v_value_1394_; lean_object* v_tail_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; size_t v___x_1400_; size_t v___x_1401_; uint8_t v___x_1402_; 
v_key_1393_ = lean_ctor_get(v_x_1391_, 0);
v_value_1394_ = lean_ctor_get(v_x_1391_, 1);
v_tail_1395_ = lean_ctor_get(v_x_1391_, 2);
v_fst_1396_ = lean_ctor_get(v_key_1393_, 0);
v_snd_1397_ = lean_ctor_get(v_key_1393_, 1);
v_fst_1398_ = lean_ctor_get(v_a_1390_, 0);
v_snd_1399_ = lean_ctor_get(v_a_1390_, 1);
v___x_1400_ = lean_ptr_addr(v_fst_1396_);
v___x_1401_ = lean_ptr_addr(v_fst_1398_);
v___x_1402_ = lean_usize_dec_eq(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
v_x_1391_ = v_tail_1395_;
goto _start;
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_eq(v_snd_1397_, v_snd_1399_);
if (v___x_1404_ == 0)
{
v_x_1391_ = v_tail_1395_;
goto _start;
}
else
{
lean_object* v___x_1406_; 
lean_inc(v_value_1394_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_value_1394_);
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_1407_, lean_object* v_x_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1407_, v_x_1408_);
lean_dec(v_x_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(lean_object* v_m_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_buckets_1412_; lean_object* v_fst_1413_; lean_object* v_snd_1414_; lean_object* v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; uint64_t v___x_1419_; uint64_t v___x_1420_; uint64_t v___x_1421_; uint64_t v___x_1422_; uint64_t v___x_1423_; uint64_t v_fold_1424_; uint64_t v___x_1425_; uint64_t v___x_1426_; uint64_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_buckets_1412_ = lean_ctor_get(v_m_1410_, 1);
v_fst_1413_ = lean_ctor_get(v_a_1411_, 0);
v_snd_1414_ = lean_ctor_get(v_a_1411_, 1);
v___x_1415_ = lean_array_get_size(v_buckets_1412_);
v___x_1416_ = lean_ptr_addr(v_fst_1413_);
v___x_1417_ = ((size_t)3ULL);
v___x_1418_ = lean_usize_shift_right(v___x_1416_, v___x_1417_);
v___x_1419_ = lean_usize_to_uint64(v___x_1418_);
v___x_1420_ = lean_uint64_of_nat(v_snd_1414_);
v___x_1421_ = lean_uint64_mix_hash(v___x_1419_, v___x_1420_);
v___x_1422_ = 32ULL;
v___x_1423_ = lean_uint64_shift_right(v___x_1421_, v___x_1422_);
v_fold_1424_ = lean_uint64_xor(v___x_1421_, v___x_1423_);
v___x_1425_ = 16ULL;
v___x_1426_ = lean_uint64_shift_right(v_fold_1424_, v___x_1425_);
v___x_1427_ = lean_uint64_xor(v_fold_1424_, v___x_1426_);
v___x_1428_ = lean_uint64_to_usize(v___x_1427_);
v___x_1429_ = lean_usize_of_nat(v___x_1415_);
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_sub(v___x_1429_, v___x_1430_);
v___x_1432_ = lean_usize_land(v___x_1428_, v___x_1431_);
v___x_1433_ = lean_array_uget_borrowed(v_buckets_1412_, v___x_1432_);
v___x_1434_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1411_, v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1435_, v_a_1436_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_m_1435_);
return v_res_1437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Array_instInhabited___redArg();
return v___x_1438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1442_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__3));
v___x_1443_ = lean_unsigned_to_nat(12u);
v___x_1444_ = lean_unsigned_to_nat(234u);
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__2));
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_1447_ = l_mkPanicMessageWithDecl(v___x_1446_, v___x_1445_, v___x_1444_, v___x_1443_, v___x_1442_);
return v___x_1447_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1452_ = lean_unsigned_to_nat(67u);
v___x_1453_ = lean_unsigned_to_nat(35u);
v___x_1454_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___x_1456_ = l_mkPanicMessageWithDecl(v___x_1455_, v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_n_1457_, lean_object* v_varDeps_1458_, lean_object* v_xs_1459_, lean_object* v_e_1460_, lean_object* v_offset_1461_, lean_object* v_a_1462_, uint8_t v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
switch(lean_obj_tag(v_e_1460_))
{
case 5:
{
lean_object* v_fn_1466_; lean_object* v_arg_1467_; lean_object* v___x_1468_; 
v_fn_1466_ = lean_ctor_get(v_e_1460_, 0);
v_arg_1467_ = lean_ctor_get(v_e_1460_, 1);
lean_inc(v_offset_1461_);
lean_inc_ref(v_fn_1466_);
v___x_1468_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_fn_1466_, v_offset_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v_a_1470_; lean_object* v_fst_1471_; lean_object* v_snd_1472_; lean_object* v___x_1473_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
v_a_1470_ = lean_ctor_get(v___x_1468_, 1);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1468_, 2);
v_fst_1471_ = lean_ctor_get(v_a_1469_, 0);
lean_inc(v_fst_1471_);
v_snd_1472_ = lean_ctor_get(v_a_1469_, 1);
lean_inc(v_snd_1472_);
lean_dec(v_a_1469_);
lean_inc_ref(v_arg_1467_);
v___x_1473_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_arg_1467_, v_offset_1461_, v_snd_1472_, v_a_1463_, v_a_1464_, v_a_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1499_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_a_1475_ = lean_ctor_get(v___x_1473_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1477_ = v___x_1473_;
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1498_; 
v_fst_1479_ = lean_ctor_get(v_a_1474_, 0);
v_snd_1480_ = lean_ctor_get(v_a_1474_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1482_ = v_a_1474_;
v_isShared_1483_ = v_isSharedCheck_1498_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1480_);
lean_inc(v_fst_1479_);
lean_dec(v_a_1474_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1498_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
size_t v___x_1484_; size_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_ptr_addr(v_fn_1466_);
v___x_1485_ = lean_ptr_addr(v_fst_1471_);
v___x_1486_ = lean_usize_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
lean_del_object(v___x_1482_);
lean_del_object(v___x_1477_);
lean_dec_ref_known(v_e_1460_, 2);
v___x_1487_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1471_, v_fst_1479_, v_snd_1480_, v_a_1463_, v_a_1464_, v_a_1475_);
return v___x_1487_;
}
else
{
size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v___x_1488_ = lean_ptr_addr(v_arg_1467_);
v___x_1489_ = lean_ptr_addr(v_fst_1479_);
v___x_1490_ = lean_usize_dec_eq(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_del_object(v___x_1482_);
lean_del_object(v___x_1477_);
lean_dec_ref_known(v_e_1460_, 2);
v___x_1491_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__3(v_fst_1471_, v_fst_1479_, v_snd_1480_, v_a_1463_, v_a_1464_, v_a_1475_);
return v___x_1491_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_fst_1479_);
lean_dec(v_fst_1471_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_e_1460_);
v___x_1493_ = v___x_1482_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_e_1460_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_snd_1480_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1493_);
v___x_1495_ = v___x_1477_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_a_1475_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1471_);
lean_dec_ref_known(v_e_1460_, 2);
return v___x_1473_;
}
}
else
{
lean_dec_ref_known(v_e_1460_, 2);
lean_dec(v_offset_1461_);
return v___x_1468_;
}
}
case 6:
{
lean_object* v_binderName_1500_; lean_object* v_binderType_1501_; lean_object* v_body_1502_; uint8_t v_binderInfo_1503_; lean_object* v___x_1504_; 
v_binderName_1500_ = lean_ctor_get(v_e_1460_, 0);
v_binderType_1501_ = lean_ctor_get(v_e_1460_, 1);
v_body_1502_ = lean_ctor_get(v_e_1460_, 2);
v_binderInfo_1503_ = lean_ctor_get_uint8(v_e_1460_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1461_);
lean_inc_ref(v_binderType_1501_);
v___x_1504_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_binderType_1501_, v_offset_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v_a_1506_; lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
v_a_1506_ = lean_ctor_get(v___x_1504_, 1);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1504_, 2);
v_fst_1507_ = lean_ctor_get(v_a_1505_, 0);
lean_inc(v_fst_1507_);
v_snd_1508_ = lean_ctor_get(v_a_1505_, 1);
lean_inc(v_snd_1508_);
lean_dec(v_a_1505_);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v_offset_1461_, v___x_1509_);
lean_dec(v_offset_1461_);
lean_inc_ref(v_body_1502_);
v___x_1511_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_body_1502_, v___x_1510_, v_snd_1508_, v_a_1463_, v_a_1464_, v_a_1506_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1537_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_a_1513_ = lean_ctor_get(v___x_1511_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1515_ = v___x_1511_;
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1536_; 
v_fst_1517_ = lean_ctor_get(v_a_1512_, 0);
v_snd_1518_ = lean_ctor_get(v_a_1512_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_a_1512_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1520_ = v_a_1512_;
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_snd_1518_);
lean_inc(v_fst_1517_);
lean_dec(v_a_1512_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
size_t v___x_1522_; size_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1522_ = lean_ptr_addr(v_binderType_1501_);
v___x_1523_ = lean_ptr_addr(v_fst_1507_);
v___x_1524_ = lean_usize_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_inc(v_binderName_1500_);
lean_del_object(v___x_1520_);
lean_del_object(v___x_1515_);
lean_dec_ref_known(v_e_1460_, 3);
v___x_1525_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1500_, v_binderInfo_1503_, v_fst_1507_, v_fst_1517_, v_snd_1518_, v_a_1463_, v_a_1464_, v_a_1513_);
return v___x_1525_;
}
else
{
size_t v___x_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_ptr_addr(v_body_1502_);
v___x_1527_ = lean_ptr_addr(v_fst_1517_);
v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_binderName_1500_);
lean_del_object(v___x_1520_);
lean_del_object(v___x_1515_);
lean_dec_ref_known(v_e_1460_, 3);
v___x_1529_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__4(v_binderName_1500_, v_binderInfo_1503_, v_fst_1507_, v_fst_1517_, v_snd_1518_, v_a_1463_, v_a_1464_, v_a_1513_);
return v___x_1529_;
}
else
{
lean_object* v___x_1531_; 
lean_dec(v_fst_1517_);
lean_dec(v_fst_1507_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_e_1460_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_e_1460_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_snd_1518_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1531_);
v___x_1533_ = v___x_1515_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_a_1513_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1507_);
lean_dec_ref_known(v_e_1460_, 3);
return v___x_1511_;
}
}
else
{
lean_dec_ref_known(v_e_1460_, 3);
lean_dec(v_offset_1461_);
return v___x_1504_;
}
}
case 7:
{
lean_object* v_binderName_1538_; lean_object* v_binderType_1539_; lean_object* v_body_1540_; uint8_t v_binderInfo_1541_; lean_object* v___x_1542_; 
v_binderName_1538_ = lean_ctor_get(v_e_1460_, 0);
v_binderType_1539_ = lean_ctor_get(v_e_1460_, 1);
v_body_1540_ = lean_ctor_get(v_e_1460_, 2);
v_binderInfo_1541_ = lean_ctor_get_uint8(v_e_1460_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1461_);
lean_inc_ref(v_binderType_1539_);
v___x_1542_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_binderType_1539_, v_offset_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_a_1544_; lean_object* v_fst_1545_; lean_object* v_snd_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
v_a_1544_ = lean_ctor_get(v___x_1542_, 1);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1542_, 2);
v_fst_1545_ = lean_ctor_get(v_a_1543_, 0);
lean_inc(v_fst_1545_);
v_snd_1546_ = lean_ctor_get(v_a_1543_, 1);
lean_inc(v_snd_1546_);
lean_dec(v_a_1543_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_offset_1461_, v___x_1547_);
lean_dec(v_offset_1461_);
lean_inc_ref(v_body_1540_);
v___x_1549_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_body_1540_, v___x_1548_, v_snd_1546_, v_a_1463_, v_a_1464_, v_a_1544_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1575_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_a_1551_ = lean_ctor_get(v___x_1549_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1553_ = v___x_1549_;
v_isShared_1554_ = v_isSharedCheck_1575_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1575_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_fst_1555_; lean_object* v_snd_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1574_; 
v_fst_1555_ = lean_ctor_get(v_a_1550_, 0);
v_snd_1556_ = lean_ctor_get(v_a_1550_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1558_ = v_a_1550_;
v_isShared_1559_ = v_isSharedCheck_1574_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_snd_1556_);
lean_inc(v_fst_1555_);
lean_dec(v_a_1550_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1574_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
size_t v___x_1560_; size_t v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = lean_ptr_addr(v_binderType_1539_);
v___x_1561_ = lean_ptr_addr(v_fst_1545_);
v___x_1562_ = lean_usize_dec_eq(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_inc(v_binderName_1538_);
lean_del_object(v___x_1558_);
lean_del_object(v___x_1553_);
lean_dec_ref_known(v_e_1460_, 3);
v___x_1563_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1538_, v_binderInfo_1541_, v_fst_1545_, v_fst_1555_, v_snd_1556_, v_a_1463_, v_a_1464_, v_a_1551_);
return v___x_1563_;
}
else
{
size_t v___x_1564_; size_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_ptr_addr(v_body_1540_);
v___x_1565_ = lean_ptr_addr(v_fst_1555_);
v___x_1566_ = lean_usize_dec_eq(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_inc(v_binderName_1538_);
lean_del_object(v___x_1558_);
lean_del_object(v___x_1553_);
lean_dec_ref_known(v_e_1460_, 3);
v___x_1567_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__5(v_binderName_1538_, v_binderInfo_1541_, v_fst_1545_, v_fst_1555_, v_snd_1556_, v_a_1463_, v_a_1464_, v_a_1551_);
return v___x_1567_;
}
else
{
lean_object* v___x_1569_; 
lean_dec(v_fst_1555_);
lean_dec(v_fst_1545_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v_e_1460_);
v___x_1569_ = v___x_1558_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_e_1460_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_snd_1556_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1569_);
v___x_1571_ = v___x_1553_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_a_1551_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1545_);
lean_dec_ref_known(v_e_1460_, 3);
return v___x_1549_;
}
}
else
{
lean_dec_ref_known(v_e_1460_, 3);
lean_dec(v_offset_1461_);
return v___x_1542_;
}
}
case 8:
{
lean_object* v_declName_1576_; lean_object* v_type_1577_; lean_object* v_value_1578_; lean_object* v_body_1579_; uint8_t v_nondep_1580_; lean_object* v___x_1581_; 
v_declName_1576_ = lean_ctor_get(v_e_1460_, 0);
v_type_1577_ = lean_ctor_get(v_e_1460_, 1);
v_value_1578_ = lean_ctor_get(v_e_1460_, 2);
v_body_1579_ = lean_ctor_get(v_e_1460_, 3);
v_nondep_1580_ = lean_ctor_get_uint8(v_e_1460_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1461_);
lean_inc_ref(v_type_1577_);
v___x_1581_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_type_1577_, v_offset_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v_a_1583_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1586_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
v_a_1583_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1581_, 2);
v_fst_1584_ = lean_ctor_get(v_a_1582_, 0);
lean_inc(v_fst_1584_);
v_snd_1585_ = lean_ctor_get(v_a_1582_, 1);
lean_inc(v_snd_1585_);
lean_dec(v_a_1582_);
lean_inc(v_offset_1461_);
lean_inc_ref(v_value_1578_);
v___x_1586_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_value_1578_, v_offset_1461_, v_snd_1585_, v_a_1463_, v_a_1464_, v_a_1583_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v_a_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
v_a_1588_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1586_, 2);
v_fst_1589_ = lean_ctor_get(v_a_1587_, 0);
lean_inc(v_fst_1589_);
v_snd_1590_ = lean_ctor_get(v_a_1587_, 1);
lean_inc(v_snd_1590_);
lean_dec(v_a_1587_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_add(v_offset_1461_, v___x_1591_);
lean_dec(v_offset_1461_);
lean_inc_ref(v_body_1579_);
v___x_1593_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_body_1579_, v___x_1592_, v_snd_1590_, v_a_1463_, v_a_1464_, v_a_1588_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1623_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_a_1595_ = lean_ctor_get(v___x_1593_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1597_ = v___x_1593_;
v_isShared_1598_ = v_isSharedCheck_1623_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1623_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1622_; 
v_fst_1599_ = lean_ctor_get(v_a_1594_, 0);
v_snd_1600_ = lean_ctor_get(v_a_1594_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1594_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1602_ = v_a_1594_;
v_isShared_1603_ = v_isSharedCheck_1622_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_inc(v_fst_1599_);
lean_dec(v_a_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1622_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
size_t v___x_1604_; size_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1604_ = lean_ptr_addr(v_type_1577_);
v___x_1605_ = lean_ptr_addr(v_fst_1584_);
v___x_1606_ = lean_usize_dec_eq(v___x_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; 
lean_inc(v_declName_1576_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1597_);
lean_dec_ref_known(v_e_1460_, 4);
v___x_1607_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1576_, v_fst_1584_, v_fst_1589_, v_fst_1599_, v_nondep_1580_, v_snd_1600_, v_a_1463_, v_a_1464_, v_a_1595_);
return v___x_1607_;
}
else
{
size_t v___x_1608_; size_t v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_ptr_addr(v_value_1578_);
v___x_1609_ = lean_ptr_addr(v_fst_1589_);
v___x_1610_ = lean_usize_dec_eq(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_inc(v_declName_1576_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1597_);
lean_dec_ref_known(v_e_1460_, 4);
v___x_1611_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1576_, v_fst_1584_, v_fst_1589_, v_fst_1599_, v_nondep_1580_, v_snd_1600_, v_a_1463_, v_a_1464_, v_a_1595_);
return v___x_1611_;
}
else
{
size_t v___x_1612_; size_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = lean_ptr_addr(v_body_1579_);
v___x_1613_ = lean_ptr_addr(v_fst_1599_);
v___x_1614_ = lean_usize_dec_eq(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_inc(v_declName_1576_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1597_);
lean_dec_ref_known(v_e_1460_, 4);
v___x_1615_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__6(v_declName_1576_, v_fst_1584_, v_fst_1589_, v_fst_1599_, v_nondep_1580_, v_snd_1600_, v_a_1463_, v_a_1464_, v_a_1595_);
return v___x_1615_;
}
else
{
lean_object* v___x_1617_; 
lean_dec(v_fst_1599_);
lean_dec(v_fst_1589_);
lean_dec(v_fst_1584_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v_e_1460_);
v___x_1617_ = v___x_1602_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_e_1460_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_snd_1600_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1617_);
v___x_1619_ = v___x_1597_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1595_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
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
lean_dec(v_fst_1589_);
lean_dec(v_fst_1584_);
lean_dec_ref_known(v_e_1460_, 4);
return v___x_1593_;
}
}
else
{
lean_dec(v_fst_1584_);
lean_dec_ref_known(v_e_1460_, 4);
lean_dec(v_offset_1461_);
return v___x_1586_;
}
}
else
{
lean_dec_ref_known(v_e_1460_, 4);
lean_dec(v_offset_1461_);
return v___x_1581_;
}
}
case 10:
{
lean_object* v_data_1624_; lean_object* v_expr_1625_; lean_object* v___x_1626_; 
v_data_1624_ = lean_ctor_get(v_e_1460_, 0);
v_expr_1625_ = lean_ctor_get(v_e_1460_, 1);
lean_inc_ref(v_expr_1625_);
v___x_1626_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_expr_1625_, v_offset_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1648_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_a_1628_ = lean_ctor_get(v___x_1626_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1630_ = v___x_1626_;
v_isShared_1631_ = v_isSharedCheck_1648_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1648_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1647_; 
v_fst_1632_ = lean_ctor_get(v_a_1627_, 0);
v_snd_1633_ = lean_ctor_get(v_a_1627_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1627_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1635_ = v_a_1627_;
v_isShared_1636_ = v_isSharedCheck_1647_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_snd_1633_);
lean_inc(v_fst_1632_);
lean_dec(v_a_1627_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1647_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
size_t v___x_1637_; size_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1637_ = lean_ptr_addr(v_expr_1625_);
v___x_1638_ = lean_ptr_addr(v_fst_1632_);
v___x_1639_ = lean_usize_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_inc(v_data_1624_);
lean_del_object(v___x_1635_);
lean_del_object(v___x_1630_);
lean_dec_ref_known(v_e_1460_, 2);
v___x_1640_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__7(v_data_1624_, v_fst_1632_, v_snd_1633_, v_a_1463_, v_a_1464_, v_a_1628_);
return v___x_1640_;
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_fst_1632_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_e_1460_);
v___x_1642_ = v___x_1635_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_e_1460_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_snd_1633_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1642_);
v___x_1644_ = v___x_1630_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1628_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1460_, 2);
return v___x_1626_;
}
}
case 11:
{
lean_object* v_typeName_1649_; lean_object* v_idx_1650_; lean_object* v_struct_1651_; lean_object* v___x_1652_; 
v_typeName_1649_ = lean_ctor_get(v_e_1460_, 0);
v_idx_1650_ = lean_ctor_get(v_e_1460_, 1);
v_struct_1651_ = lean_ctor_get(v_e_1460_, 2);
lean_inc_ref(v_struct_1651_);
v___x_1652_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1457_, v_varDeps_1458_, v_xs_1459_, v_struct_1651_, v_offset_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1674_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_a_1654_ = lean_ctor_get(v___x_1652_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1656_ = v___x_1652_;
v_isShared_1657_ = v_isSharedCheck_1674_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1674_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v_fst_1658_; lean_object* v_snd_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1673_; 
v_fst_1658_ = lean_ctor_get(v_a_1653_, 0);
v_snd_1659_ = lean_ctor_get(v_a_1653_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1653_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1661_ = v_a_1653_;
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_snd_1659_);
lean_inc(v_fst_1658_);
lean_dec(v_a_1653_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
size_t v___x_1663_; size_t v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_ptr_addr(v_struct_1651_);
v___x_1664_ = lean_ptr_addr(v_fst_1658_);
v___x_1665_ = lean_usize_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_inc(v_idx_1650_);
lean_inc(v_typeName_1649_);
lean_del_object(v___x_1661_);
lean_del_object(v___x_1656_);
lean_dec_ref_known(v_e_1460_, 3);
v___x_1666_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__8(v_typeName_1649_, v_idx_1650_, v_fst_1658_, v_snd_1659_, v_a_1463_, v_a_1464_, v_a_1654_);
return v___x_1666_;
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_fst_1658_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v_e_1460_);
v___x_1668_ = v___x_1661_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_e_1460_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_snd_1659_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1668_);
v___x_1670_ = v___x_1656_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1654_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1460_, 3);
return v___x_1652_;
}
}
default: 
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v_offset_1461_);
lean_dec_ref(v_e_1460_);
v___x_1675_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3);
v___x_1676_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__9(v___x_1675_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
return v___x_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(lean_object* v_n_1677_, lean_object* v_varDeps_1678_, lean_object* v_xs_1679_, lean_object* v_e_1680_, lean_object* v_offset_1681_, lean_object* v_a_1682_, uint8_t v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_key_1686_; lean_object* v_a_1688_; lean_object* v___x_1701_; 
lean_inc(v_offset_1681_);
lean_inc_ref(v_e_1680_);
v_key_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1686_, 0, v_e_1680_);
lean_ctor_set(v_key_1686_, 1, v_offset_1681_);
v___x_1701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_a_1682_, v_key_1686_);
if (lean_obj_tag(v___x_1701_) == 1)
{
lean_object* v_val_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref_known(v_key_1686_, 2);
lean_dec(v_offset_1681_);
lean_dec_ref(v_e_1680_);
v_val_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_val_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_val_1702_);
lean_ctor_set(v___x_1703_, 1, v_a_1682_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v_a_1685_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
lean_dec(v___x_1701_);
v___x_1705_ = l_Lean_Expr_looseBVarRange(v_e_1680_);
v___x_1706_ = lean_nat_dec_le(v___x_1705_, v_offset_1681_);
lean_dec(v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Expr_getAppFn(v_e_1680_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_deBruijnIndex_1708_; uint8_t v___x_1709_; 
v_deBruijnIndex_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_deBruijnIndex_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = lean_nat_dec_le(v_offset_1681_, v_deBruijnIndex_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v_deBruijnIndex_1708_);
lean_dec(v_offset_1681_);
v___x_1710_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_nat_add(v_offset_1681_, v_n_1677_);
v___x_1712_ = lean_nat_dec_lt(v_deBruijnIndex_1708_, v___x_1711_);
lean_dec(v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_offset_1681_);
lean_dec_ref(v_e_1680_);
v___x_1713_ = lean_nat_sub(v_deBruijnIndex_1708_, v_n_1677_);
lean_dec(v_deBruijnIndex_1708_);
v___x_1714_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1713_, v_a_1685_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v_a_1716_; lean_object* v___x_1717_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
v_a_1716_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1714_, 2);
v___x_1717_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_a_1715_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1716_);
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref_known(v_key_1686_, 2);
lean_dec_ref(v_a_1682_);
v_a_1718_ = lean_ctor_get(v___x_1714_, 0);
v_a_1719_ = lean_ctor_get(v___x_1714_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1714_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_inc(v_a_1718_);
lean_dec(v___x_1714_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1718_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v_i_1731_; lean_object* v___x_1732_; lean_object* v_expectedNumArgs_1733_; lean_object* v_numArgs_1734_; uint8_t v___x_1735_; 
v___x_1727_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v___x_1728_ = lean_nat_sub(v_deBruijnIndex_1708_, v_offset_1681_);
lean_dec(v_deBruijnIndex_1708_);
v___x_1729_ = lean_nat_sub(v_n_1677_, v___x_1728_);
lean_dec(v___x_1728_);
v___x_1730_ = lean_unsigned_to_nat(1u);
v_i_1731_ = lean_nat_sub(v___x_1729_, v___x_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_array_get_borrowed(v___x_1727_, v_varDeps_1678_, v_i_1731_);
v_expectedNumArgs_1733_ = lean_array_get_size(v___x_1732_);
v_numArgs_1734_ = l_Lean_Expr_getAppNumArgs(v_e_1680_);
v___x_1735_ = lean_nat_dec_lt(v_expectedNumArgs_1733_, v_numArgs_1734_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_eq(v_numArgs_1734_, v_expectedNumArgs_1733_);
lean_dec(v_numArgs_1734_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_i_1731_);
v___x_1737_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1738_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1737_, v_a_1683_, v_a_1684_, v_a_1685_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
if (lean_obj_tag(v_a_1739_) == 1)
{
lean_object* v_a_1740_; lean_object* v_val_1741_; lean_object* v___x_1742_; 
lean_inc_ref(v_a_1739_);
lean_dec(v_offset_1681_);
lean_dec_ref(v_e_1680_);
v_a_1740_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1738_, 2);
v_val_1741_ = lean_ctor_get(v_a_1739_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v_a_1739_, 1);
v___x_1742_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_val_1741_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1740_);
return v___x_1742_;
}
else
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1738_, 2);
v_a_1688_ = v_a_1743_;
goto v___jp_1687_;
}
}
else
{
lean_object* v_a_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref_known(v_key_1686_, 2);
lean_dec_ref(v_a_1682_);
lean_dec(v_offset_1681_);
lean_dec_ref(v_e_1680_);
v_a_1744_ = lean_ctor_get(v___x_1738_, 0);
v_a_1745_ = lean_ctor_get(v___x_1738_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1738_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_inc(v_a_1744_);
lean_dec(v___x_1738_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1744_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_offset_1681_);
lean_dec_ref(v_e_1680_);
v___x_1753_ = lean_array_fget_borrowed(v_xs_1679_, v_i_1731_);
lean_dec(v_i_1731_);
lean_inc(v___x_1753_);
v___x_1754_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v___x_1753_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1754_;
}
}
else
{
lean_dec(v_numArgs_1734_);
lean_dec(v_i_1731_);
v_a_1688_ = v_a_1685_;
goto v___jp_1687_;
}
}
}
}
else
{
lean_dec_ref(v___x_1707_);
v_a_1688_ = v_a_1685_;
goto v___jp_1687_;
}
}
else
{
lean_object* v___x_1755_; 
lean_dec(v_offset_1681_);
v___x_1755_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1755_;
}
}
v___jp_1687_:
{
switch(lean_obj_tag(v_e_1680_))
{
case 9:
{
lean_object* v___x_1689_; 
lean_dec(v_offset_1681_);
v___x_1689_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
return v___x_1689_;
}
case 2:
{
lean_object* v___x_1690_; 
lean_dec(v_offset_1681_);
v___x_1690_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
return v___x_1690_;
}
case 0:
{
lean_object* v___x_1691_; 
lean_dec(v_offset_1681_);
v___x_1691_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
return v___x_1691_;
}
case 1:
{
lean_object* v___x_1692_; 
lean_dec(v_offset_1681_);
v___x_1692_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
return v___x_1692_;
}
case 4:
{
lean_object* v___x_1693_; 
lean_dec(v_offset_1681_);
v___x_1693_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
return v___x_1693_;
}
case 3:
{
lean_object* v___x_1694_; 
lean_dec(v_offset_1681_);
v___x_1694_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_e_1680_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
return v___x_1694_;
}
default: 
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1677_, v_varDeps_1678_, v_xs_1679_, v_e_1680_, v_offset_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1688_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_a_1697_; lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v___x_1700_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
v_a_1697_ = lean_ctor_get(v___x_1695_, 1);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1695_, 2);
v_fst_1698_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_fst_1698_);
v_snd_1699_ = lean_ctor_get(v_a_1696_, 1);
lean_inc(v_snd_1699_);
lean_dec(v_a_1696_);
v___x_1700_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1686_, v_fst_1698_, v_snd_1699_, v_a_1683_, v_a_1684_, v_a_1697_);
return v___x_1700_;
}
else
{
lean_dec_ref_known(v_key_1686_, 2);
return v___x_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___boxed(lean_object* v_n_1756_, lean_object* v_varDeps_1757_, lean_object* v_xs_1758_, lean_object* v_e_1759_, lean_object* v_offset_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v_a_boxed_1765_; lean_object* v_res_1766_; 
v_a_boxed_1765_ = lean_unbox(v_a_1762_);
v_res_1766_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2(v_n_1756_, v_varDeps_1757_, v_xs_1758_, v_e_1759_, v_offset_1760_, v_a_1761_, v_a_boxed_1765_, v_a_1763_, v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec_ref(v_xs_1758_);
lean_dec_ref(v_varDeps_1757_);
lean_dec(v_n_1756_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_n_1767_, lean_object* v_varDeps_1768_, lean_object* v_xs_1769_, lean_object* v_e_1770_, lean_object* v_offset_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
uint8_t v_a_boxed_1776_; lean_object* v_res_1777_; 
v_a_boxed_1776_ = lean_unbox(v_a_1773_);
v_res_1777_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1767_, v_varDeps_1768_, v_xs_1769_, v_e_1770_, v_offset_1771_, v_a_1772_, v_a_boxed_1776_, v_a_1774_, v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v_xs_1769_);
lean_dec_ref(v_varDeps_1768_);
lean_dec(v_n_1767_);
return v_res_1777_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_unsigned_to_nat(16u);
v___x_1780_ = lean_mk_array(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__0);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v___x_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(lean_object* v_e_1784_, lean_object* v_n_1785_, lean_object* v_varDeps_1786_, lean_object* v_xs_1787_, uint8_t v_debug_1788_, lean_object* v___x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v_a_1794_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1822_ = l_Lean_Expr_looseBVarRange(v_e_1784_);
v___x_1823_ = lean_nat_dec_le(v___x_1822_, v___x_1792_);
lean_dec(v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_Expr_getAppFn(v_e_1784_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_deBruijnIndex_1825_; uint8_t v___x_1826_; 
v_deBruijnIndex_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_deBruijnIndex_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = lean_nat_dec_le(v___x_1792_, v_deBruijnIndex_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec(v_deBruijnIndex_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_e_1784_);
lean_ctor_set(v___x_1827_, 1, v___y_1791_);
return v___x_1827_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_nat_dec_lt(v_deBruijnIndex_1825_, v_n_1785_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_e_1784_);
v___x_1829_ = lean_nat_sub(v_deBruijnIndex_1825_, v_n_1785_);
lean_dec(v_deBruijnIndex_1825_);
v___x_1830_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___redArg(v___x_1829_, v___y_1791_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_i_1833_; lean_object* v___x_1834_; lean_object* v_expectedNumArgs_1835_; lean_object* v_numArgs_1836_; uint8_t v___x_1837_; 
v___x_1831_ = lean_nat_sub(v_n_1785_, v_deBruijnIndex_1825_);
lean_dec(v_deBruijnIndex_1825_);
v___x_1832_ = lean_unsigned_to_nat(1u);
v_i_1833_ = lean_nat_sub(v___x_1831_, v___x_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_array_get_borrowed(v___x_1789_, v_varDeps_1786_, v_i_1833_);
v_expectedNumArgs_1835_ = lean_array_get_size(v___x_1834_);
v_numArgs_1836_ = l_Lean_Expr_getAppNumArgs(v_e_1784_);
v___x_1837_ = lean_nat_dec_lt(v_expectedNumArgs_1835_, v_numArgs_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_nat_dec_eq(v_numArgs_1836_, v_expectedNumArgs_1835_);
lean_dec(v_numArgs_1836_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_i_1833_);
v___x_1839_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__4);
v___x_1840_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v___x_1839_, v_debug_1788_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
if (lean_obj_tag(v_a_1841_) == 1)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
lean_inc_ref(v_a_1841_);
lean_dec_ref(v_e_1784_);
v_a_1842_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v___x_1840_, 0);
lean_dec(v_unused_1851_);
v___x_1844_ = v___x_1840_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_val_1846_; lean_object* v___x_1848_; 
v_val_1846_ = lean_ctor_get(v_a_1841_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_a_1841_, 1);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_val_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_val_1846_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_a_1842_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1852_; 
v_a_1852_ = lean_ctor_get(v___x_1840_, 1);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1840_, 2);
v_a_1794_ = v_a_1852_;
goto v___jp_1793_;
}
}
else
{
lean_object* v_a_1853_; lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_e_1784_);
v_a_1853_ = lean_ctor_get(v___x_1840_, 0);
v_a_1854_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1840_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_inc(v_a_1853_);
lean_dec(v___x_1840_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1853_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v_e_1784_);
v___x_1862_ = lean_array_fget_borrowed(v_xs_1787_, v_i_1833_);
lean_dec(v_i_1833_);
lean_inc(v___x_1862_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v___y_1791_);
return v___x_1863_;
}
}
else
{
lean_dec(v_numArgs_1836_);
lean_dec(v_i_1833_);
v_a_1794_ = v___y_1791_;
goto v___jp_1793_;
}
}
}
}
else
{
lean_dec_ref(v___x_1824_);
v_a_1794_ = v___y_1791_;
goto v___jp_1793_;
}
}
else
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_e_1784_);
lean_ctor_set(v___x_1864_, 1, v___y_1791_);
return v___x_1864_;
}
v___jp_1793_:
{
switch(lean_obj_tag(v_e_1784_))
{
case 9:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_e_1784_);
lean_ctor_set(v___x_1795_, 1, v_a_1794_);
return v___x_1795_;
}
case 2:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_e_1784_);
lean_ctor_set(v___x_1796_, 1, v_a_1794_);
return v___x_1796_;
}
case 0:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_e_1784_);
lean_ctor_set(v___x_1797_, 1, v_a_1794_);
return v___x_1797_;
}
case 1:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_e_1784_);
lean_ctor_set(v___x_1798_, 1, v_a_1794_);
return v___x_1798_;
}
case 4:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_e_1784_);
lean_ctor_set(v___x_1799_, 1, v_a_1794_);
return v___x_1799_;
}
case 3:
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_e_1784_);
lean_ctor_set(v___x_1800_, 1, v_a_1794_);
return v___x_1800_;
}
default: 
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___closed__1);
v___x_1802_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_n_1785_, v_varDeps_1786_, v_xs_1787_, v_e_1784_, v___x_1792_, v___x_1801_, v_debug_1788_, v___y_1790_, v_a_1794_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1812_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_a_1804_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1806_ = v___x_1802_;
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_fst_1808_; lean_object* v___x_1810_; 
v_fst_1808_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_fst_1808_);
lean_dec(v_a_1803_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v_fst_1808_);
v___x_1810_ = v___x_1806_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_fst_1808_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_a_1804_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1813_ = lean_ctor_get(v___x_1802_, 0);
v_a_1814_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1802_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_inc(v_a_1813_);
lean_dec(v___x_1802_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1813_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed(lean_object* v_e_1865_, lean_object* v_n_1866_, lean_object* v_varDeps_1867_, lean_object* v_xs_1868_, lean_object* v_debug_1869_, lean_object* v___x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v_debug_boxed_1873_; lean_object* v_res_1874_; 
v_debug_boxed_1873_ = lean_unbox(v_debug_1869_);
v_res_1874_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0(v_e_1865_, v_n_1866_, v_varDeps_1867_, v_xs_1868_, v_debug_boxed_1873_, v___x_1870_, v___y_1871_, v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___x_1870_);
lean_dec_ref(v_xs_1868_);
lean_dec_ref(v_varDeps_1867_);
lean_dec(v_n_1866_);
return v_res_1874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1877_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_1878_ = lean_unsigned_to_nat(16u);
v___x_1879_ = lean_unsigned_to_nat(62u);
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__1));
v___x_1881_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__0));
v___x_1882_ = l_mkPanicMessageWithDecl(v___x_1881_, v___x_1880_, v___x_1879_, v___x_1878_, v___x_1877_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1883_, lean_object* v_xs_1884_, lean_object* v_varDeps_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v_n_1894_; lean_object* v___x_1895_; uint8_t v_debug_1896_; lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v_env_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1893_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__0);
v_n_1894_ = lean_array_get_size(v_xs_1884_);
v___x_1895_ = lean_st_ref_get(v_a_1887_);
v_debug_1896_ = lean_ctor_get_uint8(v___x_1895_, sizeof(void*)*12);
lean_dec(v___x_1895_);
v___x_1897_ = lean_box(v_debug_1896_);
v___f_1898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1898_, 0, v_e_1883_);
lean_closure_set(v___f_1898_, 1, v_n_1894_);
lean_closure_set(v___f_1898_, 2, v_varDeps_1885_);
lean_closure_set(v___f_1898_, 3, v_xs_1884_);
lean_closure_set(v___f_1898_, 4, v___x_1897_);
lean_closure_set(v___f_1898_, 5, v___x_1893_);
v___x_1899_ = lean_st_ref_get(v_a_1891_);
v_env_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc_ref(v_env_1900_);
lean_dec(v___x_1899_);
v___x_1901_ = 0;
v___x_1902_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1902_, 0, v_env_1900_);
lean_ctor_set_uint8(v___x_1902_, sizeof(void*)*1, v___x_1901_);
lean_ctor_set_uint8(v___x_1902_, sizeof(void*)*1 + 1, v___x_1901_);
v___x_1903_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1898_, v___x_1902_, v_a_1887_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1914_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
if (lean_obj_tag(v_a_1904_) == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec_ref_known(v_a_1904_, 1);
lean_del_object(v___x_1906_);
v___x_1908_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___closed__2);
v___x_1909_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_1908_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_1909_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; 
v_a_1910_ = lean_ctor_get(v_a_1904_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v_a_1904_, 1);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_a_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1903_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1903_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1923_, lean_object* v_xs_1924_, lean_object* v_varDeps_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1923_, v_xs_1924_, v_varDeps_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_1934_, lean_object* v_m_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___redArg(v_m_1935_, v_a_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1938_, lean_object* v_m_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4(v_00_u03b2_1938_, v_m_1939_, v_a_1940_);
lean_dec_ref(v_a_1940_);
lean_dec_ref(v_m_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_1942_, lean_object* v_a_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___redArg(v_a_1943_, v_x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1946_, lean_object* v_a_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_1946_, v_a_1947_, v_x_1948_);
lean_dec(v_x_1948_);
lean_dec_ref(v_a_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1950_, lean_object* v_type_1951_, lean_object* v_val_1952_, lean_object* v_k_1953_, uint8_t v_nondep_1954_, uint8_t v_kind_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___f_1963_; lean_object* v___x_1964_; 
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1963_, 0, v_k_1953_);
lean_closure_set(v___f_1963_, 1, v___y_1956_);
lean_closure_set(v___f_1963_, 2, v___y_1957_);
v___x_1964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1950_, v_type_1951_, v_val_1952_, v___f_1963_, v_nondep_1954_, v_kind_1955_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1964_) == 0)
{
return v___x_1964_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1973_, lean_object* v_type_1974_, lean_object* v_val_1975_, lean_object* v_k_1976_, lean_object* v_nondep_1977_, lean_object* v_kind_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
uint8_t v_nondep_boxed_1986_; uint8_t v_kind_boxed_1987_; lean_object* v_res_1988_; 
v_nondep_boxed_1986_ = lean_unbox(v_nondep_1977_);
v_kind_boxed_1987_ = lean_unbox(v_kind_1978_);
v_res_1988_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1973_, v_type_1974_, v_val_1975_, v_k_1976_, v_nondep_boxed_1986_, v_kind_boxed_1987_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1989_, lean_object* v_name_1990_, lean_object* v_type_1991_, lean_object* v_val_1992_, lean_object* v_k_1993_, uint8_t v_nondep_1994_, uint8_t v_kind_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1990_, v_type_1991_, v_val_1992_, v_k_1993_, v_nondep_1994_, v_kind_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_name_2005_, lean_object* v_type_2006_, lean_object* v_val_2007_, lean_object* v_k_2008_, lean_object* v_nondep_2009_, lean_object* v_kind_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
uint8_t v_nondep_boxed_2018_; uint8_t v_kind_boxed_2019_; lean_object* v_res_2020_; 
v_nondep_boxed_2018_ = lean_unbox(v_nondep_2009_);
v_kind_boxed_2019_ = lean_unbox(v_kind_2010_);
v_res_2020_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_2004_, v_name_2005_, v_type_2006_, v_val_2007_, v_k_2008_, v_nondep_boxed_2018_, v_kind_boxed_2019_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_2021_, size_t v_sz_2022_, size_t v_i_2023_, lean_object* v_bs_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
if (v___x_2025_ == 0)
{
return v_bs_2024_;
}
else
{
lean_object* v___x_2026_; lean_object* v_v_2027_; lean_object* v___x_2028_; lean_object* v_bs_x27_2029_; lean_object* v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2026_ = l_Lean_instInhabitedExpr;
v_v_2027_ = lean_array_uget(v_bs_2024_, v_i_2023_);
v___x_2028_ = lean_unsigned_to_nat(0u);
v_bs_x27_2029_ = lean_array_uset(v_bs_2024_, v_i_2023_, v___x_2028_);
v___x_2030_ = lean_array_get_borrowed(v___x_2026_, v_xs_2021_, v_v_2027_);
lean_dec(v_v_2027_);
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2023_, v___x_2031_);
lean_inc(v___x_2030_);
v___x_2033_ = lean_array_uset(v_bs_x27_2029_, v_i_2023_, v___x_2030_);
v_i_2023_ = v___x_2032_;
v_bs_2024_ = v___x_2033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_bs_2038_){
_start:
{
size_t v_sz_boxed_2039_; size_t v_i_boxed_2040_; lean_object* v_res_2041_; 
v_sz_boxed_2039_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2040_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2035_, v_sz_boxed_2039_, v_i_boxed_2040_, v_bs_2038_);
lean_dec_ref(v_xs_2035_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_2042_, lean_object* v_i_2043_, lean_object* v_varDeps_2044_, lean_object* v_args_2045_, lean_object* v_body_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_2042_, v_i_2043_, v_varDeps_2044_, v_args_2045_, v_body_2046_, v_x_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v_i_2043_);
return v_res_2055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2058_ = lean_unsigned_to_nat(30u);
v___x_2059_ = lean_unsigned_to_nat(254u);
v___x_2060_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_2061_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2062_ = l_mkPanicMessageWithDecl(v___x_2061_, v___x_2060_, v___x_2059_, v___x_2058_, v___x_2057_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_2063_, lean_object* v_args_2064_, lean_object* v_f_2065_, lean_object* v_xs_2066_, lean_object* v_i_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_array_get_size(v_args_2064_);
v___x_2076_ = lean_nat_dec_lt(v_i_2067_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v_i_2067_);
lean_dec_ref(v_args_2064_);
lean_inc_ref(v_xs_2066_);
v___x_2077_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_f_2065_, v_xs_2066_, v_varDeps_2063_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = 1;
v___x_2080_ = l_Lean_Meta_mkLetFVars(v_xs_2066_, v_a_2078_, v___x_2076_, v___x_2076_, v___x_2079_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec_ref(v_xs_2066_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v___x_2082_ = l_Lean_Meta_Sym_shareCommonInc(v_a_2081_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
return v___x_2082_;
}
else
{
return v___x_2080_;
}
}
else
{
lean_dec_ref(v_xs_2066_);
return v___x_2077_;
}
}
else
{
if (lean_obj_tag(v_f_2065_) == 6)
{
lean_object* v_binderName_2083_; lean_object* v_binderType_2084_; lean_object* v_body_2085_; lean_object* v___f_2086_; lean_object* v_varPos_2087_; size_t v_sz_2088_; size_t v___x_2089_; lean_object* v_ys_2090_; lean_object* v___x_2091_; lean_object* v_type_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_binderName_2083_ = lean_ctor_get(v_f_2065_, 0);
lean_inc(v_binderName_2083_);
v_binderType_2084_ = lean_ctor_get(v_f_2065_, 1);
lean_inc_ref(v_binderType_2084_);
v_body_2085_ = lean_ctor_get(v_f_2065_, 2);
lean_inc_ref(v_body_2085_);
lean_dec_ref_known(v_f_2065_, 3);
lean_inc_ref(v_args_2064_);
lean_inc_ref(v_varDeps_2063_);
lean_inc(v_i_2067_);
lean_inc_ref(v_xs_2066_);
v___f_2086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2086_, 0, v_xs_2066_);
lean_closure_set(v___f_2086_, 1, v_i_2067_);
lean_closure_set(v___f_2086_, 2, v_varDeps_2063_);
lean_closure_set(v___f_2086_, 3, v_args_2064_);
lean_closure_set(v___f_2086_, 4, v_body_2085_);
v_varPos_2087_ = lean_array_fget(v_varDeps_2063_, v_i_2067_);
lean_dec_ref(v_varDeps_2063_);
v_sz_2088_ = lean_array_size(v_varPos_2087_);
v___x_2089_ = ((size_t)0ULL);
lean_inc(v_varPos_2087_);
v_ys_2090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_2066_, v_sz_2088_, v___x_2089_, v_varPos_2087_);
lean_dec_ref(v_xs_2066_);
v___x_2091_ = lean_array_get_size(v_varPos_2087_);
lean_dec(v_varPos_2087_);
v_type_2092_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_2084_, v___x_2091_);
v___x_2093_ = lean_array_fget(v_args_2064_, v_i_2067_);
lean_dec(v_i_2067_);
lean_dec_ref(v_args_2064_);
v___x_2094_ = l_Lean_Expr_beta(v___x_2093_, v_ys_2090_);
v___x_2095_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2094_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = 0;
v___x_2098_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_2083_, v_type_2092_, v_a_2096_, v___f_2086_, v___x_2076_, v___x_2097_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
return v___x_2098_;
}
else
{
lean_dec_ref(v_type_2092_);
lean_dec_ref(v___f_2086_);
lean_dec(v_binderName_2083_);
return v___x_2095_;
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_i_2067_);
lean_dec_ref(v_xs_2066_);
lean_dec_ref(v_f_2065_);
lean_dec_ref(v_args_2064_);
lean_dec_ref(v_varDeps_2063_);
v___x_2099_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_2100_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2099_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_2101_, lean_object* v_i_2102_, lean_object* v_varDeps_2103_, lean_object* v_args_2104_, lean_object* v_body_2105_, lean_object* v_x_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Meta_Sym_shareCommonInc(v_x_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = lean_array_push(v_xs_2101_, v_a_2115_);
v___x_2117_ = lean_unsigned_to_nat(1u);
v___x_2118_ = lean_nat_add(v_i_2102_, v___x_2117_);
v___x_2119_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2103_, v_args_2104_, v_body_2105_, v___x_2116_, v___x_2118_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2119_;
}
else
{
lean_dec_ref(v_body_2105_);
lean_dec_ref(v_args_2104_);
lean_dec_ref(v_varDeps_2103_);
lean_dec_ref(v_xs_2101_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_2120_, lean_object* v_args_2121_, lean_object* v_f_2122_, lean_object* v_xs_2123_, lean_object* v_i_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2120_, v_args_2121_, v_f_2122_, v_xs_2123_, v_i_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_2133_, lean_object* v_args_2134_, lean_object* v___h_2135_, lean_object* v_f_2136_, lean_object* v_xs_2137_, lean_object* v_i_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2133_, v_args_2134_, v_f_2136_, v_xs_2137_, v_i_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_2147_, lean_object* v_args_2148_, lean_object* v___h_2149_, lean_object* v_f_2150_, lean_object* v_xs_2151_, lean_object* v_i_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_2147_, v_args_2148_, v___h_2149_, v_f_2150_, v_xs_2151_, v_i_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
return v_res_2160_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2163_ = lean_unsigned_to_nat(40u);
v___x_2164_ = lean_unsigned_to_nat(251u);
v___x_2165_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_2166_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2167_ = l_mkPanicMessageWithDecl(v___x_2166_, v___x_2165_, v___x_2164_, v___x_2163_, v___x_2162_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 5)
{
lean_object* v_fn_2179_; lean_object* v_arg_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_fn_2179_ = lean_ctor_get(v_x_2169_, 0);
lean_inc_ref(v_fn_2179_);
v_arg_2180_ = lean_ctor_get(v_x_2169_, 1);
lean_inc_ref(v_arg_2180_);
lean_dec_ref_known(v_x_2169_, 2);
v___x_2181_ = lean_array_set(v_x_2170_, v_x_2171_, v_arg_2180_);
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_sub(v_x_2171_, v___x_2182_);
lean_dec(v_x_2171_);
v_x_2169_ = v_fn_2179_;
v_x_2170_ = v___x_2181_;
v_x_2171_ = v___x_2183_;
goto _start;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
lean_dec(v_x_2171_);
v___x_2185_ = lean_array_get_size(v_x_2170_);
v___x_2186_ = lean_array_get_size(v_varDeps_2168_);
v___x_2187_ = lean_nat_dec_eq(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec_ref(v_x_2170_);
lean_dec_ref(v_x_2169_);
lean_dec_ref(v_varDeps_2168_);
v___x_2188_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_2189_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v___x_2188_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_2192_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_2168_, v_x_2170_, v_x_2169_, v___x_2191_, v___x_2190_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2193_, v_x_2194_, v_x_2195_, v_x_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_2205_; lean_object* v_dummy_2206_; 
v___x_2205_ = lean_box(0);
v_dummy_2206_ = l_Lean_Expr_sort___override(v___x_2205_);
return v_dummy_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_2207_, lean_object* v_varDeps_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_dummy_2216_; lean_object* v_nargs_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_dummy_2216_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_2217_ = l_Lean_Expr_getAppNumArgs(v_e_2207_);
lean_inc(v_nargs_2217_);
v___x_2218_ = lean_mk_array(v_nargs_2217_, v_dummy_2216_);
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = lean_nat_sub(v_nargs_2217_, v___x_2219_);
lean_dec(v_nargs_2217_);
v___x_2221_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_2208_, v_e_2207_, v___x_2218_, v___x_2220_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_2222_, lean_object* v_varDeps_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_2222_, v_varDeps_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_snd_2235_; lean_object* v_fst_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2269_; 
v_snd_2235_ = lean_ctor_get(v_a_2233_, 1);
v_fst_2236_ = lean_ctor_get(v_a_2233_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_a_2233_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2238_ = v_a_2233_;
v_isShared_2239_ = v_isSharedCheck_2269_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_snd_2235_);
lean_inc(v_fst_2236_);
lean_dec(v_a_2233_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2269_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2268_; 
v_fst_2240_ = lean_ctor_get(v_snd_2235_, 0);
v_snd_2241_ = lean_ctor_get(v_snd_2235_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_snd_2235_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2243_ = v_snd_2235_;
v_isShared_2244_ = v_isSharedCheck_2268_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_inc(v_fst_2240_);
lean_dec(v_snd_2235_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2268_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_lt(v___x_2245_, v_fst_2240_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2248_; 
if (v_isShared_2244_ == 0)
{
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_fst_2240_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_snd_2241_);
v___x_2248_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v___x_2248_);
v___x_2250_ = v___x_2238_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_fst_2236_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_nat_sub(v_fst_2240_, v___x_2255_);
lean_dec(v_fst_2240_);
v___x_2257_ = lean_array_get_borrowed(v___x_2254_, v_argUnivs_2232_, v___x_2256_);
lean_inc(v___x_2257_);
v___x_2258_ = l_Lean_mkLevelIMax_x27(v___x_2257_, v_fst_2236_);
v___x_2259_ = l_Lean_Level_normalize(v___x_2258_);
lean_dec(v___x_2258_);
lean_inc(v___x_2259_);
v___x_2260_ = lean_array_push(v_snd_2241_, v___x_2259_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2260_);
lean_ctor_set(v___x_2243_, 0, v___x_2256_);
v___x_2262_ = v___x_2243_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v___x_2262_);
lean_ctor_set(v___x_2238_, 0, v___x_2259_);
v___x_2264_ = v___x_2238_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
v_a_2233_ = v___x_2264_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2270_, lean_object* v_a_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2270_, v_a_2271_);
lean_dec_ref(v_argUnivs_2270_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2276_, lean_object* v_argUnivs_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
if (lean_obj_tag(v_type_2276_) == 7)
{
lean_object* v_binderType_2285_; lean_object* v_body_2286_; lean_object* v___x_2287_; 
v_binderType_2285_ = lean_ctor_get(v_type_2276_, 1);
lean_inc_ref(v_binderType_2285_);
v_body_2286_ = lean_ctor_get(v_type_2276_, 2);
lean_inc_ref(v_body_2286_);
lean_dec_ref_known(v_type_2276_, 3);
v___x_2287_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2285_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = lean_array_push(v_argUnivs_2277_, v_a_2288_);
v_type_2276_ = v_body_2286_;
v_argUnivs_2277_ = v___x_2289_;
goto _start;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_body_2286_);
lean_dec_ref(v_argUnivs_2277_);
v_a_2291_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2287_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2287_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2276_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = lean_array_get_size(v_argUnivs_2277_);
v___x_2302_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_a_2300_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2277_, v___x_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2324_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2324_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2324_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_snd_2310_; lean_object* v_snd_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2322_; 
v_snd_2310_ = lean_ctor_get(v_a_2306_, 1);
lean_inc(v_snd_2310_);
lean_dec(v_a_2306_);
v_snd_2311_ = lean_ctor_get(v_snd_2310_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_snd_2310_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_snd_2310_, 0);
lean_dec(v_unused_2323_);
v___x_2313_ = v_snd_2310_;
v_isShared_2314_ = v_isSharedCheck_2322_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_snd_2311_);
lean_dec(v_snd_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2322_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = l_Array_reverse___redArg(v_snd_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2315_);
lean_ctor_set(v___x_2313_, 0, v_argUnivs_2277_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_argUnivs_2277_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2317_);
v___x_2319_ = v___x_2308_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_argUnivs_2277_);
v_a_2325_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2305_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2305_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v_argUnivs_2277_);
v_a_2333_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2299_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2299_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2341_, lean_object* v_argUnivs_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2341_, v_argUnivs_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2351_, lean_object* v_inst_2352_, lean_object* v_a_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2351_, v_a_2353_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2362_, lean_object* v_inst_2363_, lean_object* v_a_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2362_, v_inst_2363_, v_a_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v_argUnivs_2362_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2382_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2373_, v___x_2381_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2392_, lean_object* v_argUnivs_2393_, lean_object* v_declName_2394_, lean_object* v_fType_2395_, lean_object* v_i_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v_00_u03b1_2399_; lean_object* v_00_u03b2_2400_; lean_object* v_u_2401_; lean_object* v_v_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2398_ = lean_box(0);
v_00_u03b1_2399_ = l_Lean_Expr_bindingDomain_x21(v_fType_2395_);
v_00_u03b2_2400_ = l_Lean_Expr_bindingBody_x21(v_fType_2395_);
v_u_2401_ = lean_array_get_borrowed(v___x_2398_, v_argUnivs_2393_, v_i_2396_);
v_v_2402_ = lean_array_get_borrowed(v___x_2398_, v_fnUnivs_2392_, v_i_2396_);
v___x_2403_ = lean_box(0);
lean_inc(v_v_2402_);
v___x_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2404_, 0, v_v_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
lean_inc(v_u_2401_);
v___x_2405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_u_2401_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_mkConst(v_declName_2394_, v___x_2405_);
v___x_2407_ = l_Lean_mkAppB(v___x_2406_, v_00_u03b1_2399_, v_00_u03b2_2400_);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2409_, lean_object* v_argUnivs_2410_, lean_object* v_declName_2411_, lean_object* v_fType_2412_, lean_object* v_i_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2409_, v_argUnivs_2410_, v_declName_2411_, v_fType_2412_, v_i_2413_);
lean_dec(v_i_2413_);
lean_dec_ref(v_fType_2412_);
lean_dec_ref(v_argUnivs_2410_);
lean_dec_ref(v_fnUnivs_2409_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2416_, lean_object* v_argUnivs_2417_, lean_object* v_declName_2418_, lean_object* v_fType_2419_, lean_object* v_i_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2416_, v_argUnivs_2417_, v_declName_2418_, v_fType_2419_, v_i_2420_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2429_, lean_object* v_argUnivs_2430_, lean_object* v_declName_2431_, lean_object* v_fType_2432_, lean_object* v_i_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2429_, v_argUnivs_2430_, v_declName_2431_, v_fType_2432_, v_i_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_i_2433_);
lean_dec_ref(v_fType_2432_);
lean_dec_ref(v_argUnivs_2430_);
lean_dec_ref(v_fnUnivs_2429_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2442_, lean_object* v_a_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___y_2452_; lean_object* v___x_2455_; uint8_t v_debug_2456_; 
v___x_2455_ = lean_st_ref_get(v___y_2445_);
v_debug_2456_ = lean_ctor_get_uint8(v___x_2455_, sizeof(void*)*12);
lean_dec(v___x_2455_);
if (v_debug_2456_ == 0)
{
v___y_2452_ = v___y_2445_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2442_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2458_; 
lean_dec_ref_known(v___x_2457_, 1);
v___x_2458_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_dec_ref_known(v___x_2458_, 1);
v___y_2452_ = v___y_2445_;
goto v___jp_2451_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v_a_2443_);
lean_dec_ref(v_f_2442_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v_a_2443_);
lean_dec_ref(v_f_2442_);
v_a_2467_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2457_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2457_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = l_Lean_Expr_app___override(v_f_2442_, v_a_2443_);
v___x_2454_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2453_, v___y_2452_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2475_, lean_object* v_a_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2475_, v_a_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2485_, lean_object* v_a_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2485_, v_a_2486_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2498_, lean_object* v_a_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2498_, v_a_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
return v_res_2510_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___redArg();
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_15220__overap_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15220__overap_2524_ = lean_panic_fn_borrowed(v___x_2523_, v_msg_2512_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
v___x_2525_ = lean_apply_10(v___x_15220__overap_2524_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
return v_res_2537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___x_2549_ = lean_unsigned_to_nat(11u);
v___x_2550_ = lean_unsigned_to_nat(346u);
v___x_2551_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2552_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2_spec__2___closed__1));
v___x_2553_ = l_mkPanicMessageWithDecl(v___x_2552_, v___x_2551_, v___x_2550_, v___x_2549_, v___x_2548_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2554_, lean_object* v_fnUnivs_2555_, lean_object* v_argUnivs_2556_, lean_object* v_simpBody_2557_, lean_object* v_e_2558_, lean_object* v_i_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
switch(lean_obj_tag(v_e_2558_))
{
case 5:
{
lean_object* v_fn_2570_; lean_object* v_arg_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_fn_2570_ = lean_ctor_get(v_e_2558_, 0);
lean_inc_ref_n(v_fn_2570_, 2);
v_arg_2571_ = lean_ctor_get(v_e_2558_, 1);
lean_inc_ref(v_arg_2571_);
lean_dec_ref_known(v_e_2558_, 2);
v___x_2572_ = lean_unsigned_to_nat(1u);
v___x_2573_ = lean_nat_sub(v_i_2559_, v___x_2572_);
v___x_2574_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2554_, v_fnUnivs_2555_, v_argUnivs_2556_, v_simpBody_2557_, v_fn_2570_, v___x_2573_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
lean_dec(v___x_2573_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2695_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2695_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2695_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_fst_2579_; lean_object* v_snd_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2694_; 
v_fst_2579_ = lean_ctor_get(v_a_2575_, 0);
v_snd_2580_ = lean_ctor_get(v_a_2575_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2575_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2582_ = v_a_2575_;
v_isShared_2583_ = v_isSharedCheck_2694_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_snd_2580_);
lean_inc(v_fst_2579_);
lean_dec(v_a_2575_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2694_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_r_2585_; lean_object* v___x_2593_; 
lean_inc(v_a_2568_);
lean_inc_ref(v_a_2567_);
lean_inc(v_a_2566_);
lean_inc_ref(v_a_2565_);
lean_inc(v_a_2564_);
lean_inc_ref(v_a_2563_);
lean_inc(v_a_2562_);
lean_inc_ref(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc_ref(v_arg_2571_);
v___x_2593_ = lean_sym_simp(v_arg_2571_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; uint8_t v___y_2596_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
if (lean_obj_tag(v_fst_2579_) == 0)
{
if (lean_obj_tag(v_a_2594_) == 0)
{
uint8_t v_contextDependent_2598_; 
lean_dec_ref(v_arg_2571_);
lean_dec_ref(v_fn_2570_);
v_contextDependent_2598_ = lean_ctor_get_uint8(v_fst_2579_, 1);
lean_dec_ref_known(v_fst_2579_, 0);
if (v_contextDependent_2598_ == 0)
{
uint8_t v_contextDependent_2599_; 
v_contextDependent_2599_ = lean_ctor_get_uint8(v_a_2594_, 1);
lean_dec_ref_known(v_a_2594_, 0);
v___y_2596_ = v_contextDependent_2599_;
goto v___jp_2595_;
}
else
{
lean_dec_ref_known(v_a_2594_, 0);
v___y_2596_ = v_contextDependent_2598_;
goto v___jp_2595_;
}
}
else
{
uint8_t v_contextDependent_2600_; lean_object* v_e_x27_2601_; lean_object* v_proof_2602_; uint8_t v_contextDependent_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2627_; 
v_contextDependent_2600_ = lean_ctor_get_uint8(v_fst_2579_, 1);
lean_dec_ref_known(v_fst_2579_, 0);
v_e_x27_2601_ = lean_ctor_get(v_a_2594_, 0);
v_proof_2602_ = lean_ctor_get(v_a_2594_, 1);
v_contextDependent_2603_ = lean_ctor_get_uint8(v_a_2594_, sizeof(void*)*2 + 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2605_ = v_a_2594_;
v_isShared_2606_ = v_isSharedCheck_2627_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_proof_2602_);
lean_inc(v_e_x27_2601_);
lean_dec(v_a_2594_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2627_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; 
lean_inc_ref(v_e_x27_2601_);
lean_inc_ref(v_fn_2570_);
v___x_2607_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2570_, v_e_x27_2601_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v_a_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; uint8_t v___y_2615_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2610_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2555_, v_argUnivs_2556_, v___x_2609_, v_snd_2580_, v_i_2559_);
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
v___x_2612_ = l_Lean_mkApp4(v_a_2611_, v_arg_2571_, v_e_x27_2601_, v_fn_2570_, v_proof_2602_);
v___x_2613_ = 0;
if (v_contextDependent_2600_ == 0)
{
v___y_2615_ = v_contextDependent_2603_;
goto v___jp_2614_;
}
else
{
v___y_2615_ = v_contextDependent_2600_;
goto v___jp_2614_;
}
v___jp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 1, v___x_2612_);
lean_ctor_set(v___x_2605_, 0, v_a_2608_);
v___x_2617_ = v___x_2605_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2608_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*2, v___x_2613_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*2 + 1, v___y_2615_);
v_r_2585_ = v___x_2617_;
goto v___jp_2584_;
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_del_object(v___x_2605_);
lean_dec_ref(v_proof_2602_);
lean_dec_ref(v_e_x27_2601_);
lean_del_object(v___x_2582_);
lean_dec(v_snd_2580_);
lean_del_object(v___x_2577_);
lean_dec_ref(v_arg_2571_);
lean_dec_ref(v_fn_2570_);
v_a_2619_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2607_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2607_);
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
}
else
{
if (lean_obj_tag(v_a_2594_) == 0)
{
lean_object* v_e_x27_2628_; lean_object* v_proof_2629_; uint8_t v_contextDependent_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2655_; 
v_e_x27_2628_ = lean_ctor_get(v_fst_2579_, 0);
v_proof_2629_ = lean_ctor_get(v_fst_2579_, 1);
v_contextDependent_2630_ = lean_ctor_get_uint8(v_fst_2579_, sizeof(void*)*2 + 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_fst_2579_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2632_ = v_fst_2579_;
v_isShared_2633_ = v_isSharedCheck_2655_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_proof_2629_);
lean_inc(v_e_x27_2628_);
lean_dec(v_fst_2579_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2655_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
uint8_t v_contextDependent_2634_; lean_object* v___x_2635_; 
v_contextDependent_2634_ = lean_ctor_get_uint8(v_a_2594_, 1);
lean_dec_ref_known(v_a_2594_, 0);
lean_inc_ref(v_arg_2571_);
lean_inc_ref(v_e_x27_2628_);
v___x_2635_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2628_, v_arg_2571_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v_a_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; uint8_t v___y_2643_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2638_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2555_, v_argUnivs_2556_, v___x_2637_, v_snd_2580_, v_i_2559_);
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref(v___x_2638_);
v___x_2640_ = l_Lean_mkApp4(v_a_2639_, v_fn_2570_, v_e_x27_2628_, v_proof_2629_, v_arg_2571_);
v___x_2641_ = 0;
if (v_contextDependent_2630_ == 0)
{
v___y_2643_ = v_contextDependent_2634_;
goto v___jp_2642_;
}
else
{
v___y_2643_ = v_contextDependent_2630_;
goto v___jp_2642_;
}
v___jp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2640_);
lean_ctor_set(v___x_2632_, 0, v_a_2636_);
v___x_2645_ = v___x_2632_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2636_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_ctor_set_uint8(v___x_2645_, sizeof(void*)*2, v___x_2641_);
lean_ctor_set_uint8(v___x_2645_, sizeof(void*)*2 + 1, v___y_2643_);
v_r_2585_ = v___x_2645_;
goto v___jp_2584_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_del_object(v___x_2632_);
lean_dec_ref(v_proof_2629_);
lean_dec_ref(v_e_x27_2628_);
lean_del_object(v___x_2582_);
lean_dec(v_snd_2580_);
lean_del_object(v___x_2577_);
lean_dec_ref(v_arg_2571_);
lean_dec_ref(v_fn_2570_);
v_a_2647_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2635_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2635_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
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
else
{
lean_object* v_e_x27_2656_; lean_object* v_proof_2657_; uint8_t v_contextDependent_2658_; lean_object* v_e_x27_2659_; lean_object* v_proof_2660_; uint8_t v_contextDependent_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2685_; 
v_e_x27_2656_ = lean_ctor_get(v_fst_2579_, 0);
lean_inc_ref(v_e_x27_2656_);
v_proof_2657_ = lean_ctor_get(v_fst_2579_, 1);
lean_inc_ref(v_proof_2657_);
v_contextDependent_2658_ = lean_ctor_get_uint8(v_fst_2579_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2579_, 2);
v_e_x27_2659_ = lean_ctor_get(v_a_2594_, 0);
v_proof_2660_ = lean_ctor_get(v_a_2594_, 1);
v_contextDependent_2661_ = lean_ctor_get_uint8(v_a_2594_, sizeof(void*)*2 + 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2663_ = v_a_2594_;
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_proof_2660_);
lean_inc(v_e_x27_2659_);
lean_dec(v_a_2594_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; 
lean_inc_ref(v_e_x27_2659_);
lean_inc_ref(v_e_x27_2656_);
v___x_2665_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2656_, v_e_x27_2659_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_a_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; uint8_t v___y_2673_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2668_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2555_, v_argUnivs_2556_, v___x_2667_, v_snd_2580_, v_i_2559_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = l_Lean_mkApp6(v_a_2669_, v_fn_2570_, v_e_x27_2656_, v_arg_2571_, v_e_x27_2659_, v_proof_2657_, v_proof_2660_);
v___x_2671_ = 0;
if (v_contextDependent_2658_ == 0)
{
v___y_2673_ = v_contextDependent_2661_;
goto v___jp_2672_;
}
else
{
v___y_2673_ = v_contextDependent_2658_;
goto v___jp_2672_;
}
v___jp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2670_);
lean_ctor_set(v___x_2663_, 0, v_a_2666_);
v___x_2675_ = v___x_2663_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2666_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*2, v___x_2671_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*2 + 1, v___y_2673_);
v_r_2585_ = v___x_2675_;
goto v___jp_2584_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_del_object(v___x_2663_);
lean_dec_ref(v_proof_2660_);
lean_dec_ref(v_e_x27_2659_);
lean_dec_ref(v_proof_2657_);
lean_dec_ref(v_e_x27_2656_);
lean_del_object(v___x_2582_);
lean_dec(v_snd_2580_);
lean_del_object(v___x_2577_);
lean_dec_ref(v_arg_2571_);
lean_dec_ref(v_fn_2570_);
v_a_2677_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2665_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2665_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
}
v___jp_2595_:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2596_);
v_r_2585_ = v___x_2597_;
goto v___jp_2584_;
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_del_object(v___x_2582_);
lean_dec(v_snd_2580_);
lean_dec(v_fst_2579_);
lean_del_object(v___x_2577_);
lean_dec_ref(v_arg_2571_);
lean_dec_ref(v_fn_2570_);
v_a_2686_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2593_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2593_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
v___jp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = l_Lean_Expr_bindingBody_x21(v_snd_2580_);
lean_dec(v_snd_2580_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v___x_2586_);
lean_ctor_set(v___x_2582_, 0, v_r_2585_);
v___x_2588_ = v___x_2582_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_r_2585_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2588_);
v___x_2590_ = v___x_2577_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
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
}
}
else
{
lean_dec_ref(v_arg_2571_);
lean_dec_ref(v_fn_2570_);
return v___x_2574_;
}
}
case 6:
{
lean_object* v___x_2696_; 
lean_inc(v_a_2568_);
lean_inc_ref(v_a_2567_);
lean_inc(v_a_2566_);
lean_inc_ref(v_a_2565_);
lean_inc(v_a_2564_);
lean_inc_ref(v_a_2563_);
lean_inc(v_a_2562_);
lean_inc_ref(v_a_2561_);
lean_inc(v_a_2560_);
v___x_2696_ = lean_apply_11(v_simpBody_2557_, v_e_2558_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, lean_box(0));
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2705_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2705_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2705_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_a_2697_);
lean_ctor_set(v___x_2701_, 1, v_fType_2554_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2701_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_fType_2554_);
v_a_2706_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2696_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2696_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
default: 
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v_e_2558_);
lean_dec_ref(v_simpBody_2557_);
lean_dec_ref(v_fType_2554_);
v___x_2714_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2715_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2714_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2716_, lean_object* v_fnUnivs_2717_, lean_object* v_argUnivs_2718_, lean_object* v_simpBody_2719_, lean_object* v_e_2720_, lean_object* v_i_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2716_, v_fnUnivs_2717_, v_argUnivs_2718_, v_simpBody_2719_, v_e_2720_, v_i_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec(v_i_2721_);
lean_dec_ref(v_argUnivs_2718_);
lean_dec_ref(v_fnUnivs_2717_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2733_, lean_object* v_fType_2734_, lean_object* v_fnUnivs_2735_, lean_object* v_argUnivs_2736_, lean_object* v_simpBody_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_numArgs_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_numArgs_2748_ = lean_array_get_size(v_argUnivs_2736_);
v___x_2749_ = lean_unsigned_to_nat(1u);
v___x_2750_ = lean_nat_sub(v_numArgs_2748_, v___x_2749_);
v___x_2751_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2734_, v_fnUnivs_2735_, v_argUnivs_2736_, v_simpBody_2737_, v_e_2733_, v___x_2750_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
lean_dec(v___x_2750_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_fst_2756_; lean_object* v___x_2758_; 
v_fst_2756_ = lean_ctor_get(v_a_2752_, 0);
lean_inc(v_fst_2756_);
lean_dec(v_a_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_fst_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_fst_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2751_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2751_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2769_, lean_object* v_fType_2770_, lean_object* v_fnUnivs_2771_, lean_object* v_argUnivs_2772_, lean_object* v_simpBody_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2769_, v_fType_2770_, v_fnUnivs_2771_, v_argUnivs_2772_, v_simpBody_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_argUnivs_2772_);
lean_dec_ref(v_fnUnivs_2771_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2789_, lean_object* v_simpBody_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
lean_inc_ref(v_e_2789_);
v___x_2801_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2789_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v_00_u03b1_2803_; lean_object* v_u_2804_; lean_object* v_e_2805_; lean_object* v_h_2806_; lean_object* v_varDeps_2807_; lean_object* v_fType_2808_; lean_object* v___x_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v_00_u03b1_2803_ = lean_ctor_get(v_a_2802_, 0);
lean_inc_ref(v_00_u03b1_2803_);
v_u_2804_ = lean_ctor_get(v_a_2802_, 1);
lean_inc(v_u_2804_);
v_e_2805_ = lean_ctor_get(v_a_2802_, 2);
lean_inc_ref(v_e_2805_);
v_h_2806_ = lean_ctor_get(v_a_2802_, 3);
lean_inc_ref(v_h_2806_);
v_varDeps_2807_ = lean_ctor_get(v_a_2802_, 4);
lean_inc_ref(v_varDeps_2807_);
v_fType_2808_ = lean_ctor_get(v_a_2802_, 5);
lean_inc_ref_n(v_fType_2808_, 2);
lean_dec(v_a_2802_);
v___x_2809_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2808_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_argUnivs_2811_; lean_object* v_fnUnivs_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2880_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v_argUnivs_2811_ = lean_ctor_get(v_a_2810_, 0);
v_fnUnivs_2812_ = lean_ctor_get(v_a_2810_, 1);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_a_2810_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2814_ = v_a_2810_;
v_isShared_2815_ = v_isSharedCheck_2880_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_fnUnivs_2812_);
lean_inc(v_argUnivs_2811_);
lean_dec(v_a_2810_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2880_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; 
lean_inc_ref(v_e_2805_);
v___x_2816_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2805_, v_fType_2808_, v_fnUnivs_2812_, v_argUnivs_2811_, v_simpBody_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec_ref(v_argUnivs_2811_);
lean_dec_ref(v_fnUnivs_2812_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2871_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2871_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2871_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
if (lean_obj_tag(v_a_2817_) == 0)
{
uint8_t v_contextDependent_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_del_object(v___x_2814_);
lean_dec_ref(v_varDeps_2807_);
lean_dec_ref(v_h_2806_);
lean_dec_ref(v_e_2805_);
lean_dec_ref(v_e_2789_);
v_contextDependent_2821_ = lean_ctor_get_uint8(v_a_2817_, 1);
lean_dec_ref_known(v_a_2817_, 0);
v___x_2822_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2821_);
v___x_2823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v_00_u03b1_2803_);
lean_ctor_set(v___x_2823_, 2, v_u_2804_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2823_);
v___x_2825_ = v___x_2819_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
else
{
lean_object* v_e_x27_2827_; lean_object* v_proof_2828_; uint8_t v_contextDependent_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2819_);
v_e_x27_2827_ = lean_ctor_get(v_a_2817_, 0);
v_proof_2828_ = lean_ctor_get(v_a_2817_, 1);
v_contextDependent_2829_ = lean_ctor_get_uint8(v_a_2817_, sizeof(void*)*2 + 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2817_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2831_ = v_a_2817_;
v_isShared_2832_ = v_isSharedCheck_2870_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_proof_2828_);
lean_inc(v_e_x27_2827_);
lean_dec(v_a_2817_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2870_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2833_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2834_ = lean_box(0);
lean_inc(v_u_2804_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 1);
lean_ctor_set(v___x_2814_, 1, v___x_2834_);
lean_ctor_set(v___x_2814_, 0, v_u_2804_);
v___x_2836_ = v___x_2814_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_u_2804_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_inc_ref(v___x_2836_);
v___x_2837_ = l_Lean_mkConst(v___x_2833_, v___x_2836_);
lean_inc_ref_n(v_e_x27_2827_, 2);
lean_inc_ref(v_e_2789_);
lean_inc_ref(v_00_u03b1_2803_);
lean_inc_ref(v___x_2837_);
v___x_2838_ = l_Lean_mkApp6(v___x_2837_, v_00_u03b1_2803_, v_e_2789_, v_e_2805_, v_e_x27_2827_, v_h_2806_, v_proof_2828_);
v___x_2839_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2827_, v_varDeps_2807_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2860_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2860_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2860_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2854_; 
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2836_);
v___x_2845_ = l_Lean_mkConst(v___x_2844_, v___x_2836_);
lean_inc_n(v_a_2840_, 2);
lean_inc_ref_n(v_e_x27_2827_, 2);
lean_inc_ref_n(v_00_u03b1_2803_, 3);
v___x_2846_ = l_Lean_mkApp3(v___x_2845_, v_00_u03b1_2803_, v_e_x27_2827_, v_a_2840_);
v___x_2847_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2848_ = l_Lean_mkConst(v___x_2847_, v___x_2836_);
v___x_2849_ = l_Lean_mkAppB(v___x_2848_, v_00_u03b1_2803_, v_e_x27_2827_);
v___x_2850_ = l_Lean_Meta_mkExpectedPropHint(v___x_2849_, v___x_2846_);
v___x_2851_ = l_Lean_mkApp6(v___x_2837_, v_00_u03b1_2803_, v_e_2789_, v_e_x27_2827_, v_a_2840_, v___x_2838_, v___x_2850_);
v___x_2852_ = 0;
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v___x_2851_);
lean_ctor_set(v___x_2831_, 0, v_a_2840_);
v___x_2854_ = v___x_2831_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2840_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v___x_2851_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*2 + 1, v_contextDependent_2829_);
v___x_2854_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*2, v___x_2852_);
v___x_2855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v_00_u03b1_2803_);
lean_ctor_set(v___x_2855_, 2, v_u_2804_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2855_);
v___x_2857_ = v___x_2842_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v___x_2836_);
lean_del_object(v___x_2831_);
lean_dec_ref(v_e_x27_2827_);
lean_dec(v_u_2804_);
lean_dec_ref(v_00_u03b1_2803_);
lean_dec_ref(v_e_2789_);
v_a_2861_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2839_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2839_);
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
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_del_object(v___x_2814_);
lean_dec_ref(v_varDeps_2807_);
lean_dec_ref(v_h_2806_);
lean_dec_ref(v_e_2805_);
lean_dec(v_u_2804_);
lean_dec_ref(v_00_u03b1_2803_);
lean_dec_ref(v_e_2789_);
v_a_2872_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2816_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2816_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref(v_fType_2808_);
lean_dec_ref(v_varDeps_2807_);
lean_dec_ref(v_h_2806_);
lean_dec_ref(v_e_2805_);
lean_dec(v_u_2804_);
lean_dec_ref(v_00_u03b1_2803_);
lean_dec_ref(v_simpBody_2790_);
lean_dec_ref(v_e_2789_);
v_a_2881_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2809_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2809_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v_simpBody_2790_);
lean_dec_ref(v_e_2789_);
v_a_2889_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2801_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2801_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2897_, lean_object* v_simpBody_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2897_, v_simpBody_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2910_, lean_object* v_simpBody_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2910_, v_simpBody_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_result_2927_; lean_object* v___x_2929_; 
v_result_2927_ = lean_ctor_get(v_a_2923_, 0);
lean_inc_ref(v_result_2927_);
lean_dec(v_a_2923_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v_result_2927_);
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_result_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2922_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2922_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2940_, lean_object* v_simpBody_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2940_, v_simpBody_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2953_, lean_object* v_simpBody_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___x_2965_; 
lean_inc_ref(v_e_u2081_2953_);
v___x_2965_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2953_, v_simpBody_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v_result_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v_result_2967_ = lean_ctor_get(v_a_2966_, 0);
lean_inc_ref(v_result_2967_);
if (lean_obj_tag(v_result_2967_) == 0)
{
lean_object* v_00_u03b1_2968_; lean_object* v_u_2969_; uint8_t v_contextDependent_2970_; lean_object* v___x_2971_; 
v_00_u03b1_2968_ = lean_ctor_get(v_a_2966_, 1);
lean_inc_ref(v_00_u03b1_2968_);
v_u_2969_ = lean_ctor_get(v_a_2966_, 2);
lean_inc(v_u_2969_);
lean_dec(v_a_2966_);
v_contextDependent_2970_ = lean_ctor_get_uint8(v_result_2967_, 1);
lean_dec_ref_known(v_result_2967_, 0);
lean_inc_ref(v_e_u2081_2953_);
v___x_2971_ = l_Lean_Meta_zetaUnused(v_e_u2081_2953_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2992_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2992_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2992_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
size_t v___x_2976_; size_t v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = lean_ptr_addr(v_e_u2081_2953_);
lean_dec_ref(v_e_u2081_2953_);
v___x_2977_ = lean_ptr_addr(v_a_2972_);
v___x_2978_ = lean_usize_dec_eq(v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2979_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_u_2969_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = l_Lean_mkConst(v___x_2979_, v___x_2981_);
lean_inc(v_a_2972_);
v___x_2983_ = l_Lean_mkAppB(v___x_2982_, v_00_u03b1_2968_, v_a_2972_);
v___x_2984_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2984_, 0, v_a_2972_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
lean_ctor_set_uint8(v___x_2984_, sizeof(void*)*2, v___x_2978_);
lean_ctor_set_uint8(v___x_2984_, sizeof(void*)*2 + 1, v_contextDependent_2970_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2984_);
v___x_2986_ = v___x_2974_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
lean_dec(v_a_2972_);
lean_dec(v_u_2969_);
lean_dec_ref(v_00_u03b1_2968_);
v___x_2988_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2970_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2988_);
v___x_2990_ = v___x_2974_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_u_2969_);
lean_dec_ref(v_00_u03b1_2968_);
lean_dec_ref(v_e_u2081_2953_);
v_a_2993_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2971_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2971_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v_00_u03b1_3001_; lean_object* v_u_3002_; lean_object* v_e_x27_3003_; lean_object* v_proof_3004_; uint8_t v_contextDependent_3005_; lean_object* v___x_3006_; 
v_00_u03b1_3001_ = lean_ctor_get(v_a_2966_, 1);
lean_inc_ref(v_00_u03b1_3001_);
v_u_3002_ = lean_ctor_get(v_a_2966_, 2);
lean_inc(v_u_3002_);
lean_dec(v_a_2966_);
v_e_x27_3003_ = lean_ctor_get(v_result_2967_, 0);
v_proof_3004_ = lean_ctor_get(v_result_2967_, 1);
v_contextDependent_3005_ = lean_ctor_get_uint8(v_result_2967_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_3003_);
v___x_3006_ = l_Lean_Meta_zetaUnused(v_e_x27_3003_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3037_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3037_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3037_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
size_t v___x_3011_; size_t v___x_3012_; uint8_t v___x_3013_; 
v___x_3011_ = lean_ptr_addr(v_e_x27_3003_);
v___x_3012_ = lean_ptr_addr(v_a_3007_);
v___x_3013_ = lean_usize_dec_eq(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3031_; 
lean_inc_ref(v_proof_3004_);
lean_inc_ref(v_e_x27_3003_);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_result_2967_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; lean_object* v_unused_3033_; 
v_unused_3032_ = lean_ctor_get(v_result_2967_, 1);
lean_dec(v_unused_3032_);
v_unused_3033_ = lean_ctor_get(v_result_2967_, 0);
lean_dec(v_unused_3033_);
v___x_3015_ = v_result_2967_;
v_isShared_3016_ = v_isSharedCheck_3031_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v_result_2967_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3031_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3017_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_u_3002_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
lean_inc_ref(v___x_3019_);
v___x_3020_ = l_Lean_mkConst(v___x_3017_, v___x_3019_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_3022_ = l_Lean_mkConst(v___x_3021_, v___x_3019_);
lean_inc_n(v_a_3007_, 2);
lean_inc_ref(v_00_u03b1_3001_);
v___x_3023_ = l_Lean_mkAppB(v___x_3022_, v_00_u03b1_3001_, v_a_3007_);
v___x_3024_ = l_Lean_mkApp6(v___x_3020_, v_00_u03b1_3001_, v_e_u2081_2953_, v_e_x27_3003_, v_a_3007_, v_proof_3004_, v___x_3023_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___x_3024_);
lean_ctor_set(v___x_3015_, 0, v_a_3007_);
v___x_3026_ = v___x_3015_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3007_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3024_);
lean_ctor_set_uint8(v_reuseFailAlloc_3030_, sizeof(void*)*2 + 1, v_contextDependent_3005_);
v___x_3026_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*2, v___x_3013_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v___x_3026_);
v___x_3028_ = v___x_3009_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v___x_3035_; 
lean_dec(v_a_3007_);
lean_dec(v_u_3002_);
lean_dec_ref(v_00_u03b1_3001_);
lean_dec_ref(v_e_u2081_2953_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_result_2967_);
v___x_3035_ = v___x_3009_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_result_2967_);
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
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v_u_3002_);
lean_dec_ref_known(v_result_2967_, 2);
lean_dec_ref(v_00_u03b1_3001_);
lean_dec_ref(v_e_u2081_2953_);
v_a_3038_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3006_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3006_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref(v_e_u2081_2953_);
v_a_3046_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_2965_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_2965_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_3054_, lean_object* v_simpBody_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_3054_, v_simpBody_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_3067_, lean_object* v_e_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
uint8_t v___x_3079_; 
v___x_3079_ = l_Lean_Expr_letNondep_x21(v_e_3068_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v_e_3068_);
lean_dec_ref(v_simpBody_3067_);
v___x_3080_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3080_, 0, v___x_3079_);
lean_ctor_set_uint8(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_3068_, v_simpBody_3067_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_3083_, lean_object* v_e_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_3083_, v_e_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_3109_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_3108_, v_e_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
return v_res_3121_;
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
