// Lean compiler output
// Module: Lean.Meta.Transform
// Imports: public import Lean.Meta.FunInfo import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_patternWithRef_x3f(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_visit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_visit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_continue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedTransformStep_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedTransformStep_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedTransformStep_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTransformStep_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedTransformStep_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedTransformStep_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedTransformStep_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedTransformStep_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTransformStep_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedTransformStep_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTransformStep_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTransformStep_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTransformStep;
static const lean_string_object l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprTransformStep_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.TransformStep.done"};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__0 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprTransformStep_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprTransformStep_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__1 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprTransformStep_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprTransformStep_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__2 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__2_value;
static lean_once_cell_t l_Lean_instReprTransformStep_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprTransformStep_repr___closed__3;
static lean_once_cell_t l_Lean_instReprTransformStep_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprTransformStep_repr___closed__4;
static const lean_string_object l_Lean_instReprTransformStep_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.TransformStep.visit"};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__5 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprTransformStep_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprTransformStep_repr___closed__5_value)}};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__6 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprTransformStep_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprTransformStep_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__7 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__7_value;
static const lean_string_object l_Lean_instReprTransformStep_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.TransformStep.continue"};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__8 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__8_value;
static const lean_ctor_object l_Lean_instReprTransformStep_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprTransformStep_repr___closed__8_value)}};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__9 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__9_value;
static const lean_ctor_object l_Lean_instReprTransformStep_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprTransformStep_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprTransformStep_repr___closed__10 = (const lean_object*)&l_Lean_instReprTransformStep_repr___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_instReprTransformStep_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprTransformStep_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprTransformStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprTransformStep_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprTransformStep___closed__0 = (const lean_object*)&l_Lean_instReprTransformStep___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprTransformStep = (const lean_object*)&l_Lean_instReprTransformStep___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___redArg___closed__0;
static lean_once_cell_t l_Lean_Core_transform___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___redArg___closed__1;
static lean_once_cell_t l_Lean_Core_transform___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Core_betaReduce___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Core_betaReduce___lam__0___closed__0 = (const lean_object*)&l_Lean_Core_betaReduce___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_betaReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_betaReduce___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_betaReduce___closed__0 = (const lean_object*)&l_Lean_Core_betaReduce___closed__0_value;
static const lean_closure_object l_Lean_Core_betaReduce___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_betaReduce___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_betaReduce___closed__1 = (const lean_object*)&l_Lean_Core_betaReduce___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object**);
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_zetaReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_zetaReduce___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_zetaReduce___closed__0 = (const lean_object*)&l_Lean_Meta_zetaReduce___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_eraseInaccessibleAnnotations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___closed__0 = (const lean_object*)&l_Lean_Meta_eraseInaccessibleAnnotations___closed__0_value;
static const lean_closure_object l_Lean_Meta_eraseInaccessibleAnnotations___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___closed__1 = (const lean_object*)&l_Lean_Meta_eraseInaccessibleAnnotations___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_erasePatternRefAnnotations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_erasePatternRefAnnotations___closed__0 = (const lean_object*)&l_Lean_Meta_erasePatternRefAnnotations___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_TransformStep_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
lean_object* v_e_x3f_9_; lean_object* v___x_10_; 
v_e_x3f_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_e_x3f_9_);
lean_dec_ref(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_e_x3f_9_);
return v___x_10_;
}
else
{
lean_object* v_e_11_; lean_object* v___x_12_; 
v_e_11_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_e_11_);
lean_dec_ref(v_t_7_);
v___x_12_ = lean_apply_1(v_k_8_, v_e_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_TransformStep_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_TransformStep_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_done_elim___redArg(lean_object* v_t_25_, lean_object* v_done_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_TransformStep_ctorElim___redArg(v_t_25_, v_done_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_done_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_done_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_TransformStep_ctorElim___redArg(v_t_29_, v_done_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_visit_elim___redArg(lean_object* v_t_33_, lean_object* v_visit_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_TransformStep_ctorElim___redArg(v_t_33_, v_visit_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_visit_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_visit_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_TransformStep_ctorElim___redArg(v_t_37_, v_visit_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_continue_elim___redArg(lean_object* v_t_41_, lean_object* v_continue_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_TransformStep_ctorElim___redArg(v_t_41_, v_continue_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_continue_elim(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_continue_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_TransformStep_ctorElim___redArg(v_t_45_, v_continue_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep_default___closed__2(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
v___x_53_ = ((lean_object*)(l_Lean_instInhabitedTransformStep_default___closed__1));
v___x_54_ = l_Lean_Expr_const___override(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep_default___closed__3(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_Lean_instInhabitedTransformStep_default___closed__2, &l_Lean_instInhabitedTransformStep_default___closed__2_once, _init_l_Lean_instInhabitedTransformStep_default___closed__2);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep_default(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Lean_instInhabitedTransformStep_default___closed__3, &l_Lean_instInhabitedTransformStep_default___closed__3_once, _init_l_Lean_instInhabitedTransformStep_default___closed__3);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_instInhabitedTransformStep_default;
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_67_; 
v___x_67_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1));
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_val_68_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_val_68_);
lean_dec_ref(v_x_65_);
v___x_69_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3));
v___x_70_ = lean_unsigned_to_nat(1024u);
v___x_71_ = l_Lean_instReprExpr_repr(v_val_68_, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_x_66_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___boxed(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(v_x_74_, v_x_75_);
lean_dec(v_x_75_);
return v_res_76_;
}
}
static lean_object* _init_l_Lean_instReprTransformStep_repr___closed__3(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(2u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_instReprTransformStep_repr___closed__4(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTransformStep_repr(lean_object* v_x_99_, lean_object* v_prec_100_){
_start:
{
switch(lean_obj_tag(v_x_99_))
{
case 0:
{
lean_object* v_e_101_; lean_object* v___y_103_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_e_101_ = lean_ctor_get(v_x_99_, 0);
lean_inc_ref(v_e_101_);
lean_dec_ref(v_x_99_);
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = lean_nat_dec_le(v___x_112_, v_prec_100_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__3, &l_Lean_instReprTransformStep_repr___closed__3_once, _init_l_Lean_instReprTransformStep_repr___closed__3);
v___y_103_ = v___x_114_;
goto v___jp_102_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__4, &l_Lean_instReprTransformStep_repr___closed__4_once, _init_l_Lean_instReprTransformStep_repr___closed__4);
v___y_103_ = v___x_115_;
goto v___jp_102_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_104_ = ((lean_object*)(l_Lean_instReprTransformStep_repr___closed__2));
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = l_Lean_instReprExpr_repr(v_e_101_, v___x_105_);
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
lean_inc(v___y_103_);
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v___y_103_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
v___x_111_ = l_Repr_addAppParen(v___x_110_, v_prec_100_);
return v___x_111_;
}
}
case 1:
{
lean_object* v_e_116_; lean_object* v___y_118_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_e_116_ = lean_ctor_get(v_x_99_, 0);
lean_inc_ref(v_e_116_);
lean_dec_ref(v_x_99_);
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_100_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__3, &l_Lean_instReprTransformStep_repr___closed__3_once, _init_l_Lean_instReprTransformStep_repr___closed__3);
v___y_118_ = v___x_129_;
goto v___jp_117_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__4, &l_Lean_instReprTransformStep_repr___closed__4_once, _init_l_Lean_instReprTransformStep_repr___closed__4);
v___y_118_ = v___x_130_;
goto v___jp_117_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_119_ = ((lean_object*)(l_Lean_instReprTransformStep_repr___closed__7));
v___x_120_ = lean_unsigned_to_nat(1024u);
v___x_121_ = l_Lean_instReprExpr_repr(v_e_116_, v___x_120_);
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
lean_inc(v___y_118_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_118_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_100_);
return v___x_126_;
}
}
default: 
{
lean_object* v_e_x3f_131_; lean_object* v___y_133_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_e_x3f_131_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_e_x3f_131_);
lean_dec_ref(v_x_99_);
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_100_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__3, &l_Lean_instReprTransformStep_repr___closed__3_once, _init_l_Lean_instReprTransformStep_repr___closed__3);
v___y_133_ = v___x_144_;
goto v___jp_132_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__4, &l_Lean_instReprTransformStep_repr___closed__4_once, _init_l_Lean_instReprTransformStep_repr___closed__4);
v___y_133_ = v___x_145_;
goto v___jp_132_;
}
v___jp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_134_ = ((lean_object*)(l_Lean_instReprTransformStep_repr___closed__10));
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(v_e_x3f_131_, v___x_135_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_134_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
lean_inc(v___y_133_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_133_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_100_);
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTransformStep_repr___boxed(lean_object* v_x_146_, lean_object* v_prec_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_instReprTransformStep_repr(v_x_146_, v_prec_147_);
lean_dec(v_prec_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(lean_object* v_toApplicative_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_toPure_154_; lean_object* v___x_155_; 
v_toPure_154_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_inc(v_toPure_154_);
lean_dec_ref(v_toApplicative_151_);
v___x_155_ = lean_apply_2(v_toPure_154_, lean_box(0), v_a_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1(lean_object* v___x_156_, lean_object* v___x_157_, lean_object* v_e_158_, lean_object* v_a_159_, lean_object* v_s_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
v___x_162_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_156_, v___x_157_, v_s_160_, v_e_158_, v_a_159_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(lean_object* v_toApplicative_164_, lean_object* v___x_165_, lean_object* v___x_166_, lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_x_169_, lean_object* v_toBind_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_inc_ref(v_a_171_);
v___f_172_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_172_, 0, v_toApplicative_164_);
lean_closure_set(v___f_172_, 1, v_a_171_);
v___f_173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_173_, 0, v___x_165_);
lean_closure_set(v___f_173_, 1, v___x_166_);
lean_closure_set(v___f_173_, 2, v_e_167_);
lean_closure_set(v___f_173_, 3, v_a_171_);
lean_inc(v_a_168_);
v___x_174_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_174_, 0, lean_box(0));
lean_closure_set(v___x_174_, 1, lean_box(0));
lean_closure_set(v___x_174_, 2, lean_box(0));
lean_closure_set(v___x_174_, 3, v_a_168_);
lean_closure_set(v___x_174_, 4, v___f_173_);
v___x_175_ = lean_apply_2(v_x_169_, lean_box(0), v___x_174_);
v___x_176_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_175_, v___f_172_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_x_182_, lean_object* v_toBind_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(v_toApplicative_177_, v___x_178_, v___x_179_, v_e_180_, v_a_181_, v_x_182_, v_toBind_183_, v_a_184_);
lean_dec(v_a_181_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object* v_toApplicative_186_, lean_object* v___x_187_, lean_object* v___x_188_, lean_object* v_e_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_toPure_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_toPure_191_ = lean_ctor_get(v_toApplicative_186_, 1);
lean_inc(v_toPure_191_);
lean_dec_ref(v_toApplicative_186_);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_187_, v___x_188_, v_a_190_, v_e_189_);
v___x_193_ = lean_apply_2(v_toPure_191_, lean_box(0), v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_194_, lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v_e_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(v_toApplicative_194_, v___x_195_, v___x_196_, v_e_197_, v_a_198_);
lean_dec_ref(v_a_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_pre_200_, lean_object* v_e_201_, lean_object* v_x_202_, lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v_inst_205_, lean_object* v___f_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, lean_object* v_toBind_210_, lean_object* v___f_211_, lean_object* v_toApplicative_212_, lean_object* v_a_213_){
_start:
{
if (lean_obj_tag(v_a_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_2135__overap_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec_ref(v_toApplicative_212_);
v___x_214_ = lean_apply_1(v_pre_200_, v_e_201_);
lean_inc_ref(v___x_204_);
lean_inc_ref(v___x_203_);
v___x_215_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_215_, 0, lean_box(0));
lean_closure_set(v___x_215_, 1, lean_box(0));
lean_closure_set(v___x_215_, 2, lean_box(0));
lean_closure_set(v___x_215_, 3, lean_box(0));
lean_closure_set(v___x_215_, 4, v_x_202_);
lean_closure_set(v___x_215_, 5, v___x_203_);
lean_closure_set(v___x_215_, 6, v___x_204_);
lean_closure_set(v___x_215_, 7, lean_box(0));
lean_closure_set(v___x_215_, 8, v___x_214_);
v___x_216_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_216_, 0, lean_box(0));
lean_closure_set(v___x_216_, 1, lean_box(0));
lean_closure_set(v___x_216_, 2, lean_box(0));
lean_closure_set(v___x_216_, 3, lean_box(0));
lean_closure_set(v___x_216_, 4, v_x_202_);
lean_closure_set(v___x_216_, 5, v___x_203_);
lean_closure_set(v___x_216_, 6, v___x_204_);
lean_closure_set(v___x_216_, 7, v_inst_205_);
lean_closure_set(v___x_216_, 8, lean_box(0));
lean_closure_set(v___x_216_, 9, lean_box(0));
lean_closure_set(v___x_216_, 10, v___x_215_);
lean_closure_set(v___x_216_, 11, v___f_206_);
v___x_2135__overap_217_ = l_Lean_Core_withIncRecDepth___redArg(v___x_207_, v___x_208_, v___x_216_);
lean_inc(v_a_209_);
v___x_218_ = lean_apply_1(v___x_2135__overap_217_, v_a_209_);
v___x_219_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v___x_218_, v___f_211_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; lean_object* v_toPure_221_; lean_object* v___x_222_; 
lean_dec(v___f_211_);
lean_dec(v_toBind_210_);
lean_dec_ref(v___x_208_);
lean_dec_ref(v___x_207_);
lean_dec(v___f_206_);
lean_dec_ref(v_inst_205_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v___x_203_);
lean_dec_ref(v_e_201_);
lean_dec(v_pre_200_);
v_val_220_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_val_220_);
lean_dec_ref(v_a_213_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_212_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_212_);
v___x_222_ = lean_apply_2(v_toPure_221_, lean_box(0), v_val_220_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object* v_pre_223_, lean_object* v_e_224_, lean_object* v_x_225_, lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v_inst_228_, lean_object* v___f_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_a_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v_toApplicative_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(v_pre_223_, v_e_224_, v_x_225_, v___x_226_, v___x_227_, v_inst_228_, v___f_229_, v___x_230_, v___x_231_, v_a_232_, v_toBind_233_, v___f_234_, v_toApplicative_235_, v_a_236_);
lean_dec(v_a_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object* v_a_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_pre_243_, lean_object* v_post_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = l_Lean_mkAppN(v_a_240_, v_a_248_);
v___x_250_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_241_, v_inst_242_, v_pre_243_, v_post_244_, v_x_245_, v_x_246_, v___x_249_, v___y_247_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object* v_a_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_pre_254_, lean_object* v_post_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v___y_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(v_a_251_, v_inst_252_, v_inst_253_, v_pre_254_, v_post_255_, v_x_256_, v_x_257_, v___y_258_, v_a_259_);
lean_dec_ref(v_a_259_);
lean_dec(v___y_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_pre_263_, lean_object* v_post_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_e_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_261_, v_inst_262_, v_pre_263_, v_post_264_, v_x_265_, v_x_266_, v_e_267_, v_a_268_);
lean_dec(v_a_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_pre_272_, lean_object* v_post_273_, lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v_args_277_, lean_object* v___x_278_, lean_object* v_toBind_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___f_281_; lean_object* v___x_282_; size_t v_sz_283_; size_t v___x_284_; lean_object* v___x_1891__overap_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_n(v___y_276_, 2);
lean_inc(v_x_275_);
lean_inc(v_post_273_);
lean_inc(v_pre_272_);
lean_inc_ref(v_inst_271_);
lean_inc_ref(v_inst_270_);
v___f_281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_281_, 0, v_a_280_);
lean_closure_set(v___f_281_, 1, v_inst_270_);
lean_closure_set(v___f_281_, 2, v_inst_271_);
lean_closure_set(v___f_281_, 3, v_pre_272_);
lean_closure_set(v___f_281_, 4, v_post_273_);
lean_closure_set(v___f_281_, 5, v_x_274_);
lean_closure_set(v___f_281_, 6, v_x_275_);
lean_closure_set(v___f_281_, 7, v___y_276_);
v___x_282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed), 8, 6);
lean_closure_set(v___x_282_, 0, v_inst_270_);
lean_closure_set(v___x_282_, 1, v_inst_271_);
lean_closure_set(v___x_282_, 2, v_pre_272_);
lean_closure_set(v___x_282_, 3, v_post_273_);
lean_closure_set(v___x_282_, 4, v_x_274_);
lean_closure_set(v___x_282_, 5, v_x_275_);
v_sz_283_ = lean_array_size(v_args_277_);
v___x_284_ = ((size_t)0ULL);
v___x_1891__overap_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_278_, v___x_282_, v_sz_283_, v___x_284_, v_args_277_);
v___x_286_ = lean_apply_1(v___x_1891__overap_285_, v___y_276_);
v___x_287_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v___x_286_, v___f_281_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_pre_290_, lean_object* v_post_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v___y_294_, lean_object* v_args_295_, lean_object* v___x_296_, lean_object* v_toBind_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(v_inst_288_, v_inst_289_, v_pre_290_, v_post_291_, v_x_292_, v_x_293_, v___y_294_, v_args_295_, v___x_296_, v_toBind_297_, v_a_298_);
lean_dec(v___y_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_pre_302_, lean_object* v_post_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v___x_306_, lean_object* v_toBind_307_, lean_object* v_f_308_, lean_object* v_args_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc(v_toBind_307_);
lean_inc(v___y_310_);
lean_inc(v_x_305_);
lean_inc(v_post_303_);
lean_inc(v_pre_302_);
lean_inc_ref(v_inst_301_);
lean_inc_ref(v_inst_300_);
v___f_311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_311_, 0, v_inst_300_);
lean_closure_set(v___f_311_, 1, v_inst_301_);
lean_closure_set(v___f_311_, 2, v_pre_302_);
lean_closure_set(v___f_311_, 3, v_post_303_);
lean_closure_set(v___f_311_, 4, v_x_304_);
lean_closure_set(v___f_311_, 5, v_x_305_);
lean_closure_set(v___f_311_, 6, v___y_310_);
lean_closure_set(v___f_311_, 7, v_args_309_);
lean_closure_set(v___f_311_, 8, v___x_306_);
lean_closure_set(v___f_311_, 9, v_toBind_307_);
v___x_312_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_300_, v_inst_301_, v_pre_302_, v_post_303_, v_x_304_, v_x_305_, v_f_308_, v___y_310_);
v___x_313_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_312_, v___f_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_pre_316_, lean_object* v_post_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v___x_320_, lean_object* v_toBind_321_, lean_object* v_f_322_, lean_object* v_args_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(v_inst_314_, v_inst_315_, v_pre_316_, v_post_317_, v_x_318_, v_x_319_, v___x_320_, v_toBind_321_, v_f_322_, v_args_323_, v___y_324_);
lean_dec(v___y_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderName_326_, lean_object* v_a_327_, uint8_t v_binderInfo_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_pre_331_, lean_object* v_post_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v_binderType_337_, lean_object* v_body_338_, lean_object* v_a_339_){
_start:
{
uint8_t v___y_341_; size_t v___x_348_; size_t v___x_349_; uint8_t v___x_350_; 
v___x_348_ = lean_ptr_addr(v_binderType_337_);
v___x_349_ = lean_ptr_addr(v_a_327_);
v___x_350_ = lean_usize_dec_eq(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
v___y_341_ = v___x_350_;
goto v___jp_340_;
}
else
{
size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_ptr_addr(v_body_338_);
v___x_352_ = lean_ptr_addr(v_a_339_);
v___x_353_ = lean_usize_dec_eq(v___x_351_, v___x_352_);
v___y_341_ = v___x_353_;
goto v___jp_340_;
}
v___jp_340_:
{
if (v___y_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec_ref(v___y_336_);
v___x_342_ = l_Lean_Expr_forallE___override(v_binderName_326_, v_a_327_, v_a_339_, v_binderInfo_328_);
v___x_343_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_329_, v_inst_330_, v_pre_331_, v_post_332_, v_x_333_, v_x_334_, v___x_342_, v___y_335_);
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_328_, v_binderInfo_328_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v___y_336_);
v___x_345_ = l_Lean_Expr_forallE___override(v_binderName_326_, v_a_327_, v_a_339_, v_binderInfo_328_);
v___x_346_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_329_, v_inst_330_, v_pre_331_, v_post_332_, v_x_333_, v_x_334_, v___x_345_, v___y_335_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
lean_dec_ref(v_a_339_);
lean_dec_ref(v_a_327_);
lean_dec(v_binderName_326_);
v___x_347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_329_, v_inst_330_, v_pre_331_, v_post_332_, v_x_333_, v_x_334_, v___y_336_, v___y_335_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderName_354_, lean_object* v_a_355_, lean_object* v_binderInfo_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_pre_359_, lean_object* v_post_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v_binderType_365_, lean_object* v_body_366_, lean_object* v_a_367_){
_start:
{
uint8_t v_binderInfo_2417__boxed_368_; lean_object* v_res_369_; 
v_binderInfo_2417__boxed_368_ = lean_unbox(v_binderInfo_356_);
v_res_369_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderName_354_, v_a_355_, v_binderInfo_2417__boxed_368_, v_inst_357_, v_inst_358_, v_pre_359_, v_post_360_, v_x_361_, v_x_362_, v___y_363_, v___y_364_, v_binderType_365_, v_body_366_, v_a_367_);
lean_dec_ref(v_body_366_);
lean_dec_ref(v_binderType_365_);
lean_dec(v___y_363_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderName_370_, uint8_t v_binderInfo_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_pre_374_, lean_object* v_post_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v_binderType_380_, lean_object* v_body_381_, lean_object* v_toBind_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_box(v_binderInfo_371_);
lean_inc_ref(v_body_381_);
lean_inc(v___y_378_);
lean_inc(v_x_377_);
lean_inc(v_post_375_);
lean_inc(v_pre_374_);
lean_inc_ref(v_inst_373_);
lean_inc_ref(v_inst_372_);
v___f_385_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 14, 13);
lean_closure_set(v___f_385_, 0, v_binderName_370_);
lean_closure_set(v___f_385_, 1, v_a_383_);
lean_closure_set(v___f_385_, 2, v___x_384_);
lean_closure_set(v___f_385_, 3, v_inst_372_);
lean_closure_set(v___f_385_, 4, v_inst_373_);
lean_closure_set(v___f_385_, 5, v_pre_374_);
lean_closure_set(v___f_385_, 6, v_post_375_);
lean_closure_set(v___f_385_, 7, v_x_376_);
lean_closure_set(v___f_385_, 8, v_x_377_);
lean_closure_set(v___f_385_, 9, v___y_378_);
lean_closure_set(v___f_385_, 10, v___y_379_);
lean_closure_set(v___f_385_, 11, v_binderType_380_);
lean_closure_set(v___f_385_, 12, v_body_381_);
v___x_386_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_372_, v_inst_373_, v_pre_374_, v_post_375_, v_x_376_, v_x_377_, v_body_381_, v___y_378_);
v___x_387_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_386_, v___f_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderName_388_, lean_object* v_binderInfo_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_pre_392_, lean_object* v_post_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v_binderType_398_, lean_object* v_body_399_, lean_object* v_toBind_400_, lean_object* v_a_401_){
_start:
{
uint8_t v_binderInfo_2298__boxed_402_; lean_object* v_res_403_; 
v_binderInfo_2298__boxed_402_ = lean_unbox(v_binderInfo_389_);
v_res_403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderName_388_, v_binderInfo_2298__boxed_402_, v_inst_390_, v_inst_391_, v_pre_392_, v_post_393_, v_x_394_, v_x_395_, v___y_396_, v___y_397_, v_binderType_398_, v_body_399_, v_toBind_400_, v_a_401_);
lean_dec(v___y_396_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderName_404_, lean_object* v_a_405_, uint8_t v_binderInfo_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_pre_409_, lean_object* v_post_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v_binderType_415_, lean_object* v_body_416_, lean_object* v_a_417_){
_start:
{
uint8_t v___y_419_; size_t v___x_426_; size_t v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_ptr_addr(v_binderType_415_);
v___x_427_ = lean_ptr_addr(v_a_405_);
v___x_428_ = lean_usize_dec_eq(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
v___y_419_ = v___x_428_;
goto v___jp_418_;
}
else
{
size_t v___x_429_; size_t v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_ptr_addr(v_body_416_);
v___x_430_ = lean_ptr_addr(v_a_417_);
v___x_431_ = lean_usize_dec_eq(v___x_429_, v___x_430_);
v___y_419_ = v___x_431_;
goto v___jp_418_;
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v___y_414_);
v___x_420_ = l_Lean_Expr_lam___override(v_binderName_404_, v_a_405_, v_a_417_, v_binderInfo_406_);
v___x_421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_407_, v_inst_408_, v_pre_409_, v_post_410_, v_x_411_, v_x_412_, v___x_420_, v___y_413_);
return v___x_421_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_406_, v_binderInfo_406_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v___y_414_);
v___x_423_ = l_Lean_Expr_lam___override(v_binderName_404_, v_a_405_, v_a_417_, v_binderInfo_406_);
v___x_424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_407_, v_inst_408_, v_pre_409_, v_post_410_, v_x_411_, v_x_412_, v___x_423_, v___y_413_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; 
lean_dec_ref(v_a_417_);
lean_dec_ref(v_a_405_);
lean_dec(v_binderName_404_);
v___x_425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_407_, v_inst_408_, v_pre_409_, v_post_410_, v_x_411_, v_x_412_, v___y_414_, v___y_413_);
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderName_432_, lean_object* v_a_433_, lean_object* v_binderInfo_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_pre_437_, lean_object* v_post_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v_binderType_443_, lean_object* v_body_444_, lean_object* v_a_445_){
_start:
{
uint8_t v_binderInfo_2393__boxed_446_; lean_object* v_res_447_; 
v_binderInfo_2393__boxed_446_ = lean_unbox(v_binderInfo_434_);
v_res_447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderName_432_, v_a_433_, v_binderInfo_2393__boxed_446_, v_inst_435_, v_inst_436_, v_pre_437_, v_post_438_, v_x_439_, v_x_440_, v___y_441_, v___y_442_, v_binderType_443_, v_body_444_, v_a_445_);
lean_dec_ref(v_body_444_);
lean_dec_ref(v_binderType_443_);
lean_dec(v___y_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderName_448_, uint8_t v_binderInfo_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_pre_452_, lean_object* v_post_453_, lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v_binderType_458_, lean_object* v_body_459_, lean_object* v_toBind_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_box(v_binderInfo_449_);
lean_inc_ref(v_body_459_);
lean_inc(v___y_456_);
lean_inc(v_x_455_);
lean_inc(v_post_453_);
lean_inc(v_pre_452_);
lean_inc_ref(v_inst_451_);
lean_inc_ref(v_inst_450_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 14, 13);
lean_closure_set(v___f_463_, 0, v_binderName_448_);
lean_closure_set(v___f_463_, 1, v_a_461_);
lean_closure_set(v___f_463_, 2, v___x_462_);
lean_closure_set(v___f_463_, 3, v_inst_450_);
lean_closure_set(v___f_463_, 4, v_inst_451_);
lean_closure_set(v___f_463_, 5, v_pre_452_);
lean_closure_set(v___f_463_, 6, v_post_453_);
lean_closure_set(v___f_463_, 7, v_x_454_);
lean_closure_set(v___f_463_, 8, v_x_455_);
lean_closure_set(v___f_463_, 9, v___y_456_);
lean_closure_set(v___f_463_, 10, v___y_457_);
lean_closure_set(v___f_463_, 11, v_binderType_458_);
lean_closure_set(v___f_463_, 12, v_body_459_);
v___x_464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_450_, v_inst_451_, v_pre_452_, v_post_453_, v_x_454_, v_x_455_, v_body_459_, v___y_456_);
v___x_465_ = lean_apply_4(v_toBind_460_, lean_box(0), lean_box(0), v___x_464_, v___f_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderName_466_, lean_object* v_binderInfo_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_pre_470_, lean_object* v_post_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v_binderType_476_, lean_object* v_body_477_, lean_object* v_toBind_478_, lean_object* v_a_479_){
_start:
{
uint8_t v_binderInfo_2248__boxed_480_; lean_object* v_res_481_; 
v_binderInfo_2248__boxed_480_ = lean_unbox(v_binderInfo_467_);
v_res_481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderName_466_, v_binderInfo_2248__boxed_480_, v_inst_468_, v_inst_469_, v_pre_470_, v_post_471_, v_x_472_, v_x_473_, v___y_474_, v___y_475_, v_binderType_476_, v_body_477_, v_toBind_478_, v_a_479_);
lean_dec(v___y_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_declName_482_, lean_object* v_a_483_, lean_object* v_a_484_, uint8_t v_nondep_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_pre_488_, lean_object* v_post_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v_body_493_, lean_object* v___y_494_, lean_object* v_type_495_, lean_object* v_value_496_, lean_object* v_a_497_){
_start:
{
uint8_t v___y_499_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_ptr_addr(v_type_495_);
v___x_509_ = lean_ptr_addr(v_a_483_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
v___y_499_ = v___x_510_;
goto v___jp_498_;
}
else
{
size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_ptr_addr(v_value_496_);
v___x_512_ = lean_ptr_addr(v_a_484_);
v___x_513_ = lean_usize_dec_eq(v___x_511_, v___x_512_);
v___y_499_ = v___x_513_;
goto v___jp_498_;
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v___y_494_);
v___x_500_ = l_Lean_Expr_letE___override(v_declName_482_, v_a_483_, v_a_484_, v_a_497_, v_nondep_485_);
v___x_501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_486_, v_inst_487_, v_pre_488_, v_post_489_, v_x_490_, v_x_491_, v___x_500_, v___y_492_);
return v___x_501_;
}
else
{
size_t v___x_502_; size_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_ptr_addr(v_body_493_);
v___x_503_ = lean_ptr_addr(v_a_497_);
v___x_504_ = lean_usize_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec_ref(v___y_494_);
v___x_505_ = l_Lean_Expr_letE___override(v_declName_482_, v_a_483_, v_a_484_, v_a_497_, v_nondep_485_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_486_, v_inst_487_, v_pre_488_, v_post_489_, v_x_490_, v_x_491_, v___x_505_, v___y_492_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_dec_ref(v_a_497_);
lean_dec_ref(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_declName_482_);
v___x_507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_486_, v_inst_487_, v_pre_488_, v_post_489_, v_x_490_, v_x_491_, v___y_494_, v___y_492_);
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object* v_declName_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_nondep_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_pre_520_, lean_object* v_post_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v_body_525_, lean_object* v___y_526_, lean_object* v_type_527_, lean_object* v_value_528_, lean_object* v_a_529_){
_start:
{
uint8_t v_nondep_2441__boxed_530_; lean_object* v_res_531_; 
v_nondep_2441__boxed_530_ = lean_unbox(v_nondep_517_);
v_res_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_declName_514_, v_a_515_, v_a_516_, v_nondep_2441__boxed_530_, v_inst_518_, v_inst_519_, v_pre_520_, v_post_521_, v_x_522_, v_x_523_, v___y_524_, v_body_525_, v___y_526_, v_type_527_, v_value_528_, v_a_529_);
lean_dec_ref(v_value_528_);
lean_dec_ref(v_type_527_);
lean_dec_ref(v_body_525_);
lean_dec(v___y_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_declName_532_, lean_object* v_a_533_, uint8_t v_nondep_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_pre_537_, lean_object* v_post_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v_body_542_, lean_object* v___y_543_, lean_object* v_type_544_, lean_object* v_value_545_, lean_object* v_toBind_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = lean_box(v_nondep_534_);
lean_inc_ref(v_body_542_);
lean_inc(v___y_541_);
lean_inc(v_x_540_);
lean_inc(v_post_538_);
lean_inc(v_pre_537_);
lean_inc_ref(v_inst_536_);
lean_inc_ref(v_inst_535_);
v___f_549_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 16, 15);
lean_closure_set(v___f_549_, 0, v_declName_532_);
lean_closure_set(v___f_549_, 1, v_a_533_);
lean_closure_set(v___f_549_, 2, v_a_547_);
lean_closure_set(v___f_549_, 3, v___x_548_);
lean_closure_set(v___f_549_, 4, v_inst_535_);
lean_closure_set(v___f_549_, 5, v_inst_536_);
lean_closure_set(v___f_549_, 6, v_pre_537_);
lean_closure_set(v___f_549_, 7, v_post_538_);
lean_closure_set(v___f_549_, 8, v_x_539_);
lean_closure_set(v___f_549_, 9, v_x_540_);
lean_closure_set(v___f_549_, 10, v___y_541_);
lean_closure_set(v___f_549_, 11, v_body_542_);
lean_closure_set(v___f_549_, 12, v___y_543_);
lean_closure_set(v___f_549_, 13, v_type_544_);
lean_closure_set(v___f_549_, 14, v_value_545_);
v___x_550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_535_, v_inst_536_, v_pre_537_, v_post_538_, v_x_539_, v_x_540_, v_body_542_, v___y_541_);
v___x_551_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_550_, v___f_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object* v_declName_552_, lean_object* v_a_553_, lean_object* v_nondep_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_pre_557_, lean_object* v_post_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v___y_561_, lean_object* v_body_562_, lean_object* v___y_563_, lean_object* v_type_564_, lean_object* v_value_565_, lean_object* v_toBind_566_, lean_object* v_a_567_){
_start:
{
uint8_t v_nondep_2261__boxed_568_; lean_object* v_res_569_; 
v_nondep_2261__boxed_568_ = lean_unbox(v_nondep_554_);
v_res_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_declName_552_, v_a_553_, v_nondep_2261__boxed_568_, v_inst_555_, v_inst_556_, v_pre_557_, v_post_558_, v_x_559_, v_x_560_, v___y_561_, v_body_562_, v___y_563_, v_type_564_, v_value_565_, v_toBind_566_, v_a_567_);
lean_dec(v___y_561_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_declName_570_, uint8_t v_nondep_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_pre_574_, lean_object* v_post_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v___y_578_, lean_object* v_body_579_, lean_object* v___y_580_, lean_object* v_type_581_, lean_object* v_value_582_, lean_object* v_toBind_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_box(v_nondep_571_);
lean_inc(v_toBind_583_);
lean_inc_ref(v_value_582_);
lean_inc(v___y_578_);
lean_inc(v_x_577_);
lean_inc(v_post_575_);
lean_inc(v_pre_574_);
lean_inc_ref(v_inst_573_);
lean_inc_ref(v_inst_572_);
v___f_586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_586_, 0, v_declName_570_);
lean_closure_set(v___f_586_, 1, v_a_584_);
lean_closure_set(v___f_586_, 2, v___x_585_);
lean_closure_set(v___f_586_, 3, v_inst_572_);
lean_closure_set(v___f_586_, 4, v_inst_573_);
lean_closure_set(v___f_586_, 5, v_pre_574_);
lean_closure_set(v___f_586_, 6, v_post_575_);
lean_closure_set(v___f_586_, 7, v_x_576_);
lean_closure_set(v___f_586_, 8, v_x_577_);
lean_closure_set(v___f_586_, 9, v___y_578_);
lean_closure_set(v___f_586_, 10, v_body_579_);
lean_closure_set(v___f_586_, 11, v___y_580_);
lean_closure_set(v___f_586_, 12, v_type_581_);
lean_closure_set(v___f_586_, 13, v_value_582_);
lean_closure_set(v___f_586_, 14, v_toBind_583_);
v___x_587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_572_, v_inst_573_, v_pre_574_, v_post_575_, v_x_576_, v_x_577_, v_value_582_, v___y_578_);
v___x_588_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_587_, v___f_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_declName_589_, lean_object* v_nondep_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_pre_593_, lean_object* v_post_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v___y_597_, lean_object* v_body_598_, lean_object* v___y_599_, lean_object* v_type_600_, lean_object* v_value_601_, lean_object* v_toBind_602_, lean_object* v_a_603_){
_start:
{
uint8_t v_nondep_2275__boxed_604_; lean_object* v_res_605_; 
v_nondep_2275__boxed_604_ = lean_unbox(v_nondep_590_);
v_res_605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_declName_589_, v_nondep_2275__boxed_604_, v_inst_591_, v_inst_592_, v_pre_593_, v_post_594_, v_x_595_, v_x_596_, v___y_597_, v_body_598_, v___y_599_, v_type_600_, v_value_601_, v_toBind_602_, v_a_603_);
lean_dec(v___y_597_);
return v_res_605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0(void){
_start:
{
lean_object* v___x_606_; lean_object* v_dummy_607_; 
v___x_606_ = lean_box(0);
v_dummy_607_ = l_Lean_Expr_sort___override(v___x_606_);
return v_dummy_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_expr_608_, lean_object* v_data_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_pre_612_, lean_object* v_post_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v_a_618_){
_start:
{
size_t v___x_619_; size_t v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_ptr_addr(v_expr_608_);
v___x_620_ = lean_ptr_addr(v_a_618_);
v___x_621_ = lean_usize_dec_eq(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref(v___y_617_);
v___x_622_ = l_Lean_Expr_mdata___override(v_data_609_, v_a_618_);
v___x_623_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v___x_622_, v___y_616_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
lean_dec_ref(v_a_618_);
lean_dec(v_data_609_);
v___x_624_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v___y_617_, v___y_616_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_expr_625_, lean_object* v_data_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_pre_629_, lean_object* v_post_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_expr_625_, v_data_626_, v_inst_627_, v_inst_628_, v_pre_629_, v_post_630_, v_x_631_, v_x_632_, v___y_633_, v___y_634_, v_a_635_);
lean_dec(v___y_633_);
lean_dec_ref(v_expr_625_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_struct_637_, lean_object* v_typeName_638_, lean_object* v_idx_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_pre_642_, lean_object* v_post_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v_a_648_){
_start:
{
size_t v___x_649_; size_t v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_ptr_addr(v_struct_637_);
v___x_650_ = lean_ptr_addr(v_a_648_);
v___x_651_ = lean_usize_dec_eq(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v___y_647_);
v___x_652_ = l_Lean_Expr_proj___override(v_typeName_638_, v_idx_639_, v_a_648_);
v___x_653_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_640_, v_inst_641_, v_pre_642_, v_post_643_, v_x_644_, v_x_645_, v___x_652_, v___y_646_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; 
lean_dec_ref(v_a_648_);
lean_dec(v_idx_639_);
lean_dec(v_typeName_638_);
v___x_654_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_640_, v_inst_641_, v_pre_642_, v_post_643_, v_x_644_, v_x_645_, v___y_647_, v___y_646_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_struct_655_, lean_object* v_typeName_656_, lean_object* v_idx_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_pre_660_, lean_object* v_post_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_struct_655_, v_typeName_656_, v_idx_657_, v_inst_658_, v_inst_659_, v_pre_660_, v_post_661_, v_x_662_, v_x_663_, v___y_664_, v___y_665_, v_a_666_);
lean_dec(v___y_664_);
lean_dec_ref(v_struct_655_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_pre_670_, lean_object* v_post_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(v_inst_668_, v_inst_669_, v_pre_670_, v_post_671_, v_x_672_, v_x_673_, v___y_674_, v_a_675_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_toApplicative_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_pre_680_, lean_object* v_post_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_toBind_684_, lean_object* v___f_685_, lean_object* v_e_686_, lean_object* v_____do__lift_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___y_690_; 
switch(lean_obj_tag(v_____do__lift_687_))
{
case 0:
{
lean_object* v_e_735_; lean_object* v_toPure_736_; lean_object* v___x_737_; 
lean_dec_ref(v_e_686_);
lean_dec(v___f_685_);
lean_dec(v_toBind_684_);
lean_dec(v_x_683_);
lean_dec(v_post_681_);
lean_dec(v_pre_680_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
v_e_735_ = lean_ctor_get(v_____do__lift_687_, 0);
lean_inc_ref(v_e_735_);
lean_dec_ref(v_____do__lift_687_);
v_toPure_736_ = lean_ctor_get(v_toApplicative_677_, 1);
lean_inc(v_toPure_736_);
lean_dec_ref(v_toApplicative_677_);
v___x_737_ = lean_apply_2(v_toPure_736_, lean_box(0), v_e_735_);
return v___x_737_;
}
case 1:
{
lean_object* v_e_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref(v_e_686_);
lean_dec(v___f_685_);
lean_dec_ref(v_toApplicative_677_);
v_e_738_ = lean_ctor_get(v_____do__lift_687_, 0);
lean_inc_ref(v_e_738_);
lean_dec_ref(v_____do__lift_687_);
lean_inc(v___y_688_);
lean_inc(v_x_683_);
lean_inc(v_post_681_);
lean_inc(v_pre_680_);
lean_inc_ref(v_inst_679_);
lean_inc_ref(v_inst_678_);
v___f_739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed), 8, 7);
lean_closure_set(v___f_739_, 0, v_inst_678_);
lean_closure_set(v___f_739_, 1, v_inst_679_);
lean_closure_set(v___f_739_, 2, v_pre_680_);
lean_closure_set(v___f_739_, 3, v_post_681_);
lean_closure_set(v___f_739_, 4, v_x_682_);
lean_closure_set(v___f_739_, 5, v_x_683_);
lean_closure_set(v___f_739_, 6, v___y_688_);
v___x_740_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v_e_738_, v___y_688_);
v___x_741_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_740_, v___f_739_);
return v___x_741_;
}
default: 
{
lean_object* v_e_x3f_742_; 
lean_dec_ref(v_toApplicative_677_);
v_e_x3f_742_ = lean_ctor_get(v_____do__lift_687_, 0);
lean_inc(v_e_x3f_742_);
lean_dec_ref(v_____do__lift_687_);
if (lean_obj_tag(v_e_x3f_742_) == 0)
{
v___y_690_ = v_e_686_;
goto v___jp_689_;
}
else
{
lean_object* v_val_743_; 
lean_dec_ref(v_e_686_);
v_val_743_ = lean_ctor_get(v_e_x3f_742_, 0);
lean_inc(v_val_743_);
lean_dec_ref(v_e_x3f_742_);
v___y_690_ = v_val_743_;
goto v___jp_689_;
}
}
}
v___jp_689_:
{
switch(lean_obj_tag(v___y_690_))
{
case 7:
{
lean_object* v_binderName_691_; lean_object* v_binderType_692_; lean_object* v_body_693_; uint8_t v_binderInfo_694_; lean_object* v___x_695_; lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec(v___f_685_);
v_binderName_691_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_binderName_691_);
v_binderType_692_ = lean_ctor_get(v___y_690_, 1);
lean_inc_ref_n(v_binderType_692_, 2);
v_body_693_ = lean_ctor_get(v___y_690_, 2);
lean_inc_ref(v_body_693_);
v_binderInfo_694_ = lean_ctor_get_uint8(v___y_690_, sizeof(void*)*3 + 8);
v___x_695_ = lean_box(v_binderInfo_694_);
lean_inc(v_toBind_684_);
lean_inc(v___y_688_);
lean_inc(v_x_683_);
lean_inc(v_post_681_);
lean_inc(v_pre_680_);
lean_inc_ref(v_inst_679_);
lean_inc_ref(v_inst_678_);
v___f_696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_696_, 0, v_binderName_691_);
lean_closure_set(v___f_696_, 1, v___x_695_);
lean_closure_set(v___f_696_, 2, v_inst_678_);
lean_closure_set(v___f_696_, 3, v_inst_679_);
lean_closure_set(v___f_696_, 4, v_pre_680_);
lean_closure_set(v___f_696_, 5, v_post_681_);
lean_closure_set(v___f_696_, 6, v_x_682_);
lean_closure_set(v___f_696_, 7, v_x_683_);
lean_closure_set(v___f_696_, 8, v___y_688_);
lean_closure_set(v___f_696_, 9, v___y_690_);
lean_closure_set(v___f_696_, 10, v_binderType_692_);
lean_closure_set(v___f_696_, 11, v_body_693_);
lean_closure_set(v___f_696_, 12, v_toBind_684_);
v___x_697_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v_binderType_692_, v___y_688_);
v___x_698_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_697_, v___f_696_);
return v___x_698_;
}
case 6:
{
lean_object* v_binderName_699_; lean_object* v_binderType_700_; lean_object* v_body_701_; uint8_t v_binderInfo_702_; lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v___f_685_);
v_binderName_699_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_binderName_699_);
v_binderType_700_ = lean_ctor_get(v___y_690_, 1);
lean_inc_ref_n(v_binderType_700_, 2);
v_body_701_ = lean_ctor_get(v___y_690_, 2);
lean_inc_ref(v_body_701_);
v_binderInfo_702_ = lean_ctor_get_uint8(v___y_690_, sizeof(void*)*3 + 8);
v___x_703_ = lean_box(v_binderInfo_702_);
lean_inc(v_toBind_684_);
lean_inc(v___y_688_);
lean_inc(v_x_683_);
lean_inc(v_post_681_);
lean_inc(v_pre_680_);
lean_inc_ref(v_inst_679_);
lean_inc_ref(v_inst_678_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 14, 13);
lean_closure_set(v___f_704_, 0, v_binderName_699_);
lean_closure_set(v___f_704_, 1, v___x_703_);
lean_closure_set(v___f_704_, 2, v_inst_678_);
lean_closure_set(v___f_704_, 3, v_inst_679_);
lean_closure_set(v___f_704_, 4, v_pre_680_);
lean_closure_set(v___f_704_, 5, v_post_681_);
lean_closure_set(v___f_704_, 6, v_x_682_);
lean_closure_set(v___f_704_, 7, v_x_683_);
lean_closure_set(v___f_704_, 8, v___y_688_);
lean_closure_set(v___f_704_, 9, v___y_690_);
lean_closure_set(v___f_704_, 10, v_binderType_700_);
lean_closure_set(v___f_704_, 11, v_body_701_);
lean_closure_set(v___f_704_, 12, v_toBind_684_);
v___x_705_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v_binderType_700_, v___y_688_);
v___x_706_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_705_, v___f_704_);
return v___x_706_;
}
case 8:
{
lean_object* v_declName_707_; lean_object* v_type_708_; lean_object* v_value_709_; lean_object* v_body_710_; uint8_t v_nondep_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v___f_685_);
v_declName_707_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_declName_707_);
v_type_708_ = lean_ctor_get(v___y_690_, 1);
lean_inc_ref_n(v_type_708_, 2);
v_value_709_ = lean_ctor_get(v___y_690_, 2);
lean_inc_ref(v_value_709_);
v_body_710_ = lean_ctor_get(v___y_690_, 3);
lean_inc_ref(v_body_710_);
v_nondep_711_ = lean_ctor_get_uint8(v___y_690_, sizeof(void*)*4 + 8);
v___x_712_ = lean_box(v_nondep_711_);
lean_inc(v_toBind_684_);
lean_inc(v___y_688_);
lean_inc(v_x_683_);
lean_inc(v_post_681_);
lean_inc(v_pre_680_);
lean_inc_ref(v_inst_679_);
lean_inc_ref(v_inst_678_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 15, 14);
lean_closure_set(v___f_713_, 0, v_declName_707_);
lean_closure_set(v___f_713_, 1, v___x_712_);
lean_closure_set(v___f_713_, 2, v_inst_678_);
lean_closure_set(v___f_713_, 3, v_inst_679_);
lean_closure_set(v___f_713_, 4, v_pre_680_);
lean_closure_set(v___f_713_, 5, v_post_681_);
lean_closure_set(v___f_713_, 6, v_x_682_);
lean_closure_set(v___f_713_, 7, v_x_683_);
lean_closure_set(v___f_713_, 8, v___y_688_);
lean_closure_set(v___f_713_, 9, v_body_710_);
lean_closure_set(v___f_713_, 10, v___y_690_);
lean_closure_set(v___f_713_, 11, v_type_708_);
lean_closure_set(v___f_713_, 12, v_value_709_);
lean_closure_set(v___f_713_, 13, v_toBind_684_);
v___x_714_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v_type_708_, v___y_688_);
v___x_715_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_714_, v___f_713_);
return v___x_715_;
}
case 5:
{
lean_object* v_dummy_716_; lean_object* v_nargs_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_2110__overap_721_; lean_object* v___x_722_; 
lean_dec(v_toBind_684_);
lean_dec(v_x_683_);
lean_dec(v_post_681_);
lean_dec(v_pre_680_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
v_dummy_716_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_717_ = l_Lean_Expr_getAppNumArgs(v___y_690_);
lean_inc(v_nargs_717_);
v___x_718_ = lean_mk_array(v_nargs_717_, v_dummy_716_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_sub(v_nargs_717_, v___x_719_);
lean_dec(v_nargs_717_);
v___x_2110__overap_721_ = l_Lean_Expr_withAppAux___redArg(v___f_685_, v___y_690_, v___x_718_, v___x_720_);
lean_inc(v___y_688_);
v___x_722_ = lean_apply_1(v___x_2110__overap_721_, v___y_688_);
return v___x_722_;
}
case 10:
{
lean_object* v_data_723_; lean_object* v_expr_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v___f_685_);
v_data_723_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_data_723_);
v_expr_724_ = lean_ctor_get(v___y_690_, 1);
lean_inc_ref_n(v_expr_724_, 2);
lean_inc(v___y_688_);
lean_inc(v_x_683_);
lean_inc(v_post_681_);
lean_inc(v_pre_680_);
lean_inc_ref(v_inst_679_);
lean_inc_ref(v_inst_678_);
v___f_725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 11, 10);
lean_closure_set(v___f_725_, 0, v_expr_724_);
lean_closure_set(v___f_725_, 1, v_data_723_);
lean_closure_set(v___f_725_, 2, v_inst_678_);
lean_closure_set(v___f_725_, 3, v_inst_679_);
lean_closure_set(v___f_725_, 4, v_pre_680_);
lean_closure_set(v___f_725_, 5, v_post_681_);
lean_closure_set(v___f_725_, 6, v_x_682_);
lean_closure_set(v___f_725_, 7, v_x_683_);
lean_closure_set(v___f_725_, 8, v___y_688_);
lean_closure_set(v___f_725_, 9, v___y_690_);
v___x_726_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v_expr_724_, v___y_688_);
v___x_727_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_726_, v___f_725_);
return v___x_727_;
}
case 11:
{
lean_object* v_typeName_728_; lean_object* v_idx_729_; lean_object* v_struct_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v___f_685_);
v_typeName_728_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_typeName_728_);
v_idx_729_ = lean_ctor_get(v___y_690_, 1);
lean_inc(v_idx_729_);
v_struct_730_ = lean_ctor_get(v___y_690_, 2);
lean_inc_ref_n(v_struct_730_, 2);
lean_inc(v___y_688_);
lean_inc(v_x_683_);
lean_inc(v_post_681_);
lean_inc(v_pre_680_);
lean_inc_ref(v_inst_679_);
lean_inc_ref(v_inst_678_);
v___f_731_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 12, 11);
lean_closure_set(v___f_731_, 0, v_struct_730_);
lean_closure_set(v___f_731_, 1, v_typeName_728_);
lean_closure_set(v___f_731_, 2, v_idx_729_);
lean_closure_set(v___f_731_, 3, v_inst_678_);
lean_closure_set(v___f_731_, 4, v_inst_679_);
lean_closure_set(v___f_731_, 5, v_pre_680_);
lean_closure_set(v___f_731_, 6, v_post_681_);
lean_closure_set(v___f_731_, 7, v_x_682_);
lean_closure_set(v___f_731_, 8, v_x_683_);
lean_closure_set(v___f_731_, 9, v___y_688_);
lean_closure_set(v___f_731_, 10, v___y_690_);
v___x_732_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v_struct_730_, v___y_688_);
v___x_733_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_732_, v___f_731_);
return v___x_733_;
}
default: 
{
lean_object* v___x_734_; 
lean_dec(v___f_685_);
lean_dec(v_toBind_684_);
v___x_734_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_678_, v_inst_679_, v_pre_680_, v_post_681_, v_x_682_, v_x_683_, v___y_690_, v___y_688_);
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object* v_toApplicative_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_pre_747_, lean_object* v_post_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_toBind_751_, lean_object* v___f_752_, lean_object* v_e_753_, lean_object* v_____do__lift_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(v_toApplicative_744_, v_inst_745_, v_inst_746_, v_pre_747_, v_post_748_, v_x_749_, v_x_750_, v_toBind_751_, v___f_752_, v_e_753_, v_____do__lift_754_, v___y_755_);
lean_dec(v___y_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_pre_759_, lean_object* v_post_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_e_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v_toApplicative_772_; lean_object* v_toBind_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_757_, 3);
v___x_767_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_761_, v___x_765_, v___x_766_, v_inst_757_);
v___x_768_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_761_, v___x_765_, v___x_766_);
lean_inc_ref_n(v_inst_758_, 3);
lean_inc_ref(v___x_768_);
v___f_769_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_769_, 0, v___x_768_);
lean_closure_set(v___f_769_, 1, v_inst_758_);
v___f_770_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_770_, 0, v___x_768_);
lean_closure_set(v___f_770_, 1, v_inst_758_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___f_769_);
lean_ctor_set(v___x_771_, 1, v___f_770_);
v_toApplicative_772_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref_n(v_toApplicative_772_, 4);
v_toBind_773_ = lean_ctor_get(v_inst_757_, 1);
lean_inc_n(v_toBind_773_, 6);
lean_inc_n(v_x_762_, 3);
lean_inc_n(v_a_764_, 3);
lean_inc_ref_n(v_e_763_, 3);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_774_, 0, v_toApplicative_772_);
lean_closure_set(v___f_774_, 1, v___x_765_);
lean_closure_set(v___f_774_, 2, v___x_766_);
lean_closure_set(v___f_774_, 3, v_e_763_);
lean_closure_set(v___f_774_, 4, v_a_764_);
lean_closure_set(v___f_774_, 5, v_x_762_);
lean_closure_set(v___f_774_, 6, v_toBind_773_);
v___f_775_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_775_, 0, v_toApplicative_772_);
lean_closure_set(v___f_775_, 1, v___x_765_);
lean_closure_set(v___f_775_, 2, v___x_766_);
lean_closure_set(v___f_775_, 3, v_e_763_);
lean_inc_ref(v___x_767_);
lean_inc(v_post_760_);
lean_inc_n(v_pre_759_, 2);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_776_, 0, v_inst_757_);
lean_closure_set(v___f_776_, 1, v_inst_758_);
lean_closure_set(v___f_776_, 2, v_pre_759_);
lean_closure_set(v___f_776_, 3, v_post_760_);
lean_closure_set(v___f_776_, 4, v_x_761_);
lean_closure_set(v___f_776_, 5, v_x_762_);
lean_closure_set(v___f_776_, 6, v___x_767_);
lean_closure_set(v___f_776_, 7, v_toBind_773_);
v___f_777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed), 12, 10);
lean_closure_set(v___f_777_, 0, v_toApplicative_772_);
lean_closure_set(v___f_777_, 1, v_inst_757_);
lean_closure_set(v___f_777_, 2, v_inst_758_);
lean_closure_set(v___f_777_, 3, v_pre_759_);
lean_closure_set(v___f_777_, 4, v_post_760_);
lean_closure_set(v___f_777_, 5, v_x_761_);
lean_closure_set(v___f_777_, 6, v_x_762_);
lean_closure_set(v___f_777_, 7, v_toBind_773_);
lean_closure_set(v___f_777_, 8, v___f_776_);
lean_closure_set(v___f_777_, 9, v_e_763_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed), 14, 13);
lean_closure_set(v___f_778_, 0, v_pre_759_);
lean_closure_set(v___f_778_, 1, v_e_763_);
lean_closure_set(v___f_778_, 2, v_x_761_);
lean_closure_set(v___f_778_, 3, v___x_765_);
lean_closure_set(v___f_778_, 4, v___x_766_);
lean_closure_set(v___f_778_, 5, v_inst_757_);
lean_closure_set(v___f_778_, 6, v___f_777_);
lean_closure_set(v___f_778_, 7, v___x_767_);
lean_closure_set(v___f_778_, 8, v___x_771_);
lean_closure_set(v___f_778_, 9, v_a_764_);
lean_closure_set(v___f_778_, 10, v_toBind_773_);
lean_closure_set(v___f_778_, 11, v___f_774_);
lean_closure_set(v___f_778_, 12, v_toApplicative_772_);
v___x_779_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_779_, 0, lean_box(0));
lean_closure_set(v___x_779_, 1, lean_box(0));
lean_closure_set(v___x_779_, 2, v_a_764_);
v___x_780_ = lean_apply_2(v_x_762_, lean_box(0), v___x_779_);
v___x_781_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_780_, v___f_775_);
v___x_782_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_781_, v___f_778_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_pre_786_, lean_object* v_post_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_a_790_, lean_object* v_e_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___y_794_; 
switch(lean_obj_tag(v_a_792_))
{
case 0:
{
lean_object* v_e_797_; lean_object* v_toPure_798_; lean_object* v___x_799_; 
lean_dec_ref(v_e_791_);
lean_dec(v_x_789_);
lean_dec(v_post_787_);
lean_dec(v_pre_786_);
lean_dec_ref(v_inst_785_);
lean_dec_ref(v_inst_784_);
v_e_797_ = lean_ctor_get(v_a_792_, 0);
lean_inc_ref(v_e_797_);
lean_dec_ref(v_a_792_);
v_toPure_798_ = lean_ctor_get(v_toApplicative_783_, 1);
lean_inc(v_toPure_798_);
lean_dec_ref(v_toApplicative_783_);
v___x_799_ = lean_apply_2(v_toPure_798_, lean_box(0), v_e_797_);
return v___x_799_;
}
case 1:
{
lean_object* v_e_800_; lean_object* v___x_801_; 
lean_dec_ref(v_e_791_);
lean_dec_ref(v_toApplicative_783_);
v_e_800_ = lean_ctor_get(v_a_792_, 0);
lean_inc_ref(v_e_800_);
lean_dec_ref(v_a_792_);
v___x_801_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_784_, v_inst_785_, v_pre_786_, v_post_787_, v_x_788_, v_x_789_, v_e_800_, v_a_790_);
return v___x_801_;
}
default: 
{
lean_object* v_e_x3f_802_; 
lean_dec(v_x_789_);
lean_dec(v_post_787_);
lean_dec(v_pre_786_);
lean_dec_ref(v_inst_785_);
lean_dec_ref(v_inst_784_);
v_e_x3f_802_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_e_x3f_802_);
lean_dec_ref(v_a_792_);
if (lean_obj_tag(v_e_x3f_802_) == 0)
{
v___y_794_ = v_e_791_;
goto v___jp_793_;
}
else
{
lean_object* v_val_803_; 
lean_dec_ref(v_e_791_);
v_val_803_ = lean_ctor_get(v_e_x3f_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref(v_e_x3f_802_);
v___y_794_ = v_val_803_;
goto v___jp_793_;
}
}
}
v___jp_793_:
{
lean_object* v_toPure_795_; lean_object* v___x_796_; 
v_toPure_795_ = lean_ctor_get(v_toApplicative_783_, 1);
lean_inc(v_toPure_795_);
lean_dec_ref(v_toApplicative_783_);
v___x_796_ = lean_apply_2(v_toPure_795_, lean_box(0), v___y_794_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_pre_807_, lean_object* v_post_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_a_811_, lean_object* v_e_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(v_toApplicative_804_, v_inst_805_, v_inst_806_, v_pre_807_, v_post_808_, v_x_809_, v_x_810_, v_a_811_, v_e_812_, v_a_813_);
lean_dec(v_a_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_pre_817_, lean_object* v_post_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_e_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_toApplicative_823_; lean_object* v_toBind_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_toApplicative_823_ = lean_ctor_get(v_inst_815_, 0);
lean_inc_ref(v_toApplicative_823_);
v_toBind_824_ = lean_ctor_get(v_inst_815_, 1);
lean_inc(v_toBind_824_);
lean_inc_ref(v_e_821_);
lean_inc(v_a_822_);
lean_inc(v_post_818_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_825_, 0, v_toApplicative_823_);
lean_closure_set(v___f_825_, 1, v_inst_815_);
lean_closure_set(v___f_825_, 2, v_inst_816_);
lean_closure_set(v___f_825_, 3, v_pre_817_);
lean_closure_set(v___f_825_, 4, v_post_818_);
lean_closure_set(v___f_825_, 5, v_x_819_);
lean_closure_set(v___f_825_, 6, v_x_820_);
lean_closure_set(v___f_825_, 7, v_a_822_);
lean_closure_set(v___f_825_, 8, v_e_821_);
v___x_826_ = lean_apply_1(v_post_818_, v_e_821_);
v___x_827_ = lean_apply_4(v_toBind_824_, lean_box(0), lean_box(0), v___x_826_, v___f_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_pre_830_, lean_object* v_post_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_828_, v_inst_829_, v_pre_830_, v_post_831_, v_x_832_, v_x_833_, v_a_835_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_pre_839_, lean_object* v_post_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_e_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_837_, v_inst_838_, v_pre_839_, v_post_840_, v_x_841_, v_x_842_, v_e_843_, v_a_844_);
lean_dec(v_a_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_pre_849_, lean_object* v_post_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_e_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_847_, v_inst_848_, v_pre_849_, v_post_850_, v_x_851_, v_x_852_, v_e_853_, v_a_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object* v_m_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_pre_859_, lean_object* v_post_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_e_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(v_m_856_, v_inst_857_, v_inst_858_, v_pre_859_, v_post_860_, v_x_861_, v_x_862_, v_e_863_, v_a_864_);
lean_dec(v_a_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_pre_869_, lean_object* v_post_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_e_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_867_, v_inst_868_, v_pre_869_, v_post_870_, v_x_871_, v_x_872_, v_e_873_, v_a_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object* v_m_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_pre_879_, lean_object* v_post_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_e_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(v_m_876_, v_inst_877_, v_inst_878_, v_pre_879_, v_post_880_, v_x_881_, v_x_882_, v_e_883_, v_a_884_);
lean_dec(v_a_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_886_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_apply_1(v_x_886_, lean_box(0));
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Core_transform___redArg___lam__0(v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_893_, lean_object* v_00_u03b1_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_896_, 0, v_x_895_);
v___x_897_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_897_, 0, lean_box(0));
lean_closure_set(v___x_897_, 1, v___f_896_);
v___x_898_ = lean_apply_2(v_inst_893_, lean_box(0), v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_899_, lean_object* v_____x_900_){
_start:
{
lean_object* v_fst_901_; lean_object* v___x_902_; 
v_fst_901_ = lean_ctor_get(v_____x_900_, 0);
lean_inc(v_fst_901_);
lean_dec_ref(v_____x_900_);
v___x_902_ = lean_apply_2(v_toPure_899_, lean_box(0), v_fst_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_903_, lean_object* v_toPure_904_, lean_object* v_s_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_a_903_);
lean_ctor_set(v___x_906_, 1, v_s_905_);
v___x_907_ = lean_apply_2(v_toPure_904_, lean_box(0), v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_908_, lean_object* v_ref_909_, lean_object* v_x_910_, lean_object* v_toBind_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_913_, 0, v_a_912_);
lean_closure_set(v___f_913_, 1, v_toPure_908_);
v___x_914_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_914_, 0, lean_box(0));
lean_closure_set(v___x_914_, 1, lean_box(0));
lean_closure_set(v___x_914_, 2, v_ref_909_);
v___x_915_ = lean_apply_2(v_x_910_, lean_box(0), v___x_914_);
v___x_916_ = lean_apply_4(v_toBind_911_, lean_box(0), lean_box(0), v___x_915_, v___f_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_917_, lean_object* v_x_918_, lean_object* v_toBind_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_pre_922_, lean_object* v_post_923_, lean_object* v_x_924_, lean_object* v_input_925_, lean_object* v_ref_926_){
_start:
{
lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc(v_toBind_919_);
lean_inc(v_x_918_);
lean_inc(v_ref_926_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_927_, 0, v_toPure_917_);
lean_closure_set(v___f_927_, 1, v_ref_926_);
lean_closure_set(v___f_927_, 2, v_x_918_);
lean_closure_set(v___f_927_, 3, v_toBind_919_);
v___x_928_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_920_, v_inst_921_, v_pre_922_, v_post_923_, v_x_924_, v_x_918_, v_input_925_, v_ref_926_);
lean_dec(v_ref_926_);
v___x_929_ = lean_apply_4(v_toBind_919_, lean_box(0), lean_box(0), v___x_928_, v___f_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_box(0);
v___x_931_ = lean_unsigned_to_nat(16u);
v___x_932_ = lean_mk_array(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_937_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_937_, 0, lean_box(0));
lean_closure_set(v___x_937_, 1, lean_box(0));
lean_closure_set(v___x_937_, 2, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_input_941_, lean_object* v_pre_942_, lean_object* v_post_943_){
_start:
{
lean_object* v_x_944_; lean_object* v_toApplicative_945_; lean_object* v_toBind_946_; lean_object* v_toPure_947_; lean_object* v_x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_x_944_ = lean_box(0);
v_toApplicative_945_ = lean_ctor_get(v_inst_938_, 0);
v_toBind_946_ = lean_ctor_get(v_inst_938_, 1);
lean_inc_n(v_toBind_946_, 3);
v_toPure_947_ = lean_ctor_get(v_toApplicative_945_, 1);
lean_inc_n(v_toPure_947_, 2);
lean_inc(v_inst_939_);
v_x_948_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_948_, 0, v_inst_939_);
v___x_949_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_950_ = l_Lean_Core_transform___redArg___lam__1(v_inst_939_, lean_box(0), v___x_949_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_951_, 0, v_toPure_947_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 10, 9);
lean_closure_set(v___f_952_, 0, v_toPure_947_);
lean_closure_set(v___f_952_, 1, v_x_948_);
lean_closure_set(v___f_952_, 2, v_toBind_946_);
lean_closure_set(v___f_952_, 3, v_inst_938_);
lean_closure_set(v___f_952_, 4, v_inst_940_);
lean_closure_set(v___f_952_, 5, v_pre_942_);
lean_closure_set(v___f_952_, 6, v_post_943_);
lean_closure_set(v___f_952_, 7, v_x_944_);
lean_closure_set(v___f_952_, 8, v_input_941_);
v___x_953_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v___x_950_, v___f_952_);
v___x_954_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v___x_953_, v___f_951_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_input_959_, lean_object* v_pre_960_, lean_object* v_post_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Core_transform___redArg(v_inst_956_, v_inst_957_, v_inst_958_, v_input_959_, v_pre_960_, v_post_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
uint8_t v___x_969_; uint8_t v___x_970_; 
v___x_969_ = 0;
v___x_970_ = l_Lean_Expr_isHeadBetaTarget(v_e_965_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec_ref(v_e_965_);
v___x_971_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = l_Lean_Expr_headBeta(v_e_965_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Core_betaReduce___lam__0(v_e_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_e_981_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Core_betaReduce___lam__1(v_e_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_991_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = l_Lean_maxRecDepthErrorMessage;
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1000_ = l_Lean_MessageData_ofFormat(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1002_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1003_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_ref_1004_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___y_1018_; lean_object* v_fileName_1027_; lean_object* v_fileMap_1028_; lean_object* v_options_1029_; lean_object* v_currRecDepth_1030_; lean_object* v_maxRecDepth_1031_; lean_object* v_ref_1032_; lean_object* v_currNamespace_1033_; lean_object* v_openDecls_1034_; lean_object* v_initHeartbeats_1035_; lean_object* v_maxHeartbeats_1036_; lean_object* v_quotContext_1037_; lean_object* v_currMacroScope_1038_; uint8_t v_diag_1039_; lean_object* v_cancelTk_x3f_1040_; uint8_t v_suppressElabErrors_1041_; lean_object* v_inheritedTraceOptions_1042_; uint8_t v___x_1043_; 
v_fileName_1027_ = lean_ctor_get(v___y_1014_, 0);
v_fileMap_1028_ = lean_ctor_get(v___y_1014_, 1);
v_options_1029_ = lean_ctor_get(v___y_1014_, 2);
v_currRecDepth_1030_ = lean_ctor_get(v___y_1014_, 3);
v_maxRecDepth_1031_ = lean_ctor_get(v___y_1014_, 4);
v_ref_1032_ = lean_ctor_get(v___y_1014_, 5);
v_currNamespace_1033_ = lean_ctor_get(v___y_1014_, 6);
v_openDecls_1034_ = lean_ctor_get(v___y_1014_, 7);
v_initHeartbeats_1035_ = lean_ctor_get(v___y_1014_, 8);
v_maxHeartbeats_1036_ = lean_ctor_get(v___y_1014_, 9);
v_quotContext_1037_ = lean_ctor_get(v___y_1014_, 10);
v_currMacroScope_1038_ = lean_ctor_get(v___y_1014_, 11);
v_diag_1039_ = lean_ctor_get_uint8(v___y_1014_, sizeof(void*)*14);
v_cancelTk_x3f_1040_ = lean_ctor_get(v___y_1014_, 12);
v_suppressElabErrors_1041_ = lean_ctor_get_uint8(v___y_1014_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1042_ = lean_ctor_get(v___y_1014_, 13);
v___x_1043_ = lean_nat_dec_eq(v_currRecDepth_1030_, v_maxRecDepth_1031_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_add(v_currRecDepth_1030_, v___x_1044_);
lean_inc_ref(v_inheritedTraceOptions_1042_);
lean_inc(v_cancelTk_x3f_1040_);
lean_inc(v_currMacroScope_1038_);
lean_inc(v_quotContext_1037_);
lean_inc(v_maxHeartbeats_1036_);
lean_inc(v_initHeartbeats_1035_);
lean_inc(v_openDecls_1034_);
lean_inc(v_currNamespace_1033_);
lean_inc(v_ref_1032_);
lean_inc(v_maxRecDepth_1031_);
lean_inc_ref(v_options_1029_);
lean_inc_ref(v_fileMap_1028_);
lean_inc_ref(v_fileName_1027_);
v___x_1046_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1046_, 0, v_fileName_1027_);
lean_ctor_set(v___x_1046_, 1, v_fileMap_1028_);
lean_ctor_set(v___x_1046_, 2, v_options_1029_);
lean_ctor_set(v___x_1046_, 3, v___x_1045_);
lean_ctor_set(v___x_1046_, 4, v_maxRecDepth_1031_);
lean_ctor_set(v___x_1046_, 5, v_ref_1032_);
lean_ctor_set(v___x_1046_, 6, v_currNamespace_1033_);
lean_ctor_set(v___x_1046_, 7, v_openDecls_1034_);
lean_ctor_set(v___x_1046_, 8, v_initHeartbeats_1035_);
lean_ctor_set(v___x_1046_, 9, v_maxHeartbeats_1036_);
lean_ctor_set(v___x_1046_, 10, v_quotContext_1037_);
lean_ctor_set(v___x_1046_, 11, v_currMacroScope_1038_);
lean_ctor_set(v___x_1046_, 12, v_cancelTk_x3f_1040_);
lean_ctor_set(v___x_1046_, 13, v_inheritedTraceOptions_1042_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*14, v_diag_1039_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*14 + 1, v_suppressElabErrors_1041_);
lean_inc(v___y_1015_);
lean_inc(v___y_1013_);
v___x_1047_ = lean_apply_4(v_x_1012_, v___y_1013_, v___x_1046_, v___y_1015_, lean_box(0));
v___y_1018_ = v___x_1047_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref(v_x_1012_);
lean_inc(v_ref_1032_);
v___x_1048_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1032_);
v___y_1018_ = v___x_1048_;
goto v___jp_1017_;
}
v___jp_1017_:
{
if (lean_obj_tag(v___y_1018_) == 0)
{
return v___y_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___y_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___y_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___y_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___y_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1055_, lean_object* v_x_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_apply_1(v_x_1056_, lean_box(0));
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1062_, lean_object* v_x_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1062_, v_x_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
uint8_t v___x_1070_; 
v___x_1070_ = 0;
return v___x_1070_;
}
else
{
lean_object* v_key_1071_; lean_object* v_tail_1072_; uint8_t v___x_1073_; 
v_key_1071_ = lean_ctor_get(v_x_1069_, 0);
v_tail_1072_ = lean_ctor_get(v_x_1069_, 2);
v___x_1073_ = l_Lean_ExprStructEq_beq(v_key_1071_, v_a_1068_);
if (v___x_1073_ == 0)
{
v_x_1069_ = v_tail_1072_;
goto _start;
}
else
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_1075_, lean_object* v_x_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1075_, v_x_1076_);
lean_dec(v_x_1076_);
lean_dec_ref(v_a_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
return v_x_1079_;
}
else
{
lean_object* v_key_1081_; lean_object* v_value_1082_; lean_object* v_tail_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1106_; 
v_key_1081_ = lean_ctor_get(v_x_1080_, 0);
v_value_1082_ = lean_ctor_get(v_x_1080_, 1);
v_tail_1083_ = lean_ctor_get(v_x_1080_, 2);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1085_ = v_x_1080_;
v_isShared_1086_ = v_isSharedCheck_1106_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_tail_1083_);
lean_inc(v_value_1082_);
lean_inc(v_key_1081_);
lean_dec(v_x_1080_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1106_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; uint64_t v___x_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v_fold_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1087_ = lean_array_get_size(v_x_1079_);
v___x_1088_ = l_Lean_ExprStructEq_hash(v_key_1081_);
v___x_1089_ = 32ULL;
v___x_1090_ = lean_uint64_shift_right(v___x_1088_, v___x_1089_);
v_fold_1091_ = lean_uint64_xor(v___x_1088_, v___x_1090_);
v___x_1092_ = 16ULL;
v___x_1093_ = lean_uint64_shift_right(v_fold_1091_, v___x_1092_);
v___x_1094_ = lean_uint64_xor(v_fold_1091_, v___x_1093_);
v___x_1095_ = lean_uint64_to_usize(v___x_1094_);
v___x_1096_ = lean_usize_of_nat(v___x_1087_);
v___x_1097_ = ((size_t)1ULL);
v___x_1098_ = lean_usize_sub(v___x_1096_, v___x_1097_);
v___x_1099_ = lean_usize_land(v___x_1095_, v___x_1098_);
v___x_1100_ = lean_array_uget_borrowed(v_x_1079_, v___x_1099_);
lean_inc(v___x_1100_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 2, v___x_1100_);
v___x_1102_ = v___x_1085_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_key_1081_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_value_1082_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_array_uset(v_x_1079_, v___x_1099_, v___x_1102_);
v_x_1079_ = v___x_1103_;
v_x_1080_ = v_tail_1083_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_1107_, lean_object* v_source_1108_, lean_object* v_target_1109_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_array_get_size(v_source_1108_);
v___x_1111_ = lean_nat_dec_lt(v_i_1107_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v_source_1108_);
lean_dec(v_i_1107_);
return v_target_1109_;
}
else
{
lean_object* v_es_1112_; lean_object* v___x_1113_; lean_object* v_source_1114_; lean_object* v_target_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_es_1112_ = lean_array_fget(v_source_1108_, v_i_1107_);
v___x_1113_ = lean_box(0);
v_source_1114_ = lean_array_fset(v_source_1108_, v_i_1107_, v___x_1113_);
v_target_1115_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_1109_, v_es_1112_);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_i_1107_, v___x_1116_);
lean_dec(v_i_1107_);
v_i_1107_ = v___x_1117_;
v_source_1108_ = v_source_1114_;
v_target_1109_ = v_target_1115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_nbuckets_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1120_ = lean_array_get_size(v_data_1119_);
v___x_1121_ = lean_unsigned_to_nat(2u);
v_nbuckets_1122_ = lean_nat_mul(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_mk_array(v_nbuckets_1122_, v___x_1124_);
v___x_1126_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_1123_, v_data_1119_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_1127_, lean_object* v_b_1128_, lean_object* v_x_1129_){
_start:
{
if (lean_obj_tag(v_x_1129_) == 0)
{
lean_dec(v_b_1128_);
lean_dec_ref(v_a_1127_);
return v_x_1129_;
}
else
{
lean_object* v_key_1130_; lean_object* v_value_1131_; lean_object* v_tail_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
v_key_1130_ = lean_ctor_get(v_x_1129_, 0);
v_value_1131_ = lean_ctor_get(v_x_1129_, 1);
v_tail_1132_ = lean_ctor_get(v_x_1129_, 2);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_x_1129_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v_x_1129_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_tail_1132_);
lean_inc(v_value_1131_);
lean_inc(v_key_1130_);
lean_dec(v_x_1129_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_Lean_ExprStructEq_beq(v_key_1130_, v_a_1127_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1127_, v_b_1128_, v_tail_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 2, v___x_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_key_1130_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_value_1131_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
else
{
lean_object* v___x_1142_; 
lean_dec(v_value_1131_);
lean_dec(v_key_1130_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v_b_1128_);
lean_ctor_set(v___x_1134_, 0, v_a_1127_);
v___x_1142_ = v___x_1134_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1127_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_b_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_tail_1132_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1145_, lean_object* v_a_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_size_1148_; lean_object* v_buckets_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1192_; 
v_size_1148_ = lean_ctor_get(v_m_1145_, 0);
v_buckets_1149_ = lean_ctor_get(v_m_1145_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_m_1145_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1151_ = v_m_1145_;
v_isShared_1152_ = v_isSharedCheck_1192_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_buckets_1149_);
lean_inc(v_size_1148_);
lean_dec(v_m_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1192_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v_fold_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; lean_object* v_bkt_1166_; uint8_t v___x_1167_; 
v___x_1153_ = lean_array_get_size(v_buckets_1149_);
v___x_1154_ = l_Lean_ExprStructEq_hash(v_a_1146_);
v___x_1155_ = 32ULL;
v___x_1156_ = lean_uint64_shift_right(v___x_1154_, v___x_1155_);
v_fold_1157_ = lean_uint64_xor(v___x_1154_, v___x_1156_);
v___x_1158_ = 16ULL;
v___x_1159_ = lean_uint64_shift_right(v_fold_1157_, v___x_1158_);
v___x_1160_ = lean_uint64_xor(v_fold_1157_, v___x_1159_);
v___x_1161_ = lean_uint64_to_usize(v___x_1160_);
v___x_1162_ = lean_usize_of_nat(v___x_1153_);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_sub(v___x_1162_, v___x_1163_);
v___x_1165_ = lean_usize_land(v___x_1161_, v___x_1164_);
v_bkt_1166_ = lean_array_uget_borrowed(v_buckets_1149_, v___x_1165_);
v___x_1167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1146_, v_bkt_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v_size_x27_1169_; lean_object* v___x_1170_; lean_object* v_buckets_x27_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v_size_x27_1169_ = lean_nat_add(v_size_1148_, v___x_1168_);
lean_dec(v_size_1148_);
lean_inc(v_bkt_1166_);
v___x_1170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1146_);
lean_ctor_set(v___x_1170_, 1, v_b_1147_);
lean_ctor_set(v___x_1170_, 2, v_bkt_1166_);
v_buckets_x27_1171_ = lean_array_uset(v_buckets_1149_, v___x_1165_, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(4u);
v___x_1173_ = lean_nat_mul(v_size_x27_1169_, v___x_1172_);
v___x_1174_ = lean_unsigned_to_nat(3u);
v___x_1175_ = lean_nat_div(v___x_1173_, v___x_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_array_get_size(v_buckets_x27_1171_);
v___x_1177_ = lean_nat_dec_le(v___x_1175_, v___x_1176_);
lean_dec(v___x_1175_);
if (v___x_1177_ == 0)
{
lean_object* v_val_1178_; lean_object* v___x_1180_; 
v_val_1178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_1171_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_val_1178_);
lean_ctor_set(v___x_1151_, 0, v_size_x27_1169_);
v___x_1180_ = v___x_1151_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_size_x27_1169_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_val_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
lean_object* v___x_1183_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_buckets_x27_1171_);
lean_ctor_set(v___x_1151_, 0, v_size_x27_1169_);
v___x_1183_ = v___x_1151_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_size_x27_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_buckets_x27_1171_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v_buckets_x27_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_inc(v_bkt_1166_);
v___x_1185_ = lean_box(0);
v_buckets_x27_1186_ = lean_array_uset(v_buckets_1149_, v___x_1165_, v___x_1185_);
v___x_1187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1146_, v_b_1147_, v_bkt_1166_);
v___x_1188_ = lean_array_uset(v_buckets_x27_1186_, v___x_1165_, v___x_1187_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___x_1188_);
v___x_1190_ = v___x_1151_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_size_1148_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1193_, lean_object* v_e_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_st_ref_take(v_a_1193_);
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1197_, v_e_1194_, v_a_1195_);
v___x_1199_ = lean_st_ref_set(v_a_1193_, v___x_1198_);
v___x_1200_ = lean_box(0);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1201_, lean_object* v_e_1202_, lean_object* v_a_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1201_, v_e_1202_, v_a_1203_);
lean_dec(v_a_1201_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1206_, lean_object* v_x_1207_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
else
{
lean_object* v_key_1209_; lean_object* v_value_1210_; lean_object* v_tail_1211_; uint8_t v___x_1212_; 
v_key_1209_ = lean_ctor_get(v_x_1207_, 0);
v_value_1210_ = lean_ctor_get(v_x_1207_, 1);
v_tail_1211_ = lean_ctor_get(v_x_1207_, 2);
v___x_1212_ = l_Lean_ExprStructEq_beq(v_key_1209_, v_a_1206_);
if (v___x_1212_ == 0)
{
v_x_1207_ = v_tail_1211_;
goto _start;
}
else
{
lean_object* v___x_1214_; 
lean_inc(v_value_1210_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_value_1210_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1215_, lean_object* v_x_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1215_, v_x_1216_);
lean_dec(v_x_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_buckets_1220_; lean_object* v___x_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; uint64_t v_fold_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_buckets_1220_ = lean_ctor_get(v_m_1218_, 1);
v___x_1221_ = lean_array_get_size(v_buckets_1220_);
v___x_1222_ = l_Lean_ExprStructEq_hash(v_a_1219_);
v___x_1223_ = 32ULL;
v___x_1224_ = lean_uint64_shift_right(v___x_1222_, v___x_1223_);
v_fold_1225_ = lean_uint64_xor(v___x_1222_, v___x_1224_);
v___x_1226_ = 16ULL;
v___x_1227_ = lean_uint64_shift_right(v_fold_1225_, v___x_1226_);
v___x_1228_ = lean_uint64_xor(v_fold_1225_, v___x_1227_);
v___x_1229_ = lean_uint64_to_usize(v___x_1228_);
v___x_1230_ = lean_usize_of_nat(v___x_1221_);
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_sub(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_usize_land(v___x_1229_, v___x_1232_);
v___x_1234_ = lean_array_uget_borrowed(v_buckets_1220_, v___x_1233_);
v___x_1235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1219_, v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1236_, v_a_1237_);
lean_dec_ref(v_a_1237_);
lean_dec_ref(v_m_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1239_, lean_object* v_post_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_bs_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref(v_post_1240_);
lean_dec_ref(v_pre_1239_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_bs_1243_);
return v___x_1249_;
}
else
{
lean_object* v_v_1250_; lean_object* v___x_1251_; 
v_v_1250_ = lean_array_uget_borrowed(v_bs_1243_, v_i_1242_);
lean_inc(v_v_1250_);
lean_inc_ref(v_post_1240_);
lean_inc_ref(v_pre_1239_);
v___x_1251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1239_, v_post_1240_, v_v_1250_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v_bs_x27_1254_; size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v_bs_x27_1254_ = lean_array_uset(v_bs_1243_, v_i_1242_, v___x_1253_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1242_, v___x_1255_);
v___x_1257_ = lean_array_uset(v_bs_x27_1254_, v_i_1242_, v_a_1252_);
v_i_1242_ = v___x_1256_;
v_bs_1243_ = v___x_1257_;
goto _start;
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_bs_1243_);
lean_dec_ref(v_post_1240_);
lean_dec_ref(v_pre_1239_);
v_a_1259_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1251_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1251_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1267_, lean_object* v_post_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 5)
{
lean_object* v_fn_1276_; lean_object* v_arg_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_fn_1276_ = lean_ctor_get(v_x_1269_, 0);
lean_inc_ref(v_fn_1276_);
v_arg_1277_ = lean_ctor_get(v_x_1269_, 1);
lean_inc_ref(v_arg_1277_);
lean_dec_ref(v_x_1269_);
v___x_1278_ = lean_array_set(v_x_1270_, v_x_1271_, v_arg_1277_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_sub(v_x_1271_, v___x_1279_);
lean_dec(v_x_1271_);
v_x_1269_ = v_fn_1276_;
v_x_1270_ = v___x_1278_;
v_x_1271_ = v___x_1280_;
goto _start;
}
else
{
lean_object* v___x_1282_; 
lean_dec(v_x_1271_);
lean_inc_ref(v_post_1268_);
lean_inc_ref(v_pre_1267_);
v___x_1282_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1267_, v_post_1268_, v_x_1269_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; size_t v_sz_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v_sz_1284_ = lean_array_size(v_x_1270_);
v___x_1285_ = ((size_t)0ULL);
lean_inc_ref(v_post_1268_);
lean_inc_ref(v_pre_1267_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1267_, v_post_1268_, v_sz_1284_, v___x_1285_, v_x_1270_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = l_Lean_mkAppN(v_a_1283_, v_a_1287_);
lean_dec(v_a_1287_);
v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1267_, v_post_1268_, v___x_1288_, v___y_1272_, v___y_1273_, v___y_1274_);
return v___x_1289_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_a_1283_);
lean_dec_ref(v_post_1268_);
lean_dec_ref(v_pre_1267_);
v_a_1290_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1286_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1286_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_dec_ref(v_x_1270_);
lean_dec_ref(v_post_1268_);
lean_dec_ref(v_pre_1267_);
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v_pre_1298_, lean_object* v_e_1299_, lean_object* v_post_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v___y_1313_; uint8_t v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; uint8_t v___y_1340_; uint8_t v___y_1341_; lean_object* v___x_1348_; 
lean_inc_ref(v_pre_1298_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc_ref(v_e_1299_);
v___x_1348_ = lean_apply_4(v_pre_1298_, v_e_1299_, v___y_1302_, v___y_1303_, lean_box(0));
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1438_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1438_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1438_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___y_1354_; 
switch(lean_obj_tag(v_a_1349_))
{
case 0:
{
lean_object* v_e_1428_; lean_object* v___x_1430_; 
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_e_1299_);
lean_dec_ref(v_pre_1298_);
v_e_1428_ = lean_ctor_get(v_a_1349_, 0);
lean_inc_ref(v_e_1428_);
lean_dec_ref(v_a_1349_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v_e_1428_);
v___x_1430_ = v___x_1351_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_e_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
case 1:
{
lean_object* v_e_1432_; lean_object* v___x_1433_; 
lean_del_object(v___x_1351_);
lean_dec_ref(v_e_1299_);
v_e_1432_ = lean_ctor_get(v_a_1349_, 0);
lean_inc_ref(v_e_1432_);
lean_dec_ref(v_a_1349_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_e_1432_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v_a_1434_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1435_;
}
else
{
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1433_;
}
}
default: 
{
lean_object* v_e_x3f_1436_; 
lean_del_object(v___x_1351_);
v_e_x3f_1436_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_e_x3f_1436_);
lean_dec_ref(v_a_1349_);
if (lean_obj_tag(v_e_x3f_1436_) == 0)
{
v___y_1354_ = v_e_1299_;
goto v___jp_1353_;
}
else
{
lean_object* v_val_1437_; 
lean_dec_ref(v_e_1299_);
v_val_1437_ = lean_ctor_get(v_e_x3f_1436_, 0);
lean_inc(v_val_1437_);
lean_dec_ref(v_e_x3f_1436_);
v___y_1354_ = v_val_1437_;
goto v___jp_1353_;
}
}
}
v___jp_1353_:
{
switch(lean_obj_tag(v___y_1354_))
{
case 7:
{
lean_object* v_binderName_1355_; lean_object* v_binderType_1356_; lean_object* v_body_1357_; uint8_t v_binderInfo_1358_; lean_object* v___x_1359_; 
v_binderName_1355_ = lean_ctor_get(v___y_1354_, 0);
lean_inc(v_binderName_1355_);
v_binderType_1356_ = lean_ctor_get(v___y_1354_, 1);
v_body_1357_ = lean_ctor_get(v___y_1354_, 2);
v_binderInfo_1358_ = lean_ctor_get_uint8(v___y_1354_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1356_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1359_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_binderType_1356_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
lean_inc_ref(v_body_1357_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1361_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_body_1357_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; size_t v___x_1363_; size_t v___x_1364_; uint8_t v___x_1365_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = lean_ptr_addr(v_binderType_1356_);
v___x_1364_ = lean_ptr_addr(v_a_1360_);
v___x_1365_ = lean_usize_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
v___y_1336_ = v_a_1362_;
v___y_1337_ = v_a_1360_;
v___y_1338_ = v_binderName_1355_;
v___y_1339_ = v___y_1354_;
v___y_1340_ = v_binderInfo_1358_;
v___y_1341_ = v___x_1365_;
goto v___jp_1335_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_ptr_addr(v_body_1357_);
v___x_1367_ = lean_ptr_addr(v_a_1362_);
v___x_1368_ = lean_usize_dec_eq(v___x_1366_, v___x_1367_);
v___y_1336_ = v_a_1362_;
v___y_1337_ = v_a_1360_;
v___y_1338_ = v_binderName_1355_;
v___y_1339_ = v___y_1354_;
v___y_1340_ = v_binderInfo_1358_;
v___y_1341_ = v___x_1368_;
goto v___jp_1335_;
}
}
else
{
lean_dec(v_a_1360_);
lean_dec(v_binderName_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1361_;
}
}
else
{
lean_dec_ref(v___y_1354_);
lean_dec(v_binderName_1355_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1359_;
}
}
case 6:
{
lean_object* v_binderName_1369_; lean_object* v_binderType_1370_; lean_object* v_body_1371_; uint8_t v_binderInfo_1372_; lean_object* v___x_1373_; 
v_binderName_1369_ = lean_ctor_get(v___y_1354_, 0);
lean_inc(v_binderName_1369_);
v_binderType_1370_ = lean_ctor_get(v___y_1354_, 1);
v_body_1371_ = lean_ctor_get(v___y_1354_, 2);
v_binderInfo_1372_ = lean_ctor_get_uint8(v___y_1354_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1370_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1373_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_binderType_1370_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
lean_inc_ref(v_body_1371_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1375_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_body_1371_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = lean_ptr_addr(v_binderType_1370_);
v___x_1378_ = lean_ptr_addr(v_a_1374_);
v___x_1379_ = lean_usize_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
v___y_1323_ = v_binderInfo_1372_;
v___y_1324_ = v_a_1376_;
v___y_1325_ = v___y_1354_;
v___y_1326_ = v_a_1374_;
v___y_1327_ = v_binderName_1369_;
v___y_1328_ = v___x_1379_;
goto v___jp_1322_;
}
else
{
size_t v___x_1380_; size_t v___x_1381_; uint8_t v___x_1382_; 
v___x_1380_ = lean_ptr_addr(v_body_1371_);
v___x_1381_ = lean_ptr_addr(v_a_1376_);
v___x_1382_ = lean_usize_dec_eq(v___x_1380_, v___x_1381_);
v___y_1323_ = v_binderInfo_1372_;
v___y_1324_ = v_a_1376_;
v___y_1325_ = v___y_1354_;
v___y_1326_ = v_a_1374_;
v___y_1327_ = v_binderName_1369_;
v___y_1328_ = v___x_1382_;
goto v___jp_1322_;
}
}
else
{
lean_dec(v_a_1374_);
lean_dec_ref(v___y_1354_);
lean_dec(v_binderName_1369_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1375_;
}
}
else
{
lean_dec(v_binderName_1369_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1373_;
}
}
case 8:
{
lean_object* v_declName_1383_; lean_object* v_type_1384_; lean_object* v_value_1385_; lean_object* v_body_1386_; uint8_t v_nondep_1387_; lean_object* v___x_1388_; 
v_declName_1383_ = lean_ctor_get(v___y_1354_, 0);
lean_inc(v_declName_1383_);
v_type_1384_ = lean_ctor_get(v___y_1354_, 1);
v_value_1385_ = lean_ctor_get(v___y_1354_, 2);
v_body_1386_ = lean_ctor_get(v___y_1354_, 3);
lean_inc_ref(v_body_1386_);
v_nondep_1387_ = lean_ctor_get_uint8(v___y_1354_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1384_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1388_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_type_1384_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
lean_inc_ref(v_value_1385_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_value_1385_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref(v___x_1390_);
lean_inc_ref(v_body_1386_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_body_1386_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = lean_ptr_addr(v_type_1384_);
v___x_1395_ = lean_ptr_addr(v_a_1389_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
v___y_1306_ = v_nondep_1387_;
v___y_1307_ = v_a_1391_;
v___y_1308_ = v___y_1354_;
v___y_1309_ = v_a_1389_;
v___y_1310_ = v_a_1393_;
v___y_1311_ = v_declName_1383_;
v___y_1312_ = v_body_1386_;
v___y_1313_ = v___x_1396_;
goto v___jp_1305_;
}
else
{
size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = lean_ptr_addr(v_value_1385_);
v___x_1398_ = lean_ptr_addr(v_a_1391_);
v___x_1399_ = lean_usize_dec_eq(v___x_1397_, v___x_1398_);
v___y_1306_ = v_nondep_1387_;
v___y_1307_ = v_a_1391_;
v___y_1308_ = v___y_1354_;
v___y_1309_ = v_a_1389_;
v___y_1310_ = v_a_1393_;
v___y_1311_ = v_declName_1383_;
v___y_1312_ = v_body_1386_;
v___y_1313_ = v___x_1399_;
goto v___jp_1305_;
}
}
else
{
lean_dec(v_a_1391_);
lean_dec(v_a_1389_);
lean_dec_ref(v_body_1386_);
lean_dec_ref(v___y_1354_);
lean_dec(v_declName_1383_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1392_;
}
}
else
{
lean_dec(v_a_1389_);
lean_dec_ref(v_body_1386_);
lean_dec(v_declName_1383_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1390_;
}
}
else
{
lean_dec_ref(v_body_1386_);
lean_dec(v_declName_1383_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1388_;
}
}
case 5:
{
lean_object* v_dummy_1400_; lean_object* v_nargs_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_dummy_1400_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1401_ = l_Lean_Expr_getAppNumArgs(v___y_1354_);
lean_inc(v_nargs_1401_);
v___x_1402_ = lean_mk_array(v_nargs_1401_, v_dummy_1400_);
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_sub(v_nargs_1401_, v___x_1403_);
lean_dec(v_nargs_1401_);
v___x_1405_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1298_, v_post_1300_, v___y_1354_, v___x_1402_, v___x_1404_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1405_;
}
case 10:
{
lean_object* v_data_1406_; lean_object* v_expr_1407_; lean_object* v___x_1408_; 
v_data_1406_ = lean_ctor_get(v___y_1354_, 0);
v_expr_1407_ = lean_ctor_get(v___y_1354_, 1);
lean_inc_ref(v_expr_1407_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1408_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_expr_1407_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; size_t v___x_1410_; size_t v___x_1411_; uint8_t v___x_1412_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = lean_ptr_addr(v_expr_1407_);
v___x_1411_ = lean_ptr_addr(v_a_1409_);
v___x_1412_ = lean_usize_dec_eq(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_inc(v_data_1406_);
lean_dec_ref(v___y_1354_);
v___x_1413_ = l_Lean_Expr_mdata___override(v_data_1406_, v_a_1409_);
v___x_1414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1413_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; 
lean_dec(v_a_1409_);
v___x_1415_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___y_1354_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1415_;
}
}
else
{
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1408_;
}
}
case 11:
{
lean_object* v_typeName_1416_; lean_object* v_idx_1417_; lean_object* v_struct_1418_; lean_object* v___x_1419_; 
v_typeName_1416_ = lean_ctor_get(v___y_1354_, 0);
v_idx_1417_ = lean_ctor_get(v___y_1354_, 1);
v_struct_1418_ = lean_ctor_get(v___y_1354_, 2);
lean_inc_ref(v_struct_1418_);
lean_inc_ref(v_post_1300_);
lean_inc_ref(v_pre_1298_);
v___x_1419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1298_, v_post_1300_, v_struct_1418_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; size_t v___x_1421_; size_t v___x_1422_; uint8_t v___x_1423_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = lean_ptr_addr(v_struct_1418_);
v___x_1422_ = lean_ptr_addr(v_a_1420_);
v___x_1423_ = lean_usize_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_inc(v_idx_1417_);
lean_inc(v_typeName_1416_);
lean_dec_ref(v___y_1354_);
v___x_1424_ = l_Lean_Expr_proj___override(v_typeName_1416_, v_idx_1417_, v_a_1420_);
v___x_1425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1424_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_a_1420_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___y_1354_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1426_;
}
}
else
{
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_pre_1298_);
return v___x_1419_;
}
}
default: 
{
lean_object* v___x_1427_; 
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___y_1354_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1427_;
}
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_post_1300_);
lean_dec_ref(v_e_1299_);
lean_dec_ref(v_pre_1298_);
v_a_1439_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1348_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1348_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
v___jp_1305_:
{
if (v___y_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1308_);
v___x_1314_ = l_Lean_Expr_letE___override(v___y_1311_, v___y_1309_, v___y_1307_, v___y_1310_, v___y_1306_);
v___x_1315_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1314_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1315_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_ptr_addr(v___y_1312_);
lean_dec_ref(v___y_1312_);
v___x_1317_ = lean_ptr_addr(v___y_1310_);
v___x_1318_ = lean_usize_dec_eq(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec_ref(v___y_1308_);
v___x_1319_ = l_Lean_Expr_letE___override(v___y_1311_, v___y_1309_, v___y_1307_, v___y_1310_, v___y_1306_);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1319_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; 
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1307_);
v___x_1321_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___y_1308_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1321_;
}
}
}
v___jp_1322_:
{
if (v___y_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___y_1325_);
v___x_1329_ = l_Lean_Expr_lam___override(v___y_1327_, v___y_1326_, v___y_1324_, v___y_1323_);
v___x_1330_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1329_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1330_;
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_instBEqBinderInfo_beq(v___y_1323_, v___y_1323_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v___y_1325_);
v___x_1332_ = l_Lean_Expr_lam___override(v___y_1327_, v___y_1326_, v___y_1324_, v___y_1323_);
v___x_1333_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1332_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec_ref(v___y_1324_);
v___x_1334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___y_1325_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1334_;
}
}
}
v___jp_1335_:
{
if (v___y_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v___y_1339_);
v___x_1342_ = l_Lean_Expr_forallE___override(v___y_1338_, v___y_1337_, v___y_1336_, v___y_1340_);
v___x_1343_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1342_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1343_;
}
else
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_instBEqBinderInfo_beq(v___y_1340_, v___y_1340_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v___y_1339_);
v___x_1345_ = l_Lean_Expr_forallE___override(v___y_1338_, v___y_1337_, v___y_1336_, v___y_1340_);
v___x_1346_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___x_1345_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v___y_1336_);
v___x_1347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1300_, v___y_1339_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_1447_, lean_object* v_e_1448_, lean_object* v_post_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v_pre_1447_, v_e_1448_, v_post_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1455_, lean_object* v_post_1456_, lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc(v_a_1458_);
v___x_1462_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1462_, 0, lean_box(0));
lean_closure_set(v___x_1462_, 1, lean_box(0));
lean_closure_set(v___x_1462_, 2, v_a_1458_);
v___x_1463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1462_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1494_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1494_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1494_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1464_, v_e_1457_);
lean_dec(v_a_1464_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v___f_1469_; lean_object* v___x_1470_; 
lean_del_object(v___x_1466_);
lean_inc_ref(v_e_1457_);
v___f_1469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_1469_, 0, v_pre_1455_);
lean_closure_set(v___f_1469_, 1, v_e_1457_);
lean_closure_set(v___f_1469_, 2, v_post_1456_);
v___x_1470_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1469_, v_a_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___f_1472_; lean_object* v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_n(v_a_1471_, 2);
lean_dec_ref(v___x_1470_);
lean_inc(v_a_1458_);
v___f_1472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1472_, 0, v_a_1458_);
lean_closure_set(v___f_1472_, 1, v_e_1457_);
lean_closure_set(v___f_1472_, 2, v_a_1471_);
v___x_1473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1472_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1473_, 0);
lean_dec(v_unused_1481_);
v___x_1475_ = v___x_1473_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v___x_1473_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_a_1471_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1471_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1471_);
v_a_1482_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1473_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1473_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_dec_ref(v_e_1457_);
return v___x_1470_;
}
}
else
{
lean_object* v_val_1490_; lean_object* v___x_1492_; 
lean_dec_ref(v_e_1457_);
lean_dec_ref(v_post_1456_);
lean_dec_ref(v_pre_1455_);
v_val_1490_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_val_1490_);
lean_dec_ref(v___x_1468_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_val_1490_);
v___x_1492_ = v___x_1466_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_val_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v_e_1457_);
lean_dec_ref(v_post_1456_);
lean_dec_ref(v_pre_1455_);
v_a_1495_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1463_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1463_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1503_, lean_object* v_post_1504_, lean_object* v_e_1505_, lean_object* v_a_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
lean_inc_ref(v_post_1504_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc_ref(v_e_1505_);
v___x_1510_ = lean_apply_4(v_post_1504_, v_e_1505_, v___y_1507_, v___y_1508_, lean_box(0));
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1529_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1529_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1529_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
switch(lean_obj_tag(v_a_1511_))
{
case 0:
{
lean_object* v_e_1515_; lean_object* v___x_1517_; 
lean_dec_ref(v_e_1505_);
lean_dec_ref(v_post_1504_);
lean_dec_ref(v_pre_1503_);
v_e_1515_ = lean_ctor_get(v_a_1511_, 0);
lean_inc_ref(v_e_1515_);
lean_dec_ref(v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v_e_1515_);
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_e_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
case 1:
{
lean_object* v_e_1519_; lean_object* v___x_1520_; 
lean_del_object(v___x_1513_);
lean_dec_ref(v_e_1505_);
v_e_1519_ = lean_ctor_get(v_a_1511_, 0);
lean_inc_ref(v_e_1519_);
lean_dec_ref(v_a_1511_);
v___x_1520_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1503_, v_post_1504_, v_e_1519_, v_a_1506_, v___y_1507_, v___y_1508_);
return v___x_1520_;
}
default: 
{
lean_object* v_e_x3f_1521_; 
lean_dec_ref(v_post_1504_);
lean_dec_ref(v_pre_1503_);
v_e_x3f_1521_ = lean_ctor_get(v_a_1511_, 0);
lean_inc(v_e_x3f_1521_);
lean_dec_ref(v_a_1511_);
if (lean_obj_tag(v_e_x3f_1521_) == 0)
{
lean_object* v___x_1523_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v_e_1505_);
v___x_1523_ = v___x_1513_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_e_1505_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
else
{
lean_object* v_val_1525_; lean_object* v___x_1527_; 
lean_dec_ref(v_e_1505_);
v_val_1525_ = lean_ctor_get(v_e_x3f_1521_, 0);
lean_inc(v_val_1525_);
lean_dec_ref(v_e_x3f_1521_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v_val_1525_);
v___x_1527_ = v___x_1513_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_val_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_e_1505_);
lean_dec_ref(v_post_1504_);
lean_dec_ref(v_pre_1503_);
v_a_1530_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1510_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1510_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1538_, lean_object* v_post_1539_, lean_object* v_e_1540_, lean_object* v_a_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1538_, v_post_1539_, v_e_1540_, v_a_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v_a_1541_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1546_, lean_object* v_post_1547_, lean_object* v_sz_1548_, lean_object* v_i_1549_, lean_object* v_bs_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
size_t v_sz_boxed_1555_; size_t v_i_boxed_1556_; lean_object* v_res_1557_; 
v_sz_boxed_1555_ = lean_unbox_usize(v_sz_1548_);
lean_dec(v_sz_1548_);
v_i_boxed_1556_ = lean_unbox_usize(v_i_1549_);
lean_dec(v_i_1549_);
v_res_1557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1546_, v_post_1547_, v_sz_boxed_1555_, v_i_boxed_1556_, v_bs_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1558_, lean_object* v_post_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1558_, v_post_1559_, v_x_1560_, v_x_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1568_, lean_object* v_post_1569_, lean_object* v_e_1570_, lean_object* v_a_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1568_, v_post_1569_, v_e_1570_, v_a_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_a_1571_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_apply_1(v_x_1577_, lean_box(0));
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1583_, v_x_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1589_, lean_object* v_pre_1590_, lean_object* v_post_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1596_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1595_, v___y_1592_, v___y_1593_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1590_, v_post_1591_, v_input_1589_, v_a_1597_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1600_, 0, lean_box(0));
lean_closure_set(v___x_1600_, 1, lean_box(0));
lean_closure_set(v___x_1600_, 2, v_a_1597_);
v___x_1601_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1600_, v___y_1592_, v___y_1593_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1601_, 0);
lean_dec(v_unused_1609_);
v___x_1603_ = v___x_1601_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v___x_1601_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_a_1599_);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1599_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
lean_dec(v_a_1597_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1610_, lean_object* v_pre_1611_, lean_object* v_post_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1610_, v_pre_1611_, v_post_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; 
v___f_1623_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1624_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1625_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1619_, v___f_1623_, v___f_1624_, v_a_1620_, v_a_1621_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Core_betaReduce(v_e_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1631_, lean_object* v_m_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1632_, v_a_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1635_, lean_object* v_m_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1635_, v_m_1636_, v_a_1637_);
lean_dec_ref(v_a_1637_);
lean_dec_ref(v_m_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1639_, lean_object* v_ref_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1640_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_ref_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1645_, v_ref_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1651_, lean_object* v_x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1658_, v_x_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1665_, lean_object* v_m_1666_, lean_object* v_a_1667_, lean_object* v_b_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1666_, v_a_1667_, v_b_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1670_, lean_object* v_a_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1671_, v_x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1674_, lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1674_, v_a_1675_, v_x_1676_);
lean_dec(v_x_1676_);
lean_dec_ref(v_a_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1678_, lean_object* v_a_1679_, lean_object* v_x_1680_){
_start:
{
uint8_t v___x_1681_; 
v___x_1681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1679_, v_x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1682_, lean_object* v_a_1683_, lean_object* v_x_1684_){
_start:
{
uint8_t v_res_1685_; lean_object* v_r_1686_; 
v_res_1685_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1682_, v_a_1683_, v_x_1684_);
lean_dec(v_x_1684_);
lean_dec_ref(v_a_1683_);
v_r_1686_ = lean_box(v_res_1685_);
return v_r_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1687_, lean_object* v_data_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1690_, lean_object* v_a_1691_, lean_object* v_b_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1691_, v_b_1692_, v_x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1695_, lean_object* v_i_1696_, lean_object* v_source_1697_, lean_object* v_target_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1696_, v_source_1697_, v_target_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1701_, v_x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_toPure_1706_; lean_object* v___x_1707_; 
v_toPure_1706_ = lean_ctor_get(v_toApplicative_1704_, 1);
lean_inc(v_toPure_1706_);
lean_dec_ref(v_toApplicative_1704_);
v___x_1707_ = lean_apply_2(v_toPure_1706_, lean_box(0), v_a_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_pre_1708_, lean_object* v_e_1709_, lean_object* v_x_1710_, lean_object* v___x_1711_, lean_object* v___x_1712_, lean_object* v_inst_1713_, lean_object* v___f_1714_, lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_a_1717_, lean_object* v_toBind_1718_, lean_object* v___f_1719_, lean_object* v_toApplicative_1720_, lean_object* v_a_1721_){
_start:
{
if (lean_obj_tag(v_a_1721_) == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_3684__overap_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v_toApplicative_1720_);
v___x_1722_ = lean_apply_1(v_pre_1708_, v_e_1709_);
lean_inc_ref(v___x_1712_);
lean_inc_ref(v___x_1711_);
v___x_1723_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1723_, 0, lean_box(0));
lean_closure_set(v___x_1723_, 1, lean_box(0));
lean_closure_set(v___x_1723_, 2, lean_box(0));
lean_closure_set(v___x_1723_, 3, lean_box(0));
lean_closure_set(v___x_1723_, 4, v_x_1710_);
lean_closure_set(v___x_1723_, 5, v___x_1711_);
lean_closure_set(v___x_1723_, 6, v___x_1712_);
lean_closure_set(v___x_1723_, 7, lean_box(0));
lean_closure_set(v___x_1723_, 8, v___x_1722_);
v___x_1724_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1724_, 0, lean_box(0));
lean_closure_set(v___x_1724_, 1, lean_box(0));
lean_closure_set(v___x_1724_, 2, lean_box(0));
lean_closure_set(v___x_1724_, 3, lean_box(0));
lean_closure_set(v___x_1724_, 4, v_x_1710_);
lean_closure_set(v___x_1724_, 5, v___x_1711_);
lean_closure_set(v___x_1724_, 6, v___x_1712_);
lean_closure_set(v___x_1724_, 7, v_inst_1713_);
lean_closure_set(v___x_1724_, 8, lean_box(0));
lean_closure_set(v___x_1724_, 9, lean_box(0));
lean_closure_set(v___x_1724_, 10, v___x_1723_);
lean_closure_set(v___x_1724_, 11, v___f_1714_);
v___x_3684__overap_1725_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1715_, v___x_1716_, v___x_1724_);
lean_inc(v_a_1717_);
v___x_1726_ = lean_apply_1(v___x_3684__overap_1725_, v_a_1717_);
v___x_1727_ = lean_apply_4(v_toBind_1718_, lean_box(0), lean_box(0), v___x_1726_, v___f_1719_);
return v___x_1727_;
}
else
{
lean_object* v_val_1728_; lean_object* v_toPure_1729_; lean_object* v___x_1730_; 
lean_dec(v___f_1719_);
lean_dec(v_toBind_1718_);
lean_dec_ref(v___x_1716_);
lean_dec_ref(v___x_1715_);
lean_dec(v___f_1714_);
lean_dec_ref(v_inst_1713_);
lean_dec_ref(v___x_1712_);
lean_dec_ref(v___x_1711_);
lean_dec_ref(v_e_1709_);
lean_dec(v_pre_1708_);
v_val_1728_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_val_1728_);
lean_dec_ref(v_a_1721_);
v_toPure_1729_ = lean_ctor_get(v_toApplicative_1720_, 1);
lean_inc(v_toPure_1729_);
lean_dec_ref(v_toApplicative_1720_);
v___x_1730_ = lean_apply_2(v_toPure_1729_, lean_box(0), v_val_1728_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_pre_1731_, lean_object* v_e_1732_, lean_object* v_x_1733_, lean_object* v___x_1734_, lean_object* v___x_1735_, lean_object* v_inst_1736_, lean_object* v___f_1737_, lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v_a_1740_, lean_object* v_toBind_1741_, lean_object* v___f_1742_, lean_object* v_toApplicative_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_pre_1731_, v_e_1732_, v_x_1733_, v___x_1734_, v___x_1735_, v_inst_1736_, v___f_1737_, v___x_1738_, v___x_1739_, v_a_1740_, v_toBind_1741_, v___f_1742_, v_toApplicative_1743_, v_a_1744_);
lean_dec(v_a_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v_declName_1748_, lean_object* v_a_1749_, lean_object* v___f_1750_, uint8_t v_nondep_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
uint8_t v___x_1754_; lean_object* v___x_3703__overap_1755_; lean_object* v___x_1756_; 
v___x_1754_ = 0;
v___x_3703__overap_1755_ = l_Lean_Meta_withLetDecl___redArg(v___x_1746_, v___x_1747_, v_declName_1748_, v_a_1749_, v_a_1753_, v___f_1750_, v_nondep_1751_, v___x_1754_);
lean_inc(v_a_1752_);
v___x_1756_ = lean_apply_1(v___x_3703__overap_1755_, v_a_1752_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1757_, lean_object* v___x_1758_, lean_object* v_declName_1759_, lean_object* v_a_1760_, lean_object* v___f_1761_, lean_object* v_nondep_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v_nondep_3850__boxed_1765_; lean_object* v_res_1766_; 
v_nondep_3850__boxed_1765_ = lean_unbox(v_nondep_1762_);
v_res_1766_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1757_, v___x_1758_, v_declName_1759_, v_a_1760_, v___f_1761_, v_nondep_3850__boxed_1765_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1767_, uint8_t v_usedLetOnly_1768_, lean_object* v_inst_1769_, lean_object* v_toBind_1770_, lean_object* v___f_1771_, lean_object* v_a_1772_){
_start:
{
uint8_t v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1773_ = 0;
v___x_1774_ = 1;
v___x_1775_ = lean_box(v_usedLetOnly_1768_);
v___x_1776_ = lean_box(v___x_1773_);
v___x_1777_ = lean_box(v___x_1774_);
v___x_1778_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1778_, 0, v_fvars_1767_);
lean_closure_set(v___x_1778_, 1, v_a_1772_);
lean_closure_set(v___x_1778_, 2, v___x_1775_);
lean_closure_set(v___x_1778_, 3, v___x_1776_);
lean_closure_set(v___x_1778_, 4, v___x_1777_);
v___x_1779_ = lean_apply_2(v_inst_1769_, lean_box(0), v___x_1778_);
v___x_1780_ = lean_apply_4(v_toBind_1770_, lean_box(0), lean_box(0), v___x_1779_, v___f_1771_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1781_, lean_object* v_usedLetOnly_1782_, lean_object* v_inst_1783_, lean_object* v_toBind_1784_, lean_object* v___f_1785_, lean_object* v_a_1786_){
_start:
{
uint8_t v_usedLetOnly_boxed_1787_; lean_object* v_res_1788_; 
v_usedLetOnly_boxed_1787_ = lean_unbox(v_usedLetOnly_1782_);
v_res_1788_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1781_, v_usedLetOnly_boxed_1787_, v_inst_1783_, v_toBind_1784_, v___f_1785_, v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1789_, uint8_t v_usedLetOnly_1790_, lean_object* v_inst_1791_, lean_object* v_toBind_1792_, lean_object* v___f_1793_, lean_object* v_a_1794_){
_start:
{
uint8_t v___x_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1795_ = 0;
v___x_1796_ = 1;
v___x_1797_ = 1;
v___x_1798_ = lean_box(v___x_1795_);
v___x_1799_ = lean_box(v_usedLetOnly_1790_);
v___x_1800_ = lean_box(v___x_1795_);
v___x_1801_ = lean_box(v___x_1796_);
v___x_1802_ = lean_box(v___x_1797_);
v___x_1803_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1803_, 0, v_fvars_1789_);
lean_closure_set(v___x_1803_, 1, v_a_1794_);
lean_closure_set(v___x_1803_, 2, v___x_1798_);
lean_closure_set(v___x_1803_, 3, v___x_1799_);
lean_closure_set(v___x_1803_, 4, v___x_1800_);
lean_closure_set(v___x_1803_, 5, v___x_1801_);
lean_closure_set(v___x_1803_, 6, v___x_1802_);
v___x_1804_ = lean_apply_2(v_inst_1791_, lean_box(0), v___x_1803_);
v___x_1805_ = lean_apply_4(v_toBind_1792_, lean_box(0), lean_box(0), v___x_1804_, v___f_1793_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1806_, lean_object* v_usedLetOnly_1807_, lean_object* v_inst_1808_, lean_object* v_toBind_1809_, lean_object* v___f_1810_, lean_object* v_a_1811_){
_start:
{
uint8_t v_usedLetOnly_boxed_1812_; lean_object* v_res_1813_; 
v_usedLetOnly_boxed_1812_ = lean_unbox(v_usedLetOnly_1807_);
v_res_1813_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1806_, v_usedLetOnly_boxed_1812_, v_inst_1808_, v_toBind_1809_, v___f_1810_, v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v_binderName_1816_, uint8_t v_binderInfo_1817_, lean_object* v___f_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
uint8_t v___x_1821_; lean_object* v___x_3761__overap_1822_; lean_object* v___x_1823_; 
v___x_1821_ = 0;
v___x_3761__overap_1822_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1814_, v___x_1815_, v_binderName_1816_, v_binderInfo_1817_, v_a_1820_, v___f_1818_, v___x_1821_);
lean_inc(v_a_1819_);
v___x_1823_ = lean_apply_1(v___x_3761__overap_1822_, v_a_1819_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1824_, lean_object* v___x_1825_, lean_object* v_binderName_1826_, lean_object* v_binderInfo_1827_, lean_object* v___f_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
uint8_t v_binderInfo_3918__boxed_1831_; lean_object* v_res_1832_; 
v_binderInfo_3918__boxed_1831_ = lean_unbox(v_binderInfo_1827_);
v_res_1832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1824_, v___x_1825_, v_binderName_1826_, v_binderInfo_3918__boxed_1831_, v___f_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1829_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1833_, uint8_t v_usedLetOnly_1834_, lean_object* v_inst_1835_, lean_object* v_toBind_1836_, lean_object* v___f_1837_, lean_object* v_a_1838_){
_start:
{
uint8_t v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1839_ = 0;
v___x_1840_ = 1;
v___x_1841_ = 1;
v___x_1842_ = lean_box(v___x_1839_);
v___x_1843_ = lean_box(v_usedLetOnly_1834_);
v___x_1844_ = lean_box(v___x_1840_);
v___x_1845_ = lean_box(v___x_1841_);
v___x_1846_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1846_, 0, v_fvars_1833_);
lean_closure_set(v___x_1846_, 1, v_a_1838_);
lean_closure_set(v___x_1846_, 2, v___x_1842_);
lean_closure_set(v___x_1846_, 3, v___x_1843_);
lean_closure_set(v___x_1846_, 4, v___x_1844_);
lean_closure_set(v___x_1846_, 5, v___x_1845_);
v___x_1847_ = lean_apply_2(v_inst_1835_, lean_box(0), v___x_1846_);
v___x_1848_ = lean_apply_4(v_toBind_1836_, lean_box(0), lean_box(0), v___x_1847_, v___f_1837_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1849_, lean_object* v_usedLetOnly_1850_, lean_object* v_inst_1851_, lean_object* v_toBind_1852_, lean_object* v___f_1853_, lean_object* v_a_1854_){
_start:
{
uint8_t v_usedLetOnly_boxed_1855_; lean_object* v_res_1856_; 
v_usedLetOnly_boxed_1855_ = lean_unbox(v_usedLetOnly_1850_);
v_res_1856_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1849_, v_usedLetOnly_boxed_1855_, v_inst_1851_, v_toBind_1852_, v___f_1853_, v_a_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1857_, lean_object* v___y_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1860_; 
lean_inc(v___y_1858_);
v___x_1860_ = lean_apply_2(v___f_1857_, v_a_1859_, v___y_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1861_, lean_object* v___y_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1861_, v___y_1862_, v_a_1863_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1865_, lean_object* v_acc_1866_, lean_object* v_next_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_toPure_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_toPure_1869_ = lean_ctor_get(v_toApplicative_1865_, 1);
lean_inc(v_toPure_1869_);
lean_dec_ref(v_toApplicative_1865_);
v___x_1870_ = lean_array_fset(v_acc_1866_, v_next_1867_, v_a_1868_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
v___x_1872_ = lean_apply_2(v_toPure_1869_, lean_box(0), v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1873_, lean_object* v_acc_1874_, lean_object* v_next_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1873_, v_acc_1874_, v_next_1875_, v_a_1876_);
lean_dec(v_next_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1878_, lean_object* v_next_1879_, lean_object* v_G_1880_, lean_object* v___y_1881_, lean_object* v_a_1882_){
_start:
{
if (lean_obj_tag(v_a_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_toPure_1884_; lean_object* v___x_1885_; 
lean_dec(v_G_1880_);
v_a_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v_a_1882_);
v_toPure_1884_ = lean_ctor_get(v_toApplicative_1878_, 1);
lean_inc(v_toPure_1884_);
lean_dec_ref(v_toApplicative_1878_);
v___x_1885_ = lean_apply_2(v_toPure_1884_, lean_box(0), v_a_1883_);
return v___x_1885_;
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_toApplicative_1878_);
v_a_1886_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v_a_1882_);
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_add(v_next_1879_, v___x_1887_);
lean_inc(v___y_1881_);
v___x_1889_ = lean_apply_5(v_G_1880_, v___x_1888_, v_a_1886_, lean_box(0), lean_box(0), v___y_1881_);
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_1890_, lean_object* v_next_1891_, lean_object* v_G_1892_, lean_object* v___y_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_1890_, v_next_1891_, v_G_1892_, v___y_1893_, v_a_1894_);
lean_dec(v___y_1893_);
lean_dec(v_next_1891_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_pre_1900_, lean_object* v_post_1901_, uint8_t v_usedLetOnly_1902_, uint8_t v_skipConstInApp_1903_, uint8_t v_skipInstances_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = l_Lean_mkAppN(v_f_1896_, v_a_1908_);
v___x_1910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_1897_, v_inst_1898_, v_inst_1899_, v_pre_1900_, v_post_1901_, v_usedLetOnly_1902_, v_skipConstInApp_1903_, v_skipInstances_1904_, v_x_1905_, v_x_1906_, v___x_1909_, v___y_1907_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_pre_1915_, lean_object* v_post_1916_, lean_object* v_usedLetOnly_1917_, lean_object* v_skipConstInApp_1918_, lean_object* v_skipInstances_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v___y_1922_, lean_object* v_a_1923_){
_start:
{
uint8_t v_usedLetOnly_boxed_1924_; uint8_t v_skipConstInApp_boxed_1925_; uint8_t v_skipInstances_boxed_1926_; lean_object* v_res_1927_; 
v_usedLetOnly_boxed_1924_ = lean_unbox(v_usedLetOnly_1917_);
v_skipConstInApp_boxed_1925_ = lean_unbox(v_skipConstInApp_1918_);
v_skipInstances_boxed_1926_ = lean_unbox(v_skipInstances_1919_);
v_res_1927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_1911_, v_inst_1912_, v_inst_1913_, v_inst_1914_, v_pre_1915_, v_post_1916_, v_usedLetOnly_boxed_1924_, v_skipConstInApp_boxed_1925_, v_skipInstances_boxed_1926_, v_x_1920_, v_x_1921_, v___y_1922_, v_a_1923_);
lean_dec_ref(v_a_1923_);
lean_dec(v___y_1922_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_pre_1931_, lean_object* v_post_1932_, lean_object* v_usedLetOnly_1933_, lean_object* v_skipConstInApp_1934_, lean_object* v_skipInstances_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_, lean_object* v_e_1938_, lean_object* v_a_1939_){
_start:
{
uint8_t v_usedLetOnly_boxed_1940_; uint8_t v_skipConstInApp_boxed_1941_; uint8_t v_skipInstances_boxed_1942_; lean_object* v_res_1943_; 
v_usedLetOnly_boxed_1940_ = lean_unbox(v_usedLetOnly_1933_);
v_skipConstInApp_boxed_1941_ = lean_unbox(v_skipConstInApp_1934_);
v_skipInstances_boxed_1942_ = lean_unbox(v_skipInstances_1935_);
v_res_1943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1928_, v_inst_1929_, v_inst_1930_, v_pre_1931_, v_post_1932_, v_usedLetOnly_boxed_1940_, v_skipConstInApp_boxed_1941_, v_skipInstances_boxed_1942_, v_x_1936_, v_x_1937_, v_e_1938_, v_a_1939_);
lean_dec(v_a_1939_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_1944_, lean_object* v_toApplicative_1945_, lean_object* v_toBind_1946_, lean_object* v___f_1947_, lean_object* v_paramInfo_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_pre_1952_, lean_object* v_post_1953_, uint8_t v_usedLetOnly_1954_, uint8_t v_skipConstInApp_1955_, uint8_t v_skipInstances_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_next_1959_, lean_object* v_acc_1960_, lean_object* v_h_1961_, lean_object* v_G_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_nat_dec_lt(v_next_1959_, v___x_1944_);
if (v___x_1964_ == 0)
{
lean_object* v_toPure_1965_; lean_object* v___x_1966_; 
lean_dec(v_G_1962_);
lean_dec(v_next_1959_);
lean_dec(v_x_1958_);
lean_dec(v_post_1953_);
lean_dec(v_pre_1952_);
lean_dec_ref(v_inst_1951_);
lean_dec(v_inst_1950_);
lean_dec_ref(v_inst_1949_);
lean_dec(v___f_1947_);
lean_dec(v_toBind_1946_);
v_toPure_1965_ = lean_ctor_get(v_toApplicative_1945_, 1);
lean_inc(v_toPure_1965_);
lean_dec_ref(v_toApplicative_1945_);
v___x_1966_ = lean_apply_2(v_toPure_1965_, lean_box(0), v_acc_1960_);
return v___x_1966_;
}
else
{
lean_object* v___f_1967_; lean_object* v___y_1969_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
lean_inc(v___y_1963_);
lean_inc(v_next_1959_);
lean_inc_ref(v_toApplicative_1945_);
v___f_1967_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1967_, 0, v_toApplicative_1945_);
lean_closure_set(v___f_1967_, 1, v_next_1959_);
lean_closure_set(v___f_1967_, 2, v_G_1962_);
lean_closure_set(v___f_1967_, 3, v___y_1963_);
v___x_1972_ = lean_array_fget_borrowed(v_acc_1960_, v_next_1959_);
v___x_1973_ = lean_array_get_size(v_paramInfo_1948_);
v___x_1974_ = lean_nat_dec_lt(v_next_1959_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_inc(v___x_1972_);
v___f_1975_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1975_, 0, v_toApplicative_1945_);
lean_closure_set(v___f_1975_, 1, v_acc_1960_);
lean_closure_set(v___f_1975_, 2, v_next_1959_);
v___x_1976_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1949_, v_inst_1950_, v_inst_1951_, v_pre_1952_, v_post_1953_, v_usedLetOnly_1954_, v_skipConstInApp_1955_, v_skipInstances_1956_, v_x_1957_, v_x_1958_, v___x_1972_, v___y_1963_);
lean_inc(v_toBind_1946_);
v___x_1977_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1976_, v___f_1975_);
v___y_1969_ = v___x_1977_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_1978_; uint8_t v_isInstance_1979_; 
v___x_1978_ = lean_array_fget_borrowed(v_paramInfo_1948_, v_next_1959_);
v_isInstance_1979_ = lean_ctor_get_uint8(v___x_1978_, sizeof(void*)*1 + 4);
if (v_isInstance_1979_ == 0)
{
lean_object* v___f_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_inc(v___x_1972_);
v___f_1980_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1980_, 0, v_toApplicative_1945_);
lean_closure_set(v___f_1980_, 1, v_acc_1960_);
lean_closure_set(v___f_1980_, 2, v_next_1959_);
v___x_1981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1949_, v_inst_1950_, v_inst_1951_, v_pre_1952_, v_post_1953_, v_usedLetOnly_1954_, v_skipConstInApp_1955_, v_skipInstances_1956_, v_x_1957_, v_x_1958_, v___x_1972_, v___y_1963_);
lean_inc(v_toBind_1946_);
v___x_1982_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1981_, v___f_1980_);
v___y_1969_ = v___x_1982_;
goto v___jp_1968_;
}
else
{
lean_object* v_toPure_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec(v_next_1959_);
lean_dec(v_x_1958_);
lean_dec(v_post_1953_);
lean_dec(v_pre_1952_);
lean_dec_ref(v_inst_1951_);
lean_dec(v_inst_1950_);
lean_dec_ref(v_inst_1949_);
v_toPure_1983_ = lean_ctor_get(v_toApplicative_1945_, 1);
lean_inc(v_toPure_1983_);
lean_dec_ref(v_toApplicative_1945_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_acc_1960_);
v___x_1985_ = lean_apply_2(v_toPure_1983_, lean_box(0), v___x_1984_);
v___y_1969_ = v___x_1985_;
goto v___jp_1968_;
}
}
v___jp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_inc(v_toBind_1946_);
v___x_1970_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___y_1969_, v___f_1947_);
v___x_1971_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1970_, v___f_1967_);
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1986_ = _args[0];
lean_object* v_toApplicative_1987_ = _args[1];
lean_object* v_toBind_1988_ = _args[2];
lean_object* v___f_1989_ = _args[3];
lean_object* v_paramInfo_1990_ = _args[4];
lean_object* v_inst_1991_ = _args[5];
lean_object* v_inst_1992_ = _args[6];
lean_object* v_inst_1993_ = _args[7];
lean_object* v_pre_1994_ = _args[8];
lean_object* v_post_1995_ = _args[9];
lean_object* v_usedLetOnly_1996_ = _args[10];
lean_object* v_skipConstInApp_1997_ = _args[11];
lean_object* v_skipInstances_1998_ = _args[12];
lean_object* v_x_1999_ = _args[13];
lean_object* v_x_2000_ = _args[14];
lean_object* v_next_2001_ = _args[15];
lean_object* v_acc_2002_ = _args[16];
lean_object* v_h_2003_ = _args[17];
lean_object* v_G_2004_ = _args[18];
lean_object* v___y_2005_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2006_; uint8_t v_skipConstInApp_boxed_2007_; uint8_t v_skipInstances_boxed_2008_; lean_object* v_res_2009_; 
v_usedLetOnly_boxed_2006_ = lean_unbox(v_usedLetOnly_1996_);
v_skipConstInApp_boxed_2007_ = lean_unbox(v_skipConstInApp_1997_);
v_skipInstances_boxed_2008_ = lean_unbox(v_skipInstances_1998_);
v_res_2009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_1986_, v_toApplicative_1987_, v_toBind_1988_, v___f_1989_, v_paramInfo_1990_, v_inst_1991_, v_inst_1992_, v_inst_1993_, v_pre_1994_, v_post_1995_, v_usedLetOnly_boxed_2006_, v_skipConstInApp_boxed_2007_, v_skipInstances_boxed_2008_, v_x_1999_, v_x_2000_, v_next_2001_, v_acc_2002_, v_h_2003_, v_G_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v_paramInfo_1990_);
lean_dec(v___x_1986_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2010_, lean_object* v_toApplicative_2011_, lean_object* v_toBind_2012_, lean_object* v___f_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_pre_2017_, lean_object* v_post_2018_, uint8_t v_usedLetOnly_2019_, uint8_t v_skipConstInApp_2020_, uint8_t v_skipInstances_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_args_2024_, lean_object* v___y_2025_, lean_object* v___f_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_paramInfo_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___f_2033_; lean_object* v___x_3541__overap_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_paramInfo_2028_ = lean_ctor_get(v_a_2027_, 0);
lean_inc_ref(v_paramInfo_2028_);
lean_dec_ref(v_a_2027_);
v___x_2029_ = lean_unsigned_to_nat(0u);
v___x_2030_ = lean_box(v_usedLetOnly_2019_);
v___x_2031_ = lean_box(v_skipConstInApp_2020_);
v___x_2032_ = lean_box(v_skipInstances_2021_);
lean_inc(v_toBind_2012_);
v___f_2033_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2033_, 0, v___x_2010_);
lean_closure_set(v___f_2033_, 1, v_toApplicative_2011_);
lean_closure_set(v___f_2033_, 2, v_toBind_2012_);
lean_closure_set(v___f_2033_, 3, v___f_2013_);
lean_closure_set(v___f_2033_, 4, v_paramInfo_2028_);
lean_closure_set(v___f_2033_, 5, v_inst_2014_);
lean_closure_set(v___f_2033_, 6, v_inst_2015_);
lean_closure_set(v___f_2033_, 7, v_inst_2016_);
lean_closure_set(v___f_2033_, 8, v_pre_2017_);
lean_closure_set(v___f_2033_, 9, v_post_2018_);
lean_closure_set(v___f_2033_, 10, v___x_2030_);
lean_closure_set(v___f_2033_, 11, v___x_2031_);
lean_closure_set(v___f_2033_, 12, v___x_2032_);
lean_closure_set(v___f_2033_, 13, v_x_2022_);
lean_closure_set(v___f_2033_, 14, v_x_2023_);
v___x_3541__overap_2034_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2033_, v___x_2029_, v_args_2024_, lean_box(0));
lean_inc(v___y_2025_);
v___x_2035_ = lean_apply_1(v___x_3541__overap_2034_, v___y_2025_);
v___x_2036_ = lean_apply_4(v_toBind_2012_, lean_box(0), lean_box(0), v___x_2035_, v___f_2026_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2037_ = _args[0];
lean_object* v_toApplicative_2038_ = _args[1];
lean_object* v_toBind_2039_ = _args[2];
lean_object* v___f_2040_ = _args[3];
lean_object* v_inst_2041_ = _args[4];
lean_object* v_inst_2042_ = _args[5];
lean_object* v_inst_2043_ = _args[6];
lean_object* v_pre_2044_ = _args[7];
lean_object* v_post_2045_ = _args[8];
lean_object* v_usedLetOnly_2046_ = _args[9];
lean_object* v_skipConstInApp_2047_ = _args[10];
lean_object* v_skipInstances_2048_ = _args[11];
lean_object* v_x_2049_ = _args[12];
lean_object* v_x_2050_ = _args[13];
lean_object* v_args_2051_ = _args[14];
lean_object* v___y_2052_ = _args[15];
lean_object* v___f_2053_ = _args[16];
lean_object* v_a_2054_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2055_; uint8_t v_skipConstInApp_boxed_2056_; uint8_t v_skipInstances_boxed_2057_; lean_object* v_res_2058_; 
v_usedLetOnly_boxed_2055_ = lean_unbox(v_usedLetOnly_2046_);
v_skipConstInApp_boxed_2056_ = lean_unbox(v_skipConstInApp_2047_);
v_skipInstances_boxed_2057_ = lean_unbox(v_skipInstances_2048_);
v_res_2058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2037_, v_toApplicative_2038_, v_toBind_2039_, v___f_2040_, v_inst_2041_, v_inst_2042_, v_inst_2043_, v_pre_2044_, v_post_2045_, v_usedLetOnly_boxed_2055_, v_skipConstInApp_boxed_2056_, v_skipInstances_boxed_2057_, v_x_2049_, v_x_2050_, v_args_2051_, v___y_2052_, v___f_2053_, v_a_2054_);
lean_dec(v___y_2052_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_pre_2063_, lean_object* v_post_2064_, uint8_t v_usedLetOnly_2065_, uint8_t v_skipConstInApp_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v_args_2069_, lean_object* v___x_2070_, lean_object* v_toBind_2071_, lean_object* v_toApplicative_2072_, lean_object* v___f_2073_, lean_object* v_f_2074_, lean_object* v___y_2075_){
_start:
{
if (v_skipInstances_2059_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___f_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_3554__overap_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v___f_2073_);
lean_dec_ref(v_toApplicative_2072_);
v___x_2076_ = lean_box(v_usedLetOnly_2065_);
v___x_2077_ = lean_box(v_skipConstInApp_2066_);
v___x_2078_ = lean_box(v_skipInstances_2059_);
lean_inc_n(v___y_2075_, 2);
lean_inc(v_x_2068_);
lean_inc(v_post_2064_);
lean_inc(v_pre_2063_);
lean_inc_ref(v_inst_2062_);
lean_inc(v_inst_2061_);
lean_inc_ref(v_inst_2060_);
v___f_2079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2079_, 0, v_f_2074_);
lean_closure_set(v___f_2079_, 1, v_inst_2060_);
lean_closure_set(v___f_2079_, 2, v_inst_2061_);
lean_closure_set(v___f_2079_, 3, v_inst_2062_);
lean_closure_set(v___f_2079_, 4, v_pre_2063_);
lean_closure_set(v___f_2079_, 5, v_post_2064_);
lean_closure_set(v___f_2079_, 6, v___x_2076_);
lean_closure_set(v___f_2079_, 7, v___x_2077_);
lean_closure_set(v___f_2079_, 8, v___x_2078_);
lean_closure_set(v___f_2079_, 9, v_x_2067_);
lean_closure_set(v___f_2079_, 10, v_x_2068_);
lean_closure_set(v___f_2079_, 11, v___y_2075_);
v___x_2080_ = lean_box(v_usedLetOnly_2065_);
v___x_2081_ = lean_box(v_skipConstInApp_2066_);
v___x_2082_ = lean_box(v_skipInstances_2059_);
v___x_2083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2083_, 0, v_inst_2060_);
lean_closure_set(v___x_2083_, 1, v_inst_2061_);
lean_closure_set(v___x_2083_, 2, v_inst_2062_);
lean_closure_set(v___x_2083_, 3, v_pre_2063_);
lean_closure_set(v___x_2083_, 4, v_post_2064_);
lean_closure_set(v___x_2083_, 5, v___x_2080_);
lean_closure_set(v___x_2083_, 6, v___x_2081_);
lean_closure_set(v___x_2083_, 7, v___x_2082_);
lean_closure_set(v___x_2083_, 8, v_x_2067_);
lean_closure_set(v___x_2083_, 9, v_x_2068_);
v_sz_2084_ = lean_array_size(v_args_2069_);
v___x_2085_ = ((size_t)0ULL);
v___x_3554__overap_2086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2070_, v___x_2083_, v_sz_2084_, v___x_2085_, v_args_2069_);
v___x_2087_ = lean_apply_1(v___x_3554__overap_2086_, v___y_2075_);
v___x_2088_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2087_, v___f_2079_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec_ref(v___x_2070_);
v___x_2089_ = lean_box(v_usedLetOnly_2065_);
v___x_2090_ = lean_box(v_skipConstInApp_2066_);
v___x_2091_ = lean_box(v_skipInstances_2059_);
lean_inc_n(v___y_2075_, 2);
lean_inc(v_x_2068_);
lean_inc(v_post_2064_);
lean_inc(v_pre_2063_);
lean_inc_ref(v_inst_2062_);
lean_inc_n(v_inst_2061_, 2);
lean_inc_ref(v_inst_2060_);
lean_inc_ref(v_f_2074_);
v___f_2092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2092_, 0, v_f_2074_);
lean_closure_set(v___f_2092_, 1, v_inst_2060_);
lean_closure_set(v___f_2092_, 2, v_inst_2061_);
lean_closure_set(v___f_2092_, 3, v_inst_2062_);
lean_closure_set(v___f_2092_, 4, v_pre_2063_);
lean_closure_set(v___f_2092_, 5, v_post_2064_);
lean_closure_set(v___f_2092_, 6, v___x_2089_);
lean_closure_set(v___f_2092_, 7, v___x_2090_);
lean_closure_set(v___f_2092_, 8, v___x_2091_);
lean_closure_set(v___f_2092_, 9, v_x_2067_);
lean_closure_set(v___f_2092_, 10, v_x_2068_);
lean_closure_set(v___f_2092_, 11, v___y_2075_);
v___x_2093_ = lean_array_get_size(v_args_2069_);
v___x_2094_ = lean_box(v_usedLetOnly_2065_);
v___x_2095_ = lean_box(v_skipConstInApp_2066_);
v___x_2096_ = lean_box(v_skipInstances_2059_);
lean_inc(v_toBind_2071_);
v___f_2097_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2097_, 0, v___x_2093_);
lean_closure_set(v___f_2097_, 1, v_toApplicative_2072_);
lean_closure_set(v___f_2097_, 2, v_toBind_2071_);
lean_closure_set(v___f_2097_, 3, v___f_2073_);
lean_closure_set(v___f_2097_, 4, v_inst_2060_);
lean_closure_set(v___f_2097_, 5, v_inst_2061_);
lean_closure_set(v___f_2097_, 6, v_inst_2062_);
lean_closure_set(v___f_2097_, 7, v_pre_2063_);
lean_closure_set(v___f_2097_, 8, v_post_2064_);
lean_closure_set(v___f_2097_, 9, v___x_2094_);
lean_closure_set(v___f_2097_, 10, v___x_2095_);
lean_closure_set(v___f_2097_, 11, v___x_2096_);
lean_closure_set(v___f_2097_, 12, v_x_2067_);
lean_closure_set(v___f_2097_, 13, v_x_2068_);
lean_closure_set(v___f_2097_, 14, v_args_2069_);
lean_closure_set(v___f_2097_, 15, v___y_2075_);
lean_closure_set(v___f_2097_, 16, v___f_2092_);
v___x_2098_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2098_, 0, v_f_2074_);
lean_closure_set(v___x_2098_, 1, v___x_2093_);
v___x_2099_ = lean_apply_2(v_inst_2061_, lean_box(0), v___x_2098_);
v___x_2100_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2099_, v___f_2097_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2101_ = _args[0];
lean_object* v_inst_2102_ = _args[1];
lean_object* v_inst_2103_ = _args[2];
lean_object* v_inst_2104_ = _args[3];
lean_object* v_pre_2105_ = _args[4];
lean_object* v_post_2106_ = _args[5];
lean_object* v_usedLetOnly_2107_ = _args[6];
lean_object* v_skipConstInApp_2108_ = _args[7];
lean_object* v_x_2109_ = _args[8];
lean_object* v_x_2110_ = _args[9];
lean_object* v_args_2111_ = _args[10];
lean_object* v___x_2112_ = _args[11];
lean_object* v_toBind_2113_ = _args[12];
lean_object* v_toApplicative_2114_ = _args[13];
lean_object* v___f_2115_ = _args[14];
lean_object* v_f_2116_ = _args[15];
lean_object* v___y_2117_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2118_; uint8_t v_usedLetOnly_boxed_2119_; uint8_t v_skipConstInApp_boxed_2120_; lean_object* v_res_2121_; 
v_skipInstances_boxed_2118_ = lean_unbox(v_skipInstances_2101_);
v_usedLetOnly_boxed_2119_ = lean_unbox(v_usedLetOnly_2107_);
v_skipConstInApp_boxed_2120_ = lean_unbox(v_skipConstInApp_2108_);
v_res_2121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2118_, v_inst_2102_, v_inst_2103_, v_inst_2104_, v_pre_2105_, v_post_2106_, v_usedLetOnly_boxed_2119_, v_skipConstInApp_boxed_2120_, v_x_2109_, v_x_2110_, v_args_2111_, v___x_2112_, v_toBind_2113_, v_toApplicative_2114_, v___f_2115_, v_f_2116_, v___y_2117_);
lean_dec(v___y_2117_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_pre_2126_, lean_object* v_post_2127_, uint8_t v_usedLetOnly_2128_, uint8_t v_skipConstInApp_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v___x_2132_, lean_object* v_toBind_2133_, lean_object* v_toApplicative_2134_, lean_object* v___f_2135_, lean_object* v_f_2136_, lean_object* v_args_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___f_2142_; lean_object* v___f_2143_; 
v___x_2139_ = lean_box(v_skipInstances_2122_);
v___x_2140_ = lean_box(v_usedLetOnly_2128_);
v___x_2141_ = lean_box(v_skipConstInApp_2129_);
lean_inc_ref(v_toApplicative_2134_);
lean_inc(v_toBind_2133_);
lean_inc(v_x_2131_);
lean_inc(v_post_2127_);
lean_inc(v_pre_2126_);
lean_inc_ref(v_inst_2125_);
lean_inc(v_inst_2124_);
lean_inc_ref(v_inst_2123_);
v___f_2142_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2142_, 0, v___x_2139_);
lean_closure_set(v___f_2142_, 1, v_inst_2123_);
lean_closure_set(v___f_2142_, 2, v_inst_2124_);
lean_closure_set(v___f_2142_, 3, v_inst_2125_);
lean_closure_set(v___f_2142_, 4, v_pre_2126_);
lean_closure_set(v___f_2142_, 5, v_post_2127_);
lean_closure_set(v___f_2142_, 6, v___x_2140_);
lean_closure_set(v___f_2142_, 7, v___x_2141_);
lean_closure_set(v___f_2142_, 8, v_x_2130_);
lean_closure_set(v___f_2142_, 9, v_x_2131_);
lean_closure_set(v___f_2142_, 10, v_args_2137_);
lean_closure_set(v___f_2142_, 11, v___x_2132_);
lean_closure_set(v___f_2142_, 12, v_toBind_2133_);
lean_closure_set(v___f_2142_, 13, v_toApplicative_2134_);
lean_closure_set(v___f_2142_, 14, v___f_2135_);
lean_inc(v___y_2138_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2143_, 0, v___f_2142_);
lean_closure_set(v___f_2143_, 1, v___y_2138_);
if (v_skipConstInApp_2129_ == 0)
{
lean_dec_ref(v_toApplicative_2134_);
goto v___jp_2144_;
}
else
{
uint8_t v___x_2147_; 
v___x_2147_ = l_Lean_Expr_isConst(v_f_2136_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v_toApplicative_2134_);
goto v___jp_2144_;
}
else
{
lean_object* v_toPure_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec(v_x_2131_);
lean_dec(v_post_2127_);
lean_dec(v_pre_2126_);
lean_dec_ref(v_inst_2125_);
lean_dec(v_inst_2124_);
lean_dec_ref(v_inst_2123_);
v_toPure_2148_ = lean_ctor_get(v_toApplicative_2134_, 1);
lean_inc(v_toPure_2148_);
lean_dec_ref(v_toApplicative_2134_);
v___x_2149_ = lean_apply_2(v_toPure_2148_, lean_box(0), v_f_2136_);
v___x_2150_ = lean_apply_4(v_toBind_2133_, lean_box(0), lean_box(0), v___x_2149_, v___f_2143_);
return v___x_2150_;
}
}
v___jp_2144_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2123_, v_inst_2124_, v_inst_2125_, v_pre_2126_, v_post_2127_, v_usedLetOnly_2128_, v_skipConstInApp_2129_, v_skipInstances_2122_, v_x_2130_, v_x_2131_, v_f_2136_, v___y_2138_);
v___x_2146_ = lean_apply_4(v_toBind_2133_, lean_box(0), lean_box(0), v___x_2145_, v___f_2143_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2151_ = _args[0];
lean_object* v_inst_2152_ = _args[1];
lean_object* v_inst_2153_ = _args[2];
lean_object* v_inst_2154_ = _args[3];
lean_object* v_pre_2155_ = _args[4];
lean_object* v_post_2156_ = _args[5];
lean_object* v_usedLetOnly_2157_ = _args[6];
lean_object* v_skipConstInApp_2158_ = _args[7];
lean_object* v_x_2159_ = _args[8];
lean_object* v_x_2160_ = _args[9];
lean_object* v___x_2161_ = _args[10];
lean_object* v_toBind_2162_ = _args[11];
lean_object* v_toApplicative_2163_ = _args[12];
lean_object* v___f_2164_ = _args[13];
lean_object* v_f_2165_ = _args[14];
lean_object* v_args_2166_ = _args[15];
lean_object* v___y_2167_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2168_; uint8_t v_usedLetOnly_boxed_2169_; uint8_t v_skipConstInApp_boxed_2170_; lean_object* v_res_2171_; 
v_skipInstances_boxed_2168_ = lean_unbox(v_skipInstances_2151_);
v_usedLetOnly_boxed_2169_ = lean_unbox(v_usedLetOnly_2157_);
v_skipConstInApp_boxed_2170_ = lean_unbox(v_skipConstInApp_2158_);
v_res_2171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2168_, v_inst_2152_, v_inst_2153_, v_inst_2154_, v_pre_2155_, v_post_2156_, v_usedLetOnly_boxed_2169_, v_skipConstInApp_boxed_2170_, v_x_2159_, v_x_2160_, v___x_2161_, v_toBind_2162_, v_toApplicative_2163_, v___f_2164_, v_f_2165_, v_args_2166_, v___y_2167_);
lean_dec(v___y_2167_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_pre_2178_, lean_object* v_post_2179_, uint8_t v_usedLetOnly_2180_, uint8_t v_skipConstInApp_2181_, uint8_t v_skipInstances_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_, lean_object* v_body_2185_, lean_object* v_x_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_array_push(v_fvars_2174_, v_x_2186_);
v___x_2189_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2175_, v_inst_2176_, v_inst_2177_, v_pre_2178_, v_post_2179_, v_usedLetOnly_2180_, v_skipConstInApp_2181_, v_skipInstances_2182_, v_x_2183_, v_x_2184_, v___x_2188_, v_body_2185_, v___y_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v_pre_2194_, lean_object* v_post_2195_, lean_object* v_usedLetOnly_2196_, lean_object* v_skipConstInApp_2197_, lean_object* v_skipInstances_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_, lean_object* v_body_2201_, lean_object* v_x_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v_usedLetOnly_boxed_2204_; uint8_t v_skipConstInApp_boxed_2205_; uint8_t v_skipInstances_boxed_2206_; lean_object* v_res_2207_; 
v_usedLetOnly_boxed_2204_ = lean_unbox(v_usedLetOnly_2196_);
v_skipConstInApp_boxed_2205_ = lean_unbox(v_skipConstInApp_2197_);
v_skipInstances_boxed_2206_ = lean_unbox(v_skipInstances_2198_);
v_res_2207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2190_, v_inst_2191_, v_inst_2192_, v_inst_2193_, v_pre_2194_, v_post_2195_, v_usedLetOnly_boxed_2204_, v_skipConstInApp_boxed_2205_, v_skipInstances_boxed_2206_, v_x_2199_, v_x_2200_, v_body_2201_, v_x_2202_, v___y_2203_);
lean_dec(v___y_2203_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_pre_2211_, lean_object* v_post_2212_, lean_object* v_usedLetOnly_2213_, lean_object* v_skipConstInApp_2214_, lean_object* v_skipInstances_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
uint8_t v_usedLetOnly_boxed_2220_; uint8_t v_skipConstInApp_boxed_2221_; uint8_t v_skipInstances_boxed_2222_; lean_object* v_res_2223_; 
v_usedLetOnly_boxed_2220_ = lean_unbox(v_usedLetOnly_2213_);
v_skipConstInApp_boxed_2221_ = lean_unbox(v_skipConstInApp_2214_);
v_skipInstances_boxed_2222_ = lean_unbox(v_skipInstances_2215_);
v_res_2223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2208_, v_inst_2209_, v_inst_2210_, v_pre_2211_, v_post_2212_, v_usedLetOnly_boxed_2220_, v_skipConstInApp_boxed_2221_, v_skipInstances_boxed_2222_, v_x_2216_, v_x_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2218_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_pre_2227_, lean_object* v_post_2228_, uint8_t v_usedLetOnly_2229_, uint8_t v_skipConstInApp_2230_, uint8_t v_skipInstances_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_fvars_2234_, lean_object* v_e_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___x_2243_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2224_);
v___x_2239_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2232_, v___x_2237_, v___x_2238_, v_inst_2224_);
v___x_2240_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2232_, v___x_2237_, v___x_2238_);
lean_inc_ref_n(v_inst_2226_, 2);
lean_inc_ref(v___x_2240_);
v___f_2241_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2241_, 0, v___x_2240_);
lean_closure_set(v___f_2241_, 1, v_inst_2226_);
v___f_2242_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2242_, 0, v___x_2240_);
lean_closure_set(v___f_2242_, 1, v_inst_2226_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___f_2241_);
lean_ctor_set(v___x_2243_, 1, v___f_2242_);
if (lean_obj_tag(v_e_2235_) == 7)
{
lean_object* v_binderName_2244_; lean_object* v_binderType_2245_; lean_object* v_body_2246_; uint8_t v_binderInfo_2247_; lean_object* v_toBind_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_binderName_2244_ = lean_ctor_get(v_e_2235_, 0);
lean_inc(v_binderName_2244_);
v_binderType_2245_ = lean_ctor_get(v_e_2235_, 1);
lean_inc_ref(v_binderType_2245_);
v_body_2246_ = lean_ctor_get(v_e_2235_, 2);
lean_inc_ref(v_body_2246_);
v_binderInfo_2247_ = lean_ctor_get_uint8(v_e_2235_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2235_);
v_toBind_2248_ = lean_ctor_get(v_inst_2224_, 1);
lean_inc(v_toBind_2248_);
v___x_2249_ = lean_box(v_usedLetOnly_2229_);
v___x_2250_ = lean_box(v_skipConstInApp_2230_);
v___x_2251_ = lean_box(v_skipInstances_2231_);
lean_inc(v_x_2233_);
lean_inc(v_post_2228_);
lean_inc(v_pre_2227_);
lean_inc_ref(v_inst_2226_);
lean_inc(v_inst_2225_);
lean_inc_ref(v_inst_2224_);
lean_inc_ref(v_fvars_2234_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2252_, 0, v_fvars_2234_);
lean_closure_set(v___f_2252_, 1, v_inst_2224_);
lean_closure_set(v___f_2252_, 2, v_inst_2225_);
lean_closure_set(v___f_2252_, 3, v_inst_2226_);
lean_closure_set(v___f_2252_, 4, v_pre_2227_);
lean_closure_set(v___f_2252_, 5, v_post_2228_);
lean_closure_set(v___f_2252_, 6, v___x_2249_);
lean_closure_set(v___f_2252_, 7, v___x_2250_);
lean_closure_set(v___f_2252_, 8, v___x_2251_);
lean_closure_set(v___f_2252_, 9, v_x_2232_);
lean_closure_set(v___f_2252_, 10, v_x_2233_);
lean_closure_set(v___f_2252_, 11, v_body_2246_);
v___x_2253_ = lean_box(v_binderInfo_2247_);
lean_inc(v_a_2236_);
v___f_2254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2254_, 0, v___x_2243_);
lean_closure_set(v___f_2254_, 1, v___x_2239_);
lean_closure_set(v___f_2254_, 2, v_binderName_2244_);
lean_closure_set(v___f_2254_, 3, v___x_2253_);
lean_closure_set(v___f_2254_, 4, v___f_2252_);
lean_closure_set(v___f_2254_, 5, v_a_2236_);
v___x_2255_ = lean_expr_instantiate_rev(v_binderType_2245_, v_fvars_2234_);
lean_dec_ref(v_fvars_2234_);
lean_dec_ref(v_binderType_2245_);
v___x_2256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2224_, v_inst_2225_, v_inst_2226_, v_pre_2227_, v_post_2228_, v_usedLetOnly_2229_, v_skipConstInApp_2230_, v_skipInstances_2231_, v_x_2232_, v_x_2233_, v___x_2255_, v_a_2236_);
v___x_2257_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2256_, v___f_2254_);
return v___x_2257_;
}
else
{
lean_object* v_toBind_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___x_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2239_);
v_toBind_2258_ = lean_ctor_get(v_inst_2224_, 1);
lean_inc_n(v_toBind_2258_, 2);
v___x_2259_ = lean_box(v_usedLetOnly_2229_);
v___x_2260_ = lean_box(v_skipConstInApp_2230_);
v___x_2261_ = lean_box(v_skipInstances_2231_);
lean_inc(v_a_2236_);
lean_inc(v_x_2233_);
lean_inc(v_post_2228_);
lean_inc(v_pre_2227_);
lean_inc_ref(v_inst_2226_);
lean_inc_n(v_inst_2225_, 2);
lean_inc_ref(v_inst_2224_);
v___f_2262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2262_, 0, v_inst_2224_);
lean_closure_set(v___f_2262_, 1, v_inst_2225_);
lean_closure_set(v___f_2262_, 2, v_inst_2226_);
lean_closure_set(v___f_2262_, 3, v_pre_2227_);
lean_closure_set(v___f_2262_, 4, v_post_2228_);
lean_closure_set(v___f_2262_, 5, v___x_2259_);
lean_closure_set(v___f_2262_, 6, v___x_2260_);
lean_closure_set(v___f_2262_, 7, v___x_2261_);
lean_closure_set(v___f_2262_, 8, v_x_2232_);
lean_closure_set(v___f_2262_, 9, v_x_2233_);
lean_closure_set(v___f_2262_, 10, v_a_2236_);
v___x_2263_ = lean_box(v_usedLetOnly_2229_);
lean_inc_ref(v_fvars_2234_);
v___f_2264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2264_, 0, v_fvars_2234_);
lean_closure_set(v___f_2264_, 1, v___x_2263_);
lean_closure_set(v___f_2264_, 2, v_inst_2225_);
lean_closure_set(v___f_2264_, 3, v_toBind_2258_);
lean_closure_set(v___f_2264_, 4, v___f_2262_);
v___x_2265_ = lean_expr_instantiate_rev(v_e_2235_, v_fvars_2234_);
lean_dec_ref(v_fvars_2234_);
lean_dec_ref(v_e_2235_);
v___x_2266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2224_, v_inst_2225_, v_inst_2226_, v_pre_2227_, v_post_2228_, v_usedLetOnly_2229_, v_skipConstInApp_2230_, v_skipInstances_2231_, v_x_2232_, v_x_2233_, v___x_2265_, v_a_2236_);
v___x_2267_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2266_, v___f_2264_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_pre_2272_, lean_object* v_post_2273_, uint8_t v_usedLetOnly_2274_, uint8_t v_skipConstInApp_2275_, uint8_t v_skipInstances_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_, lean_object* v_body_2279_, lean_object* v_x_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_array_push(v_fvars_2268_, v_x_2280_);
v___x_2283_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2269_, v_inst_2270_, v_inst_2271_, v_pre_2272_, v_post_2273_, v_usedLetOnly_2274_, v_skipConstInApp_2275_, v_skipInstances_2276_, v_x_2277_, v_x_2278_, v___x_2282_, v_body_2279_, v___y_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_pre_2288_, lean_object* v_post_2289_, lean_object* v_usedLetOnly_2290_, lean_object* v_skipConstInApp_2291_, lean_object* v_skipInstances_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_, lean_object* v_body_2295_, lean_object* v_x_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v_usedLetOnly_boxed_2298_; uint8_t v_skipConstInApp_boxed_2299_; uint8_t v_skipInstances_boxed_2300_; lean_object* v_res_2301_; 
v_usedLetOnly_boxed_2298_ = lean_unbox(v_usedLetOnly_2290_);
v_skipConstInApp_boxed_2299_ = lean_unbox(v_skipConstInApp_2291_);
v_skipInstances_boxed_2300_ = lean_unbox(v_skipInstances_2292_);
v_res_2301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2284_, v_inst_2285_, v_inst_2286_, v_inst_2287_, v_pre_2288_, v_post_2289_, v_usedLetOnly_boxed_2298_, v_skipConstInApp_boxed_2299_, v_skipInstances_boxed_2300_, v_x_2293_, v_x_2294_, v_body_2295_, v_x_2296_, v___y_2297_);
lean_dec(v___y_2297_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_pre_2305_, lean_object* v_post_2306_, uint8_t v_usedLetOnly_2307_, uint8_t v_skipConstInApp_2308_, uint8_t v_skipInstances_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_fvars_2312_, lean_object* v_e_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; lean_object* v___f_2320_; lean_object* v___x_2321_; 
v___x_2315_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2302_);
v___x_2317_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2310_, v___x_2315_, v___x_2316_, v_inst_2302_);
v___x_2318_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2310_, v___x_2315_, v___x_2316_);
lean_inc_ref_n(v_inst_2304_, 2);
lean_inc_ref(v___x_2318_);
v___f_2319_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2319_, 0, v___x_2318_);
lean_closure_set(v___f_2319_, 1, v_inst_2304_);
v___f_2320_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2320_, 0, v___x_2318_);
lean_closure_set(v___f_2320_, 1, v_inst_2304_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___f_2319_);
lean_ctor_set(v___x_2321_, 1, v___f_2320_);
if (lean_obj_tag(v_e_2313_) == 6)
{
lean_object* v_binderName_2322_; lean_object* v_binderType_2323_; lean_object* v_body_2324_; uint8_t v_binderInfo_2325_; lean_object* v_toBind_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_binderName_2322_ = lean_ctor_get(v_e_2313_, 0);
lean_inc(v_binderName_2322_);
v_binderType_2323_ = lean_ctor_get(v_e_2313_, 1);
lean_inc_ref(v_binderType_2323_);
v_body_2324_ = lean_ctor_get(v_e_2313_, 2);
lean_inc_ref(v_body_2324_);
v_binderInfo_2325_ = lean_ctor_get_uint8(v_e_2313_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2313_);
v_toBind_2326_ = lean_ctor_get(v_inst_2302_, 1);
lean_inc(v_toBind_2326_);
v___x_2327_ = lean_box(v_usedLetOnly_2307_);
v___x_2328_ = lean_box(v_skipConstInApp_2308_);
v___x_2329_ = lean_box(v_skipInstances_2309_);
lean_inc(v_x_2311_);
lean_inc(v_post_2306_);
lean_inc(v_pre_2305_);
lean_inc_ref(v_inst_2304_);
lean_inc(v_inst_2303_);
lean_inc_ref(v_inst_2302_);
lean_inc_ref(v_fvars_2312_);
v___f_2330_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2330_, 0, v_fvars_2312_);
lean_closure_set(v___f_2330_, 1, v_inst_2302_);
lean_closure_set(v___f_2330_, 2, v_inst_2303_);
lean_closure_set(v___f_2330_, 3, v_inst_2304_);
lean_closure_set(v___f_2330_, 4, v_pre_2305_);
lean_closure_set(v___f_2330_, 5, v_post_2306_);
lean_closure_set(v___f_2330_, 6, v___x_2327_);
lean_closure_set(v___f_2330_, 7, v___x_2328_);
lean_closure_set(v___f_2330_, 8, v___x_2329_);
lean_closure_set(v___f_2330_, 9, v_x_2310_);
lean_closure_set(v___f_2330_, 10, v_x_2311_);
lean_closure_set(v___f_2330_, 11, v_body_2324_);
v___x_2331_ = lean_box(v_binderInfo_2325_);
lean_inc(v_a_2314_);
v___f_2332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2332_, 0, v___x_2321_);
lean_closure_set(v___f_2332_, 1, v___x_2317_);
lean_closure_set(v___f_2332_, 2, v_binderName_2322_);
lean_closure_set(v___f_2332_, 3, v___x_2331_);
lean_closure_set(v___f_2332_, 4, v___f_2330_);
lean_closure_set(v___f_2332_, 5, v_a_2314_);
v___x_2333_ = lean_expr_instantiate_rev(v_binderType_2323_, v_fvars_2312_);
lean_dec_ref(v_fvars_2312_);
lean_dec_ref(v_binderType_2323_);
v___x_2334_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2302_, v_inst_2303_, v_inst_2304_, v_pre_2305_, v_post_2306_, v_usedLetOnly_2307_, v_skipConstInApp_2308_, v_skipInstances_2309_, v_x_2310_, v_x_2311_, v___x_2333_, v_a_2314_);
v___x_2335_ = lean_apply_4(v_toBind_2326_, lean_box(0), lean_box(0), v___x_2334_, v___f_2332_);
return v___x_2335_;
}
else
{
lean_object* v_toBind_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec_ref(v___x_2321_);
lean_dec_ref(v___x_2317_);
v_toBind_2336_ = lean_ctor_get(v_inst_2302_, 1);
lean_inc_n(v_toBind_2336_, 2);
v___x_2337_ = lean_box(v_usedLetOnly_2307_);
v___x_2338_ = lean_box(v_skipConstInApp_2308_);
v___x_2339_ = lean_box(v_skipInstances_2309_);
lean_inc(v_a_2314_);
lean_inc(v_x_2311_);
lean_inc(v_post_2306_);
lean_inc(v_pre_2305_);
lean_inc_ref(v_inst_2304_);
lean_inc_n(v_inst_2303_, 2);
lean_inc_ref(v_inst_2302_);
v___f_2340_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2340_, 0, v_inst_2302_);
lean_closure_set(v___f_2340_, 1, v_inst_2303_);
lean_closure_set(v___f_2340_, 2, v_inst_2304_);
lean_closure_set(v___f_2340_, 3, v_pre_2305_);
lean_closure_set(v___f_2340_, 4, v_post_2306_);
lean_closure_set(v___f_2340_, 5, v___x_2337_);
lean_closure_set(v___f_2340_, 6, v___x_2338_);
lean_closure_set(v___f_2340_, 7, v___x_2339_);
lean_closure_set(v___f_2340_, 8, v_x_2310_);
lean_closure_set(v___f_2340_, 9, v_x_2311_);
lean_closure_set(v___f_2340_, 10, v_a_2314_);
v___x_2341_ = lean_box(v_usedLetOnly_2307_);
lean_inc_ref(v_fvars_2312_);
v___f_2342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2342_, 0, v_fvars_2312_);
lean_closure_set(v___f_2342_, 1, v___x_2341_);
lean_closure_set(v___f_2342_, 2, v_inst_2303_);
lean_closure_set(v___f_2342_, 3, v_toBind_2336_);
lean_closure_set(v___f_2342_, 4, v___f_2340_);
v___x_2343_ = lean_expr_instantiate_rev(v_e_2313_, v_fvars_2312_);
lean_dec_ref(v_fvars_2312_);
lean_dec_ref(v_e_2313_);
v___x_2344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2302_, v_inst_2303_, v_inst_2304_, v_pre_2305_, v_post_2306_, v_usedLetOnly_2307_, v_skipConstInApp_2308_, v_skipInstances_2309_, v_x_2310_, v_x_2311_, v___x_2343_, v_a_2314_);
v___x_2345_ = lean_apply_4(v_toBind_2336_, lean_box(0), lean_box(0), v___x_2344_, v___f_2342_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_pre_2350_, lean_object* v_post_2351_, uint8_t v_usedLetOnly_2352_, uint8_t v_skipConstInApp_2353_, uint8_t v_skipInstances_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_, lean_object* v_body_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_array_push(v_fvars_2346_, v_x_2358_);
v___x_2361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2347_, v_inst_2348_, v_inst_2349_, v_pre_2350_, v_post_2351_, v_usedLetOnly_2352_, v_skipConstInApp_2353_, v_skipInstances_2354_, v_x_2355_, v_x_2356_, v___x_2360_, v_body_2357_, v___y_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_pre_2366_, lean_object* v_post_2367_, lean_object* v_usedLetOnly_2368_, lean_object* v_skipConstInApp_2369_, lean_object* v_skipInstances_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_body_2373_, lean_object* v_x_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_usedLetOnly_boxed_2376_; uint8_t v_skipConstInApp_boxed_2377_; uint8_t v_skipInstances_boxed_2378_; lean_object* v_res_2379_; 
v_usedLetOnly_boxed_2376_ = lean_unbox(v_usedLetOnly_2368_);
v_skipConstInApp_boxed_2377_ = lean_unbox(v_skipConstInApp_2369_);
v_skipInstances_boxed_2378_ = lean_unbox(v_skipInstances_2370_);
v_res_2379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2362_, v_inst_2363_, v_inst_2364_, v_inst_2365_, v_pre_2366_, v_post_2367_, v_usedLetOnly_boxed_2376_, v_skipConstInApp_boxed_2377_, v_skipInstances_boxed_2378_, v_x_2371_, v_x_2372_, v_body_2373_, v_x_2374_, v___y_2375_);
lean_dec(v___y_2375_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v_declName_2382_, lean_object* v___f_2383_, uint8_t v_nondep_2384_, lean_object* v_a_2385_, lean_object* v_value_2386_, lean_object* v_fvars_2387_, lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_pre_2391_, lean_object* v_post_2392_, uint8_t v_usedLetOnly_2393_, uint8_t v_skipConstInApp_2394_, uint8_t v_skipInstances_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_toBind_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2400_ = lean_box(v_nondep_2384_);
lean_inc(v_a_2385_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2401_, 0, v___x_2380_);
lean_closure_set(v___f_2401_, 1, v___x_2381_);
lean_closure_set(v___f_2401_, 2, v_declName_2382_);
lean_closure_set(v___f_2401_, 3, v_a_2399_);
lean_closure_set(v___f_2401_, 4, v___f_2383_);
lean_closure_set(v___f_2401_, 5, v___x_2400_);
lean_closure_set(v___f_2401_, 6, v_a_2385_);
v___x_2402_ = lean_expr_instantiate_rev(v_value_2386_, v_fvars_2387_);
v___x_2403_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2388_, v_inst_2389_, v_inst_2390_, v_pre_2391_, v_post_2392_, v_usedLetOnly_2393_, v_skipConstInApp_2394_, v_skipInstances_2395_, v_x_2396_, v_x_2397_, v___x_2402_, v_a_2385_);
v___x_2404_ = lean_apply_4(v_toBind_2398_, lean_box(0), lean_box(0), v___x_2403_, v___f_2401_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2405_ = _args[0];
lean_object* v___x_2406_ = _args[1];
lean_object* v_declName_2407_ = _args[2];
lean_object* v___f_2408_ = _args[3];
lean_object* v_nondep_2409_ = _args[4];
lean_object* v_a_2410_ = _args[5];
lean_object* v_value_2411_ = _args[6];
lean_object* v_fvars_2412_ = _args[7];
lean_object* v_inst_2413_ = _args[8];
lean_object* v_inst_2414_ = _args[9];
lean_object* v_inst_2415_ = _args[10];
lean_object* v_pre_2416_ = _args[11];
lean_object* v_post_2417_ = _args[12];
lean_object* v_usedLetOnly_2418_ = _args[13];
lean_object* v_skipConstInApp_2419_ = _args[14];
lean_object* v_skipInstances_2420_ = _args[15];
lean_object* v_x_2421_ = _args[16];
lean_object* v_x_2422_ = _args[17];
lean_object* v_toBind_2423_ = _args[18];
lean_object* v_a_2424_ = _args[19];
_start:
{
uint8_t v_nondep_4049__boxed_2425_; uint8_t v_usedLetOnly_boxed_2426_; uint8_t v_skipConstInApp_boxed_2427_; uint8_t v_skipInstances_boxed_2428_; lean_object* v_res_2429_; 
v_nondep_4049__boxed_2425_ = lean_unbox(v_nondep_2409_);
v_usedLetOnly_boxed_2426_ = lean_unbox(v_usedLetOnly_2418_);
v_skipConstInApp_boxed_2427_ = lean_unbox(v_skipConstInApp_2419_);
v_skipInstances_boxed_2428_ = lean_unbox(v_skipInstances_2420_);
v_res_2429_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2405_, v___x_2406_, v_declName_2407_, v___f_2408_, v_nondep_4049__boxed_2425_, v_a_2410_, v_value_2411_, v_fvars_2412_, v_inst_2413_, v_inst_2414_, v_inst_2415_, v_pre_2416_, v_post_2417_, v_usedLetOnly_boxed_2426_, v_skipConstInApp_boxed_2427_, v_skipInstances_boxed_2428_, v_x_2421_, v_x_2422_, v_toBind_2423_, v_a_2424_);
lean_dec_ref(v_fvars_2412_);
lean_dec_ref(v_value_2411_);
lean_dec(v_a_2410_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_pre_2433_, lean_object* v_post_2434_, uint8_t v_usedLetOnly_2435_, uint8_t v_skipConstInApp_2436_, uint8_t v_skipInstances_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_, lean_object* v_fvars_2440_, lean_object* v_e_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; 
v___x_2443_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2430_);
v___x_2445_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2438_, v___x_2443_, v___x_2444_, v_inst_2430_);
v___x_2446_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2438_, v___x_2443_, v___x_2444_);
lean_inc_ref_n(v_inst_2432_, 2);
lean_inc_ref(v___x_2446_);
v___f_2447_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2447_, 0, v___x_2446_);
lean_closure_set(v___f_2447_, 1, v_inst_2432_);
v___f_2448_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2448_, 0, v___x_2446_);
lean_closure_set(v___f_2448_, 1, v_inst_2432_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___f_2447_);
lean_ctor_set(v___x_2449_, 1, v___f_2448_);
if (lean_obj_tag(v_e_2441_) == 8)
{
lean_object* v_declName_2450_; lean_object* v_type_2451_; lean_object* v_value_2452_; lean_object* v_body_2453_; uint8_t v_nondep_2454_; lean_object* v_toBind_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_declName_2450_ = lean_ctor_get(v_e_2441_, 0);
lean_inc(v_declName_2450_);
v_type_2451_ = lean_ctor_get(v_e_2441_, 1);
lean_inc_ref(v_type_2451_);
v_value_2452_ = lean_ctor_get(v_e_2441_, 2);
lean_inc_ref(v_value_2452_);
v_body_2453_ = lean_ctor_get(v_e_2441_, 3);
lean_inc_ref(v_body_2453_);
v_nondep_2454_ = lean_ctor_get_uint8(v_e_2441_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2441_);
v_toBind_2455_ = lean_ctor_get(v_inst_2430_, 1);
lean_inc_n(v_toBind_2455_, 2);
v___x_2456_ = lean_box(v_usedLetOnly_2435_);
v___x_2457_ = lean_box(v_skipConstInApp_2436_);
v___x_2458_ = lean_box(v_skipInstances_2437_);
lean_inc_n(v_x_2439_, 2);
lean_inc_n(v_post_2434_, 2);
lean_inc_n(v_pre_2433_, 2);
lean_inc_ref_n(v_inst_2432_, 2);
lean_inc_n(v_inst_2431_, 2);
lean_inc_ref_n(v_inst_2430_, 2);
lean_inc_ref_n(v_fvars_2440_, 2);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2459_, 0, v_fvars_2440_);
lean_closure_set(v___f_2459_, 1, v_inst_2430_);
lean_closure_set(v___f_2459_, 2, v_inst_2431_);
lean_closure_set(v___f_2459_, 3, v_inst_2432_);
lean_closure_set(v___f_2459_, 4, v_pre_2433_);
lean_closure_set(v___f_2459_, 5, v_post_2434_);
lean_closure_set(v___f_2459_, 6, v___x_2456_);
lean_closure_set(v___f_2459_, 7, v___x_2457_);
lean_closure_set(v___f_2459_, 8, v___x_2458_);
lean_closure_set(v___f_2459_, 9, v_x_2438_);
lean_closure_set(v___f_2459_, 10, v_x_2439_);
lean_closure_set(v___f_2459_, 11, v_body_2453_);
v___x_2460_ = lean_box(v_nondep_2454_);
v___x_2461_ = lean_box(v_usedLetOnly_2435_);
v___x_2462_ = lean_box(v_skipConstInApp_2436_);
v___x_2463_ = lean_box(v_skipInstances_2437_);
lean_inc(v_a_2442_);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2464_, 0, v___x_2449_);
lean_closure_set(v___f_2464_, 1, v___x_2445_);
lean_closure_set(v___f_2464_, 2, v_declName_2450_);
lean_closure_set(v___f_2464_, 3, v___f_2459_);
lean_closure_set(v___f_2464_, 4, v___x_2460_);
lean_closure_set(v___f_2464_, 5, v_a_2442_);
lean_closure_set(v___f_2464_, 6, v_value_2452_);
lean_closure_set(v___f_2464_, 7, v_fvars_2440_);
lean_closure_set(v___f_2464_, 8, v_inst_2430_);
lean_closure_set(v___f_2464_, 9, v_inst_2431_);
lean_closure_set(v___f_2464_, 10, v_inst_2432_);
lean_closure_set(v___f_2464_, 11, v_pre_2433_);
lean_closure_set(v___f_2464_, 12, v_post_2434_);
lean_closure_set(v___f_2464_, 13, v___x_2461_);
lean_closure_set(v___f_2464_, 14, v___x_2462_);
lean_closure_set(v___f_2464_, 15, v___x_2463_);
lean_closure_set(v___f_2464_, 16, v_x_2438_);
lean_closure_set(v___f_2464_, 17, v_x_2439_);
lean_closure_set(v___f_2464_, 18, v_toBind_2455_);
v___x_2465_ = lean_expr_instantiate_rev(v_type_2451_, v_fvars_2440_);
lean_dec_ref(v_fvars_2440_);
lean_dec_ref(v_type_2451_);
v___x_2466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2430_, v_inst_2431_, v_inst_2432_, v_pre_2433_, v_post_2434_, v_usedLetOnly_2435_, v_skipConstInApp_2436_, v_skipInstances_2437_, v_x_2438_, v_x_2439_, v___x_2465_, v_a_2442_);
v___x_2467_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v___x_2466_, v___f_2464_);
return v___x_2467_;
}
else
{
lean_object* v_toBind_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec_ref(v___x_2449_);
lean_dec_ref(v___x_2445_);
v_toBind_2468_ = lean_ctor_get(v_inst_2430_, 1);
lean_inc_n(v_toBind_2468_, 2);
v___x_2469_ = lean_box(v_usedLetOnly_2435_);
v___x_2470_ = lean_box(v_skipConstInApp_2436_);
v___x_2471_ = lean_box(v_skipInstances_2437_);
lean_inc(v_a_2442_);
lean_inc(v_x_2439_);
lean_inc(v_post_2434_);
lean_inc(v_pre_2433_);
lean_inc_ref(v_inst_2432_);
lean_inc_n(v_inst_2431_, 2);
lean_inc_ref(v_inst_2430_);
v___f_2472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2472_, 0, v_inst_2430_);
lean_closure_set(v___f_2472_, 1, v_inst_2431_);
lean_closure_set(v___f_2472_, 2, v_inst_2432_);
lean_closure_set(v___f_2472_, 3, v_pre_2433_);
lean_closure_set(v___f_2472_, 4, v_post_2434_);
lean_closure_set(v___f_2472_, 5, v___x_2469_);
lean_closure_set(v___f_2472_, 6, v___x_2470_);
lean_closure_set(v___f_2472_, 7, v___x_2471_);
lean_closure_set(v___f_2472_, 8, v_x_2438_);
lean_closure_set(v___f_2472_, 9, v_x_2439_);
lean_closure_set(v___f_2472_, 10, v_a_2442_);
v___x_2473_ = lean_box(v_usedLetOnly_2435_);
lean_inc_ref(v_fvars_2440_);
v___f_2474_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2474_, 0, v_fvars_2440_);
lean_closure_set(v___f_2474_, 1, v___x_2473_);
lean_closure_set(v___f_2474_, 2, v_inst_2431_);
lean_closure_set(v___f_2474_, 3, v_toBind_2468_);
lean_closure_set(v___f_2474_, 4, v___f_2472_);
v___x_2475_ = lean_expr_instantiate_rev(v_e_2441_, v_fvars_2440_);
lean_dec_ref(v_fvars_2440_);
lean_dec_ref(v_e_2441_);
v___x_2476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2430_, v_inst_2431_, v_inst_2432_, v_pre_2433_, v_post_2434_, v_usedLetOnly_2435_, v_skipConstInApp_2436_, v_skipInstances_2437_, v_x_2438_, v_x_2439_, v___x_2475_, v_a_2442_);
v___x_2477_ = lean_apply_4(v_toBind_2468_, lean_box(0), lean_box(0), v___x_2476_, v___f_2474_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2478_, lean_object* v_data_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_pre_2483_, lean_object* v_post_2484_, uint8_t v_usedLetOnly_2485_, uint8_t v_skipConstInApp_2486_, uint8_t v_skipInstances_2487_, lean_object* v_x_2488_, lean_object* v_x_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v_a_2492_){
_start:
{
size_t v___x_2493_; size_t v___x_2494_; uint8_t v___x_2495_; 
v___x_2493_ = lean_ptr_addr(v_expr_2478_);
v___x_2494_ = lean_ptr_addr(v_a_2492_);
v___x_2495_ = lean_usize_dec_eq(v___x_2493_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_dec_ref(v___y_2491_);
v___x_2496_ = l_Lean_Expr_mdata___override(v_data_2479_, v_a_2492_);
v___x_2497_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2480_, v_inst_2481_, v_inst_2482_, v_pre_2483_, v_post_2484_, v_usedLetOnly_2485_, v_skipConstInApp_2486_, v_skipInstances_2487_, v_x_2488_, v_x_2489_, v___x_2496_, v___y_2490_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; 
lean_dec_ref(v_a_2492_);
lean_dec(v_data_2479_);
v___x_2498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2480_, v_inst_2481_, v_inst_2482_, v_pre_2483_, v_post_2484_, v_usedLetOnly_2485_, v_skipConstInApp_2486_, v_skipInstances_2487_, v_x_2488_, v_x_2489_, v___y_2491_, v___y_2490_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2499_, lean_object* v_data_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_pre_2504_, lean_object* v_post_2505_, lean_object* v_usedLetOnly_2506_, lean_object* v_skipConstInApp_2507_, lean_object* v_skipInstances_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v_a_2513_){
_start:
{
uint8_t v_usedLetOnly_boxed_2514_; uint8_t v_skipConstInApp_boxed_2515_; uint8_t v_skipInstances_boxed_2516_; lean_object* v_res_2517_; 
v_usedLetOnly_boxed_2514_ = lean_unbox(v_usedLetOnly_2506_);
v_skipConstInApp_boxed_2515_ = lean_unbox(v_skipConstInApp_2507_);
v_skipInstances_boxed_2516_ = lean_unbox(v_skipInstances_2508_);
v_res_2517_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2499_, v_data_2500_, v_inst_2501_, v_inst_2502_, v_inst_2503_, v_pre_2504_, v_post_2505_, v_usedLetOnly_boxed_2514_, v_skipConstInApp_boxed_2515_, v_skipInstances_boxed_2516_, v_x_2509_, v_x_2510_, v___y_2511_, v___y_2512_, v_a_2513_);
lean_dec(v___y_2511_);
lean_dec_ref(v_expr_2499_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2518_, lean_object* v_typeName_2519_, lean_object* v_idx_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_pre_2524_, lean_object* v_post_2525_, uint8_t v_usedLetOnly_2526_, uint8_t v_skipConstInApp_2527_, uint8_t v_skipInstances_2528_, lean_object* v_x_2529_, lean_object* v_x_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v_a_2533_){
_start:
{
size_t v___x_2534_; size_t v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_ptr_addr(v_struct_2518_);
v___x_2535_ = lean_ptr_addr(v_a_2533_);
v___x_2536_ = lean_usize_dec_eq(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec_ref(v___y_2532_);
v___x_2537_ = l_Lean_Expr_proj___override(v_typeName_2519_, v_idx_2520_, v_a_2533_);
v___x_2538_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2521_, v_inst_2522_, v_inst_2523_, v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2528_, v_x_2529_, v_x_2530_, v___x_2537_, v___y_2531_);
return v___x_2538_;
}
else
{
lean_object* v___x_2539_; 
lean_dec_ref(v_a_2533_);
lean_dec(v_idx_2520_);
lean_dec(v_typeName_2519_);
v___x_2539_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2521_, v_inst_2522_, v_inst_2523_, v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2528_, v_x_2529_, v_x_2530_, v___y_2532_, v___y_2531_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2540_, lean_object* v_typeName_2541_, lean_object* v_idx_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_pre_2546_, lean_object* v_post_2547_, lean_object* v_usedLetOnly_2548_, lean_object* v_skipConstInApp_2549_, lean_object* v_skipInstances_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v_a_2555_){
_start:
{
uint8_t v_usedLetOnly_boxed_2556_; uint8_t v_skipConstInApp_boxed_2557_; uint8_t v_skipInstances_boxed_2558_; lean_object* v_res_2559_; 
v_usedLetOnly_boxed_2556_ = lean_unbox(v_usedLetOnly_2548_);
v_skipConstInApp_boxed_2557_ = lean_unbox(v_skipConstInApp_2549_);
v_skipInstances_boxed_2558_ = lean_unbox(v_skipInstances_2550_);
v_res_2559_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2540_, v_typeName_2541_, v_idx_2542_, v_inst_2543_, v_inst_2544_, v_inst_2545_, v_pre_2546_, v_post_2547_, v_usedLetOnly_boxed_2556_, v_skipConstInApp_boxed_2557_, v_skipInstances_boxed_2558_, v_x_2551_, v_x_2552_, v___y_2553_, v___y_2554_, v_a_2555_);
lean_dec(v___y_2553_);
lean_dec_ref(v_struct_2540_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_pre_2564_, lean_object* v_post_2565_, uint8_t v_usedLetOnly_2566_, uint8_t v_skipConstInApp_2567_, uint8_t v_skipInstances_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v___f_2571_, lean_object* v_toBind_2572_, lean_object* v_e_2573_, lean_object* v_____do__lift_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___y_2577_; 
switch(lean_obj_tag(v_____do__lift_2574_))
{
case 0:
{
lean_object* v_e_2609_; lean_object* v_toPure_2610_; lean_object* v___x_2611_; 
lean_dec_ref(v_e_2573_);
lean_dec(v_toBind_2572_);
lean_dec(v___f_2571_);
lean_dec(v_x_2570_);
lean_dec(v_post_2565_);
lean_dec(v_pre_2564_);
lean_dec_ref(v_inst_2563_);
lean_dec(v_inst_2562_);
lean_dec_ref(v_inst_2561_);
v_e_2609_ = lean_ctor_get(v_____do__lift_2574_, 0);
lean_inc_ref(v_e_2609_);
lean_dec_ref(v_____do__lift_2574_);
v_toPure_2610_ = lean_ctor_get(v_toApplicative_2560_, 1);
lean_inc(v_toPure_2610_);
lean_dec_ref(v_toApplicative_2560_);
v___x_2611_ = lean_apply_2(v_toPure_2610_, lean_box(0), v_e_2609_);
return v___x_2611_;
}
case 1:
{
lean_object* v_e_2612_; lean_object* v___x_2613_; 
lean_dec_ref(v_e_2573_);
lean_dec(v_toBind_2572_);
lean_dec(v___f_2571_);
lean_dec_ref(v_toApplicative_2560_);
v_e_2612_ = lean_ctor_get(v_____do__lift_2574_, 0);
lean_inc_ref(v_e_2612_);
lean_dec_ref(v_____do__lift_2574_);
v___x_2613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v_e_2612_, v___y_2575_);
return v___x_2613_;
}
default: 
{
lean_object* v_e_x3f_2614_; 
lean_dec_ref(v_toApplicative_2560_);
v_e_x3f_2614_ = lean_ctor_get(v_____do__lift_2574_, 0);
lean_inc(v_e_x3f_2614_);
lean_dec_ref(v_____do__lift_2574_);
if (lean_obj_tag(v_e_x3f_2614_) == 0)
{
v___y_2577_ = v_e_2573_;
goto v___jp_2576_;
}
else
{
lean_object* v_val_2615_; 
lean_dec_ref(v_e_2573_);
v_val_2615_ = lean_ctor_get(v_e_x3f_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref(v_e_x3f_2614_);
v___y_2577_ = v_val_2615_;
goto v___jp_2576_;
}
}
}
v___jp_2576_:
{
switch(lean_obj_tag(v___y_2577_))
{
case 7:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v_toBind_2572_);
lean_dec(v___f_2571_);
v___x_2578_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v___x_2578_, v___y_2577_, v___y_2575_);
return v___x_2579_;
}
case 6:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v_toBind_2572_);
lean_dec(v___f_2571_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v___x_2580_, v___y_2577_, v___y_2575_);
return v___x_2581_;
}
case 8:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v_toBind_2572_);
lean_dec(v___f_2571_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2583_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v___x_2582_, v___y_2577_, v___y_2575_);
return v___x_2583_;
}
case 5:
{
lean_object* v_dummy_2584_; lean_object* v_nargs_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_3659__overap_2589_; lean_object* v___x_2590_; 
lean_dec(v_toBind_2572_);
lean_dec(v_x_2570_);
lean_dec(v_post_2565_);
lean_dec(v_pre_2564_);
lean_dec_ref(v_inst_2563_);
lean_dec(v_inst_2562_);
lean_dec_ref(v_inst_2561_);
v_dummy_2584_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2585_ = l_Lean_Expr_getAppNumArgs(v___y_2577_);
lean_inc(v_nargs_2585_);
v___x_2586_ = lean_mk_array(v_nargs_2585_, v_dummy_2584_);
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_nat_sub(v_nargs_2585_, v___x_2587_);
lean_dec(v_nargs_2585_);
v___x_3659__overap_2589_ = l_Lean_Expr_withAppAux___redArg(v___f_2571_, v___y_2577_, v___x_2586_, v___x_2588_);
lean_inc(v___y_2575_);
v___x_2590_ = lean_apply_1(v___x_3659__overap_2589_, v___y_2575_);
return v___x_2590_;
}
case 10:
{
lean_object* v_data_2591_; lean_object* v_expr_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v___f_2571_);
v_data_2591_ = lean_ctor_get(v___y_2577_, 0);
lean_inc(v_data_2591_);
v_expr_2592_ = lean_ctor_get(v___y_2577_, 1);
lean_inc_ref_n(v_expr_2592_, 2);
v___x_2593_ = lean_box(v_usedLetOnly_2566_);
v___x_2594_ = lean_box(v_skipConstInApp_2567_);
v___x_2595_ = lean_box(v_skipInstances_2568_);
lean_inc(v___y_2575_);
lean_inc(v_x_2570_);
lean_inc(v_post_2565_);
lean_inc(v_pre_2564_);
lean_inc_ref(v_inst_2563_);
lean_inc(v_inst_2562_);
lean_inc_ref(v_inst_2561_);
v___f_2596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2596_, 0, v_expr_2592_);
lean_closure_set(v___f_2596_, 1, v_data_2591_);
lean_closure_set(v___f_2596_, 2, v_inst_2561_);
lean_closure_set(v___f_2596_, 3, v_inst_2562_);
lean_closure_set(v___f_2596_, 4, v_inst_2563_);
lean_closure_set(v___f_2596_, 5, v_pre_2564_);
lean_closure_set(v___f_2596_, 6, v_post_2565_);
lean_closure_set(v___f_2596_, 7, v___x_2593_);
lean_closure_set(v___f_2596_, 8, v___x_2594_);
lean_closure_set(v___f_2596_, 9, v___x_2595_);
lean_closure_set(v___f_2596_, 10, v_x_2569_);
lean_closure_set(v___f_2596_, 11, v_x_2570_);
lean_closure_set(v___f_2596_, 12, v___y_2575_);
lean_closure_set(v___f_2596_, 13, v___y_2577_);
v___x_2597_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v_expr_2592_, v___y_2575_);
v___x_2598_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2597_, v___f_2596_);
return v___x_2598_;
}
case 11:
{
lean_object* v_typeName_2599_; lean_object* v_idx_2600_; lean_object* v_struct_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v___f_2571_);
v_typeName_2599_ = lean_ctor_get(v___y_2577_, 0);
lean_inc(v_typeName_2599_);
v_idx_2600_ = lean_ctor_get(v___y_2577_, 1);
lean_inc(v_idx_2600_);
v_struct_2601_ = lean_ctor_get(v___y_2577_, 2);
lean_inc_ref_n(v_struct_2601_, 2);
v___x_2602_ = lean_box(v_usedLetOnly_2566_);
v___x_2603_ = lean_box(v_skipConstInApp_2567_);
v___x_2604_ = lean_box(v_skipInstances_2568_);
lean_inc(v___y_2575_);
lean_inc(v_x_2570_);
lean_inc(v_post_2565_);
lean_inc(v_pre_2564_);
lean_inc_ref(v_inst_2563_);
lean_inc(v_inst_2562_);
lean_inc_ref(v_inst_2561_);
v___f_2605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2605_, 0, v_struct_2601_);
lean_closure_set(v___f_2605_, 1, v_typeName_2599_);
lean_closure_set(v___f_2605_, 2, v_idx_2600_);
lean_closure_set(v___f_2605_, 3, v_inst_2561_);
lean_closure_set(v___f_2605_, 4, v_inst_2562_);
lean_closure_set(v___f_2605_, 5, v_inst_2563_);
lean_closure_set(v___f_2605_, 6, v_pre_2564_);
lean_closure_set(v___f_2605_, 7, v_post_2565_);
lean_closure_set(v___f_2605_, 8, v___x_2602_);
lean_closure_set(v___f_2605_, 9, v___x_2603_);
lean_closure_set(v___f_2605_, 10, v___x_2604_);
lean_closure_set(v___f_2605_, 11, v_x_2569_);
lean_closure_set(v___f_2605_, 12, v_x_2570_);
lean_closure_set(v___f_2605_, 13, v___y_2575_);
lean_closure_set(v___f_2605_, 14, v___y_2577_);
v___x_2606_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v_struct_2601_, v___y_2575_);
v___x_2607_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2606_, v___f_2605_);
return v___x_2607_;
}
default: 
{
lean_object* v___x_2608_; 
lean_dec(v_toBind_2572_);
lean_dec(v___f_2571_);
v___x_2608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v___y_2577_, v___y_2575_);
return v___x_2608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2616_, lean_object* v_inst_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_pre_2620_, lean_object* v_post_2621_, lean_object* v_usedLetOnly_2622_, lean_object* v_skipConstInApp_2623_, lean_object* v_skipInstances_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v___f_2627_, lean_object* v_toBind_2628_, lean_object* v_e_2629_, lean_object* v_____do__lift_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v_usedLetOnly_boxed_2632_; uint8_t v_skipConstInApp_boxed_2633_; uint8_t v_skipInstances_boxed_2634_; lean_object* v_res_2635_; 
v_usedLetOnly_boxed_2632_ = lean_unbox(v_usedLetOnly_2622_);
v_skipConstInApp_boxed_2633_ = lean_unbox(v_skipConstInApp_2623_);
v_skipInstances_boxed_2634_ = lean_unbox(v_skipInstances_2624_);
v_res_2635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2616_, v_inst_2617_, v_inst_2618_, v_inst_2619_, v_pre_2620_, v_post_2621_, v_usedLetOnly_boxed_2632_, v_skipConstInApp_boxed_2633_, v_skipInstances_boxed_2634_, v_x_2625_, v_x_2626_, v___f_2627_, v_toBind_2628_, v_e_2629_, v_____do__lift_2630_, v___y_2631_);
lean_dec(v___y_2631_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_pre_2639_, lean_object* v_post_2640_, uint8_t v_usedLetOnly_2641_, uint8_t v_skipConstInApp_2642_, uint8_t v_skipInstances_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v_e_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___f_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v_toApplicative_2655_; lean_object* v_toBind_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___f_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___f_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2648_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2649_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2636_, 3);
v___x_2650_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2644_, v___x_2648_, v___x_2649_, v_inst_2636_);
v___x_2651_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2644_, v___x_2648_, v___x_2649_);
lean_inc_ref_n(v_inst_2638_, 3);
lean_inc_ref(v___x_2651_);
v___f_2652_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2652_, 0, v___x_2651_);
lean_closure_set(v___f_2652_, 1, v_inst_2638_);
v___f_2653_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2653_, 0, v___x_2651_);
lean_closure_set(v___f_2653_, 1, v_inst_2638_);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___f_2652_);
lean_ctor_set(v___x_2654_, 1, v___f_2653_);
v_toApplicative_2655_ = lean_ctor_get(v_inst_2636_, 0);
lean_inc_ref_n(v_toApplicative_2655_, 6);
v_toBind_2656_ = lean_ctor_get(v_inst_2636_, 1);
lean_inc_n(v_toBind_2656_, 6);
v___f_2657_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2657_, 0, v_toApplicative_2655_);
lean_inc_n(v_x_2645_, 3);
lean_inc_n(v_a_2647_, 3);
lean_inc_ref_n(v_e_2646_, 3);
v___f_2658_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2658_, 0, v_toApplicative_2655_);
lean_closure_set(v___f_2658_, 1, v___x_2648_);
lean_closure_set(v___f_2658_, 2, v___x_2649_);
lean_closure_set(v___f_2658_, 3, v_e_2646_);
lean_closure_set(v___f_2658_, 4, v_a_2647_);
lean_closure_set(v___f_2658_, 5, v_x_2645_);
lean_closure_set(v___f_2658_, 6, v_toBind_2656_);
v___f_2659_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2659_, 0, v_toApplicative_2655_);
lean_closure_set(v___f_2659_, 1, v___x_2648_);
lean_closure_set(v___f_2659_, 2, v___x_2649_);
lean_closure_set(v___f_2659_, 3, v_e_2646_);
v___x_2660_ = lean_box(v_skipInstances_2643_);
v___x_2661_ = lean_box(v_usedLetOnly_2641_);
v___x_2662_ = lean_box(v_skipConstInApp_2642_);
lean_inc_ref(v___x_2650_);
lean_inc(v_post_2640_);
lean_inc_n(v_pre_2639_, 2);
lean_inc(v_inst_2637_);
v___f_2663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2663_, 0, v___x_2660_);
lean_closure_set(v___f_2663_, 1, v_inst_2636_);
lean_closure_set(v___f_2663_, 2, v_inst_2637_);
lean_closure_set(v___f_2663_, 3, v_inst_2638_);
lean_closure_set(v___f_2663_, 4, v_pre_2639_);
lean_closure_set(v___f_2663_, 5, v_post_2640_);
lean_closure_set(v___f_2663_, 6, v___x_2661_);
lean_closure_set(v___f_2663_, 7, v___x_2662_);
lean_closure_set(v___f_2663_, 8, v_x_2644_);
lean_closure_set(v___f_2663_, 9, v_x_2645_);
lean_closure_set(v___f_2663_, 10, v___x_2650_);
lean_closure_set(v___f_2663_, 11, v_toBind_2656_);
lean_closure_set(v___f_2663_, 12, v_toApplicative_2655_);
lean_closure_set(v___f_2663_, 13, v___f_2657_);
v___x_2664_ = lean_box(v_usedLetOnly_2641_);
v___x_2665_ = lean_box(v_skipConstInApp_2642_);
v___x_2666_ = lean_box(v_skipInstances_2643_);
v___f_2667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 14);
lean_closure_set(v___f_2667_, 0, v_toApplicative_2655_);
lean_closure_set(v___f_2667_, 1, v_inst_2636_);
lean_closure_set(v___f_2667_, 2, v_inst_2637_);
lean_closure_set(v___f_2667_, 3, v_inst_2638_);
lean_closure_set(v___f_2667_, 4, v_pre_2639_);
lean_closure_set(v___f_2667_, 5, v_post_2640_);
lean_closure_set(v___f_2667_, 6, v___x_2664_);
lean_closure_set(v___f_2667_, 7, v___x_2665_);
lean_closure_set(v___f_2667_, 8, v___x_2666_);
lean_closure_set(v___f_2667_, 9, v_x_2644_);
lean_closure_set(v___f_2667_, 10, v_x_2645_);
lean_closure_set(v___f_2667_, 11, v___f_2663_);
lean_closure_set(v___f_2667_, 12, v_toBind_2656_);
lean_closure_set(v___f_2667_, 13, v_e_2646_);
v___f_2668_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 14, 13);
lean_closure_set(v___f_2668_, 0, v_pre_2639_);
lean_closure_set(v___f_2668_, 1, v_e_2646_);
lean_closure_set(v___f_2668_, 2, v_x_2644_);
lean_closure_set(v___f_2668_, 3, v___x_2648_);
lean_closure_set(v___f_2668_, 4, v___x_2649_);
lean_closure_set(v___f_2668_, 5, v_inst_2636_);
lean_closure_set(v___f_2668_, 6, v___f_2667_);
lean_closure_set(v___f_2668_, 7, v___x_2654_);
lean_closure_set(v___f_2668_, 8, v___x_2650_);
lean_closure_set(v___f_2668_, 9, v_a_2647_);
lean_closure_set(v___f_2668_, 10, v_toBind_2656_);
lean_closure_set(v___f_2668_, 11, v___f_2658_);
lean_closure_set(v___f_2668_, 12, v_toApplicative_2655_);
v___x_2669_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2669_, 0, lean_box(0));
lean_closure_set(v___x_2669_, 1, lean_box(0));
lean_closure_set(v___x_2669_, 2, v_a_2647_);
v___x_2670_ = lean_apply_2(v_x_2645_, lean_box(0), v___x_2669_);
v___x_2671_ = lean_apply_4(v_toBind_2656_, lean_box(0), lean_box(0), v___x_2670_, v___f_2659_);
v___x_2672_ = lean_apply_4(v_toBind_2656_, lean_box(0), lean_box(0), v___x_2671_, v___f_2668_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_pre_2677_, lean_object* v_post_2678_, uint8_t v_usedLetOnly_2679_, uint8_t v_skipConstInApp_2680_, uint8_t v_skipInstances_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v_a_2684_, lean_object* v_e_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___y_2688_; 
switch(lean_obj_tag(v_a_2686_))
{
case 0:
{
lean_object* v_e_2691_; lean_object* v_toPure_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v_e_2685_);
lean_dec(v_x_2683_);
lean_dec(v_post_2678_);
lean_dec(v_pre_2677_);
lean_dec_ref(v_inst_2676_);
lean_dec(v_inst_2675_);
lean_dec_ref(v_inst_2674_);
v_e_2691_ = lean_ctor_get(v_a_2686_, 0);
lean_inc_ref(v_e_2691_);
lean_dec_ref(v_a_2686_);
v_toPure_2692_ = lean_ctor_get(v_toApplicative_2673_, 1);
lean_inc(v_toPure_2692_);
lean_dec_ref(v_toApplicative_2673_);
v___x_2693_ = lean_apply_2(v_toPure_2692_, lean_box(0), v_e_2691_);
return v___x_2693_;
}
case 1:
{
lean_object* v_e_2694_; lean_object* v___x_2695_; 
lean_dec_ref(v_e_2685_);
lean_dec_ref(v_toApplicative_2673_);
v_e_2694_ = lean_ctor_get(v_a_2686_, 0);
lean_inc_ref(v_e_2694_);
lean_dec_ref(v_a_2686_);
v___x_2695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v_e_2694_, v_a_2684_);
return v___x_2695_;
}
default: 
{
lean_object* v_e_x3f_2696_; 
lean_dec(v_x_2683_);
lean_dec(v_post_2678_);
lean_dec(v_pre_2677_);
lean_dec_ref(v_inst_2676_);
lean_dec(v_inst_2675_);
lean_dec_ref(v_inst_2674_);
v_e_x3f_2696_ = lean_ctor_get(v_a_2686_, 0);
lean_inc(v_e_x3f_2696_);
lean_dec_ref(v_a_2686_);
if (lean_obj_tag(v_e_x3f_2696_) == 0)
{
v___y_2688_ = v_e_2685_;
goto v___jp_2687_;
}
else
{
lean_object* v_val_2697_; 
lean_dec_ref(v_e_2685_);
v_val_2697_ = lean_ctor_get(v_e_x3f_2696_, 0);
lean_inc(v_val_2697_);
lean_dec_ref(v_e_x3f_2696_);
v___y_2688_ = v_val_2697_;
goto v___jp_2687_;
}
}
}
v___jp_2687_:
{
lean_object* v_toPure_2689_; lean_object* v___x_2690_; 
v_toPure_2689_ = lean_ctor_get(v_toApplicative_2673_, 1);
lean_inc(v_toPure_2689_);
lean_dec_ref(v_toApplicative_2673_);
v___x_2690_ = lean_apply_2(v_toPure_2689_, lean_box(0), v___y_2688_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_pre_2702_, lean_object* v_post_2703_, lean_object* v_usedLetOnly_2704_, lean_object* v_skipConstInApp_2705_, lean_object* v_skipInstances_2706_, lean_object* v_x_2707_, lean_object* v_x_2708_, lean_object* v_a_2709_, lean_object* v_e_2710_, lean_object* v_a_2711_){
_start:
{
uint8_t v_usedLetOnly_boxed_2712_; uint8_t v_skipConstInApp_boxed_2713_; uint8_t v_skipInstances_boxed_2714_; lean_object* v_res_2715_; 
v_usedLetOnly_boxed_2712_ = lean_unbox(v_usedLetOnly_2704_);
v_skipConstInApp_boxed_2713_ = lean_unbox(v_skipConstInApp_2705_);
v_skipInstances_boxed_2714_ = lean_unbox(v_skipInstances_2706_);
v_res_2715_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_pre_2702_, v_post_2703_, v_usedLetOnly_boxed_2712_, v_skipConstInApp_boxed_2713_, v_skipInstances_boxed_2714_, v_x_2707_, v_x_2708_, v_a_2709_, v_e_2710_, v_a_2711_);
lean_dec(v_a_2709_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_pre_2719_, lean_object* v_post_2720_, uint8_t v_usedLetOnly_2721_, uint8_t v_skipConstInApp_2722_, uint8_t v_skipInstances_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v_e_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_toApplicative_2728_; lean_object* v_toBind_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_toApplicative_2728_ = lean_ctor_get(v_inst_2716_, 0);
lean_inc_ref(v_toApplicative_2728_);
v_toBind_2729_ = lean_ctor_get(v_inst_2716_, 1);
lean_inc(v_toBind_2729_);
v___x_2730_ = lean_box(v_usedLetOnly_2721_);
v___x_2731_ = lean_box(v_skipConstInApp_2722_);
v___x_2732_ = lean_box(v_skipInstances_2723_);
lean_inc_ref(v_e_2726_);
lean_inc(v_a_2727_);
lean_inc(v_post_2720_);
v___f_2733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2733_, 0, v_toApplicative_2728_);
lean_closure_set(v___f_2733_, 1, v_inst_2716_);
lean_closure_set(v___f_2733_, 2, v_inst_2717_);
lean_closure_set(v___f_2733_, 3, v_inst_2718_);
lean_closure_set(v___f_2733_, 4, v_pre_2719_);
lean_closure_set(v___f_2733_, 5, v_post_2720_);
lean_closure_set(v___f_2733_, 6, v___x_2730_);
lean_closure_set(v___f_2733_, 7, v___x_2731_);
lean_closure_set(v___f_2733_, 8, v___x_2732_);
lean_closure_set(v___f_2733_, 9, v_x_2724_);
lean_closure_set(v___f_2733_, 10, v_x_2725_);
lean_closure_set(v___f_2733_, 11, v_a_2727_);
lean_closure_set(v___f_2733_, 12, v_e_2726_);
v___x_2734_ = lean_apply_1(v_post_2720_, v_e_2726_);
v___x_2735_ = lean_apply_4(v_toBind_2729_, lean_box(0), lean_box(0), v___x_2734_, v___f_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_pre_2739_, lean_object* v_post_2740_, uint8_t v_usedLetOnly_2741_, uint8_t v_skipConstInApp_2742_, uint8_t v_skipInstances_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2736_, v_inst_2737_, v_inst_2738_, v_pre_2739_, v_post_2740_, v_usedLetOnly_2741_, v_skipConstInApp_2742_, v_skipInstances_2743_, v_x_2744_, v_x_2745_, v_a_2747_, v_a_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_pre_2752_, lean_object* v_post_2753_, lean_object* v_usedLetOnly_2754_, lean_object* v_skipConstInApp_2755_, lean_object* v_skipInstances_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v_e_2759_, lean_object* v_a_2760_){
_start:
{
uint8_t v_usedLetOnly_boxed_2761_; uint8_t v_skipConstInApp_boxed_2762_; uint8_t v_skipInstances_boxed_2763_; lean_object* v_res_2764_; 
v_usedLetOnly_boxed_2761_ = lean_unbox(v_usedLetOnly_2754_);
v_skipConstInApp_boxed_2762_ = lean_unbox(v_skipConstInApp_2755_);
v_skipInstances_boxed_2763_ = lean_unbox(v_skipInstances_2756_);
v_res_2764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2749_, v_inst_2750_, v_inst_2751_, v_pre_2752_, v_post_2753_, v_usedLetOnly_boxed_2761_, v_skipConstInApp_boxed_2762_, v_skipInstances_boxed_2763_, v_x_2757_, v_x_2758_, v_e_2759_, v_a_2760_);
lean_dec(v_a_2760_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_pre_2768_, lean_object* v_post_2769_, lean_object* v_usedLetOnly_2770_, lean_object* v_skipConstInApp_2771_, lean_object* v_skipInstances_2772_, lean_object* v_x_2773_, lean_object* v_x_2774_, lean_object* v_fvars_2775_, lean_object* v_e_2776_, lean_object* v_a_2777_){
_start:
{
uint8_t v_usedLetOnly_boxed_2778_; uint8_t v_skipConstInApp_boxed_2779_; uint8_t v_skipInstances_boxed_2780_; lean_object* v_res_2781_; 
v_usedLetOnly_boxed_2778_ = lean_unbox(v_usedLetOnly_2770_);
v_skipConstInApp_boxed_2779_ = lean_unbox(v_skipConstInApp_2771_);
v_skipInstances_boxed_2780_ = lean_unbox(v_skipInstances_2772_);
v_res_2781_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2765_, v_inst_2766_, v_inst_2767_, v_pre_2768_, v_post_2769_, v_usedLetOnly_boxed_2778_, v_skipConstInApp_boxed_2779_, v_skipInstances_boxed_2780_, v_x_2773_, v_x_2774_, v_fvars_2775_, v_e_2776_, v_a_2777_);
lean_dec(v_a_2777_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2782_, lean_object* v_inst_2783_, lean_object* v_inst_2784_, lean_object* v_pre_2785_, lean_object* v_post_2786_, lean_object* v_usedLetOnly_2787_, lean_object* v_skipConstInApp_2788_, lean_object* v_skipInstances_2789_, lean_object* v_x_2790_, lean_object* v_x_2791_, lean_object* v_fvars_2792_, lean_object* v_e_2793_, lean_object* v_a_2794_){
_start:
{
uint8_t v_usedLetOnly_boxed_2795_; uint8_t v_skipConstInApp_boxed_2796_; uint8_t v_skipInstances_boxed_2797_; lean_object* v_res_2798_; 
v_usedLetOnly_boxed_2795_ = lean_unbox(v_usedLetOnly_2787_);
v_skipConstInApp_boxed_2796_ = lean_unbox(v_skipConstInApp_2788_);
v_skipInstances_boxed_2797_ = lean_unbox(v_skipInstances_2789_);
v_res_2798_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2782_, v_inst_2783_, v_inst_2784_, v_pre_2785_, v_post_2786_, v_usedLetOnly_boxed_2795_, v_skipConstInApp_boxed_2796_, v_skipInstances_boxed_2797_, v_x_2790_, v_x_2791_, v_fvars_2792_, v_e_2793_, v_a_2794_);
lean_dec(v_a_2794_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_pre_2802_, lean_object* v_post_2803_, lean_object* v_usedLetOnly_2804_, lean_object* v_skipConstInApp_2805_, lean_object* v_skipInstances_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_, lean_object* v_fvars_2809_, lean_object* v_e_2810_, lean_object* v_a_2811_){
_start:
{
uint8_t v_usedLetOnly_boxed_2812_; uint8_t v_skipConstInApp_boxed_2813_; uint8_t v_skipInstances_boxed_2814_; lean_object* v_res_2815_; 
v_usedLetOnly_boxed_2812_ = lean_unbox(v_usedLetOnly_2804_);
v_skipConstInApp_boxed_2813_ = lean_unbox(v_skipConstInApp_2805_);
v_skipInstances_boxed_2814_ = lean_unbox(v_skipInstances_2806_);
v_res_2815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2799_, v_inst_2800_, v_inst_2801_, v_pre_2802_, v_post_2803_, v_usedLetOnly_boxed_2812_, v_skipConstInApp_boxed_2813_, v_skipInstances_boxed_2814_, v_x_2807_, v_x_2808_, v_fvars_2809_, v_e_2810_, v_a_2811_);
lean_dec(v_a_2811_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2816_, lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_pre_2820_, lean_object* v_post_2821_, uint8_t v_usedLetOnly_2822_, uint8_t v_skipConstInApp_2823_, uint8_t v_skipInstances_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_e_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2817_, v_inst_2818_, v_inst_2819_, v_pre_2820_, v_post_2821_, v_usedLetOnly_2822_, v_skipConstInApp_2823_, v_skipInstances_2824_, v_x_2825_, v_x_2826_, v_e_2827_, v_a_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_pre_2834_, lean_object* v_post_2835_, lean_object* v_usedLetOnly_2836_, lean_object* v_skipConstInApp_2837_, lean_object* v_skipInstances_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_, lean_object* v_e_2841_, lean_object* v_a_2842_){
_start:
{
uint8_t v_usedLetOnly_boxed_2843_; uint8_t v_skipConstInApp_boxed_2844_; uint8_t v_skipInstances_boxed_2845_; lean_object* v_res_2846_; 
v_usedLetOnly_boxed_2843_ = lean_unbox(v_usedLetOnly_2836_);
v_skipConstInApp_boxed_2844_ = lean_unbox(v_skipConstInApp_2837_);
v_skipInstances_boxed_2845_ = lean_unbox(v_skipInstances_2838_);
v_res_2846_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2830_, v_inst_2831_, v_inst_2832_, v_inst_2833_, v_pre_2834_, v_post_2835_, v_usedLetOnly_boxed_2843_, v_skipConstInApp_boxed_2844_, v_skipInstances_boxed_2845_, v_x_2839_, v_x_2840_, v_e_2841_, v_a_2842_);
lean_dec(v_a_2842_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_pre_2851_, lean_object* v_post_2852_, uint8_t v_usedLetOnly_2853_, uint8_t v_skipConstInApp_2854_, uint8_t v_skipInstances_2855_, lean_object* v_x_2856_, lean_object* v_x_2857_, lean_object* v_fvars_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2848_, v_inst_2849_, v_inst_2850_, v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v_x_2856_, v_x_2857_, v_fvars_2858_, v_e_2859_, v_a_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_pre_2866_, lean_object* v_post_2867_, lean_object* v_usedLetOnly_2868_, lean_object* v_skipConstInApp_2869_, lean_object* v_skipInstances_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_, lean_object* v_fvars_2873_, lean_object* v_e_2874_, lean_object* v_a_2875_){
_start:
{
uint8_t v_usedLetOnly_boxed_2876_; uint8_t v_skipConstInApp_boxed_2877_; uint8_t v_skipInstances_boxed_2878_; lean_object* v_res_2879_; 
v_usedLetOnly_boxed_2876_ = lean_unbox(v_usedLetOnly_2868_);
v_skipConstInApp_boxed_2877_ = lean_unbox(v_skipConstInApp_2869_);
v_skipInstances_boxed_2878_ = lean_unbox(v_skipInstances_2870_);
v_res_2879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_2862_, v_inst_2863_, v_inst_2864_, v_inst_2865_, v_pre_2866_, v_post_2867_, v_usedLetOnly_boxed_2876_, v_skipConstInApp_boxed_2877_, v_skipInstances_boxed_2878_, v_x_2871_, v_x_2872_, v_fvars_2873_, v_e_2874_, v_a_2875_);
lean_dec(v_a_2875_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_pre_2884_, lean_object* v_post_2885_, uint8_t v_usedLetOnly_2886_, uint8_t v_skipConstInApp_2887_, uint8_t v_skipInstances_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_, lean_object* v_e_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2881_, v_inst_2882_, v_inst_2883_, v_pre_2884_, v_post_2885_, v_usedLetOnly_2886_, v_skipConstInApp_2887_, v_skipInstances_2888_, v_x_2889_, v_x_2890_, v_e_2891_, v_a_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_pre_2898_, lean_object* v_post_2899_, lean_object* v_usedLetOnly_2900_, lean_object* v_skipConstInApp_2901_, lean_object* v_skipInstances_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_e_2905_, lean_object* v_a_2906_){
_start:
{
uint8_t v_usedLetOnly_boxed_2907_; uint8_t v_skipConstInApp_boxed_2908_; uint8_t v_skipInstances_boxed_2909_; lean_object* v_res_2910_; 
v_usedLetOnly_boxed_2907_ = lean_unbox(v_usedLetOnly_2900_);
v_skipConstInApp_boxed_2908_ = lean_unbox(v_skipConstInApp_2901_);
v_skipInstances_boxed_2909_ = lean_unbox(v_skipInstances_2902_);
v_res_2910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_2894_, v_inst_2895_, v_inst_2896_, v_inst_2897_, v_pre_2898_, v_post_2899_, v_usedLetOnly_boxed_2907_, v_skipConstInApp_boxed_2908_, v_skipInstances_boxed_2909_, v_x_2903_, v_x_2904_, v_e_2905_, v_a_2906_);
lean_dec(v_a_2906_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_inst_2914_, lean_object* v_pre_2915_, lean_object* v_post_2916_, uint8_t v_usedLetOnly_2917_, uint8_t v_skipConstInApp_2918_, uint8_t v_skipInstances_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_, lean_object* v_fvars_2922_, lean_object* v_e_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2912_, v_inst_2913_, v_inst_2914_, v_pre_2915_, v_post_2916_, v_usedLetOnly_2917_, v_skipConstInApp_2918_, v_skipInstances_2919_, v_x_2920_, v_x_2921_, v_fvars_2922_, v_e_2923_, v_a_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_pre_2930_, lean_object* v_post_2931_, lean_object* v_usedLetOnly_2932_, lean_object* v_skipConstInApp_2933_, lean_object* v_skipInstances_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_fvars_2937_, lean_object* v_e_2938_, lean_object* v_a_2939_){
_start:
{
uint8_t v_usedLetOnly_boxed_2940_; uint8_t v_skipConstInApp_boxed_2941_; uint8_t v_skipInstances_boxed_2942_; lean_object* v_res_2943_; 
v_usedLetOnly_boxed_2940_ = lean_unbox(v_usedLetOnly_2932_);
v_skipConstInApp_boxed_2941_ = lean_unbox(v_skipConstInApp_2933_);
v_skipInstances_boxed_2942_ = lean_unbox(v_skipInstances_2934_);
v_res_2943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_2926_, v_inst_2927_, v_inst_2928_, v_inst_2929_, v_pre_2930_, v_post_2931_, v_usedLetOnly_boxed_2940_, v_skipConstInApp_boxed_2941_, v_skipInstances_boxed_2942_, v_x_2935_, v_x_2936_, v_fvars_2937_, v_e_2938_, v_a_2939_);
lean_dec(v_a_2939_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_pre_2948_, lean_object* v_post_2949_, uint8_t v_usedLetOnly_2950_, uint8_t v_skipConstInApp_2951_, uint8_t v_skipInstances_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_, lean_object* v_fvars_2955_, lean_object* v_e_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2945_, v_inst_2946_, v_inst_2947_, v_pre_2948_, v_post_2949_, v_usedLetOnly_2950_, v_skipConstInApp_2951_, v_skipInstances_2952_, v_x_2953_, v_x_2954_, v_fvars_2955_, v_e_2956_, v_a_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_pre_2963_, lean_object* v_post_2964_, lean_object* v_usedLetOnly_2965_, lean_object* v_skipConstInApp_2966_, lean_object* v_skipInstances_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_, lean_object* v_fvars_2970_, lean_object* v_e_2971_, lean_object* v_a_2972_){
_start:
{
uint8_t v_usedLetOnly_boxed_2973_; uint8_t v_skipConstInApp_boxed_2974_; uint8_t v_skipInstances_boxed_2975_; lean_object* v_res_2976_; 
v_usedLetOnly_boxed_2973_ = lean_unbox(v_usedLetOnly_2965_);
v_skipConstInApp_boxed_2974_ = lean_unbox(v_skipConstInApp_2966_);
v_skipInstances_boxed_2975_ = lean_unbox(v_skipInstances_2967_);
v_res_2976_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_2959_, v_inst_2960_, v_inst_2961_, v_inst_2962_, v_pre_2963_, v_post_2964_, v_usedLetOnly_boxed_2973_, v_skipConstInApp_boxed_2974_, v_skipInstances_boxed_2975_, v_x_2968_, v_x_2969_, v_fvars_2970_, v_e_2971_, v_a_2972_);
lean_dec(v_a_2972_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_apply_1(v_x_2977_, lean_box(0));
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_2992_, lean_object* v_00_u03b1_2993_, lean_object* v_x_2994_){
_start:
{
lean_object* v___f_2995_; lean_object* v___x_2996_; 
v___f_2995_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2995_, 0, v_x_2994_);
v___x_2996_ = lean_apply_2(v_inst_2992_, lean_box(0), v___f_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_2997_, lean_object* v_x_2998_, lean_object* v_toBind_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_pre_3003_, lean_object* v_post_3004_, uint8_t v_usedLetOnly_3005_, uint8_t v_skipConstInApp_3006_, uint8_t v_skipInstances_3007_, lean_object* v_x_3008_, lean_object* v_input_3009_, lean_object* v_ref_3010_){
_start:
{
lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_inc(v_toBind_2999_);
lean_inc(v_x_2998_);
lean_inc(v_ref_3010_);
v___f_3011_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3011_, 0, v_toPure_2997_);
lean_closure_set(v___f_3011_, 1, v_ref_3010_);
lean_closure_set(v___f_3011_, 2, v_x_2998_);
lean_closure_set(v___f_3011_, 3, v_toBind_2999_);
v___x_3012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3000_, v_inst_3001_, v_inst_3002_, v_pre_3003_, v_post_3004_, v_usedLetOnly_3005_, v_skipConstInApp_3006_, v_skipInstances_3007_, v_x_3008_, v_x_2998_, v_input_3009_, v_ref_3010_);
lean_dec(v_ref_3010_);
v___x_3013_ = lean_apply_4(v_toBind_2999_, lean_box(0), lean_box(0), v___x_3012_, v___f_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3014_, lean_object* v_x_3015_, lean_object* v_toBind_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_pre_3020_, lean_object* v_post_3021_, lean_object* v_usedLetOnly_3022_, lean_object* v_skipConstInApp_3023_, lean_object* v_skipInstances_3024_, lean_object* v_x_3025_, lean_object* v_input_3026_, lean_object* v_ref_3027_){
_start:
{
uint8_t v_usedLetOnly_boxed_3028_; uint8_t v_skipConstInApp_boxed_3029_; uint8_t v_skipInstances_boxed_3030_; lean_object* v_res_3031_; 
v_usedLetOnly_boxed_3028_ = lean_unbox(v_usedLetOnly_3022_);
v_skipConstInApp_boxed_3029_ = lean_unbox(v_skipConstInApp_3023_);
v_skipInstances_boxed_3030_ = lean_unbox(v_skipInstances_3024_);
v_res_3031_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3014_, v_x_3015_, v_toBind_3016_, v_inst_3017_, v_inst_3018_, v_inst_3019_, v_pre_3020_, v_post_3021_, v_usedLetOnly_boxed_3028_, v_skipConstInApp_boxed_3029_, v_skipInstances_boxed_3030_, v_x_3025_, v_input_3026_, v_ref_3027_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_input_3035_, lean_object* v_cache_3036_, lean_object* v_pre_3037_, lean_object* v_post_3038_, uint8_t v_usedLetOnly_3039_, uint8_t v_skipConstInApp_3040_, uint8_t v_skipInstances_3041_){
_start:
{
lean_object* v_x_3042_; lean_object* v_toApplicative_3043_; lean_object* v_toBind_3044_; lean_object* v_toPure_3045_; lean_object* v_x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___f_3052_; lean_object* v___x_3053_; 
v_x_3042_ = lean_box(0);
v_toApplicative_3043_ = lean_ctor_get(v_inst_3032_, 0);
v_toBind_3044_ = lean_ctor_get(v_inst_3032_, 1);
lean_inc_n(v_toBind_3044_, 2);
v_toPure_3045_ = lean_ctor_get(v_toApplicative_3043_, 1);
lean_inc(v_toPure_3045_);
lean_inc_n(v_inst_3033_, 2);
v_x_3046_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3046_, 0, v_inst_3033_);
v___x_3047_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3047_, 0, lean_box(0));
lean_closure_set(v___x_3047_, 1, lean_box(0));
lean_closure_set(v___x_3047_, 2, v_cache_3036_);
v___x_3048_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3033_, lean_box(0), v___x_3047_);
v___x_3049_ = lean_box(v_usedLetOnly_3039_);
v___x_3050_ = lean_box(v_skipConstInApp_3040_);
v___x_3051_ = lean_box(v_skipInstances_3041_);
v___f_3052_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3052_, 0, v_toPure_3045_);
lean_closure_set(v___f_3052_, 1, v_x_3046_);
lean_closure_set(v___f_3052_, 2, v_toBind_3044_);
lean_closure_set(v___f_3052_, 3, v_inst_3032_);
lean_closure_set(v___f_3052_, 4, v_inst_3033_);
lean_closure_set(v___f_3052_, 5, v_inst_3034_);
lean_closure_set(v___f_3052_, 6, v_pre_3037_);
lean_closure_set(v___f_3052_, 7, v_post_3038_);
lean_closure_set(v___f_3052_, 8, v___x_3049_);
lean_closure_set(v___f_3052_, 9, v___x_3050_);
lean_closure_set(v___f_3052_, 10, v___x_3051_);
lean_closure_set(v___f_3052_, 11, v_x_3042_);
lean_closure_set(v___f_3052_, 12, v_input_3035_);
v___x_3053_ = lean_apply_4(v_toBind_3044_, lean_box(0), lean_box(0), v___x_3048_, v___f_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_input_3057_, lean_object* v_cache_3058_, lean_object* v_pre_3059_, lean_object* v_post_3060_, lean_object* v_usedLetOnly_3061_, lean_object* v_skipConstInApp_3062_, lean_object* v_skipInstances_3063_){
_start:
{
uint8_t v_usedLetOnly_boxed_3064_; uint8_t v_skipConstInApp_boxed_3065_; uint8_t v_skipInstances_boxed_3066_; lean_object* v_res_3067_; 
v_usedLetOnly_boxed_3064_ = lean_unbox(v_usedLetOnly_3061_);
v_skipConstInApp_boxed_3065_ = lean_unbox(v_skipConstInApp_3062_);
v_skipInstances_boxed_3066_ = lean_unbox(v_skipInstances_3063_);
v_res_3067_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3054_, v_inst_3055_, v_inst_3056_, v_input_3057_, v_cache_3058_, v_pre_3059_, v_post_3060_, v_usedLetOnly_boxed_3064_, v_skipConstInApp_boxed_3065_, v_skipInstances_boxed_3066_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_input_3072_, lean_object* v_cache_3073_, lean_object* v_pre_3074_, lean_object* v_post_3075_, uint8_t v_usedLetOnly_3076_, uint8_t v_skipConstInApp_3077_, uint8_t v_skipInstances_3078_){
_start:
{
lean_object* v_x_3079_; lean_object* v_toApplicative_3080_; lean_object* v_toBind_3081_; lean_object* v_toPure_3082_; lean_object* v_x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___f_3089_; lean_object* v___x_3090_; 
v_x_3079_ = lean_box(0);
v_toApplicative_3080_ = lean_ctor_get(v_inst_3069_, 0);
v_toBind_3081_ = lean_ctor_get(v_inst_3069_, 1);
lean_inc_n(v_toBind_3081_, 2);
v_toPure_3082_ = lean_ctor_get(v_toApplicative_3080_, 1);
lean_inc(v_toPure_3082_);
lean_inc_n(v_inst_3070_, 2);
v_x_3083_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3083_, 0, v_inst_3070_);
v___x_3084_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3084_, 0, lean_box(0));
lean_closure_set(v___x_3084_, 1, lean_box(0));
lean_closure_set(v___x_3084_, 2, v_cache_3073_);
v___x_3085_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3070_, lean_box(0), v___x_3084_);
v___x_3086_ = lean_box(v_usedLetOnly_3076_);
v___x_3087_ = lean_box(v_skipConstInApp_3077_);
v___x_3088_ = lean_box(v_skipInstances_3078_);
v___f_3089_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3089_, 0, v_toPure_3082_);
lean_closure_set(v___f_3089_, 1, v_x_3083_);
lean_closure_set(v___f_3089_, 2, v_toBind_3081_);
lean_closure_set(v___f_3089_, 3, v_inst_3069_);
lean_closure_set(v___f_3089_, 4, v_inst_3070_);
lean_closure_set(v___f_3089_, 5, v_inst_3071_);
lean_closure_set(v___f_3089_, 6, v_pre_3074_);
lean_closure_set(v___f_3089_, 7, v_post_3075_);
lean_closure_set(v___f_3089_, 8, v___x_3086_);
lean_closure_set(v___f_3089_, 9, v___x_3087_);
lean_closure_set(v___f_3089_, 10, v___x_3088_);
lean_closure_set(v___f_3089_, 11, v_x_3079_);
lean_closure_set(v___f_3089_, 12, v_input_3072_);
v___x_3090_ = lean_apply_4(v_toBind_3081_, lean_box(0), lean_box(0), v___x_3085_, v___f_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_input_3095_, lean_object* v_cache_3096_, lean_object* v_pre_3097_, lean_object* v_post_3098_, lean_object* v_usedLetOnly_3099_, lean_object* v_skipConstInApp_3100_, lean_object* v_skipInstances_3101_){
_start:
{
uint8_t v_usedLetOnly_boxed_3102_; uint8_t v_skipConstInApp_boxed_3103_; uint8_t v_skipInstances_boxed_3104_; lean_object* v_res_3105_; 
v_usedLetOnly_boxed_3102_ = lean_unbox(v_usedLetOnly_3099_);
v_skipConstInApp_boxed_3103_ = lean_unbox(v_skipConstInApp_3100_);
v_skipInstances_boxed_3104_ = lean_unbox(v_skipInstances_3101_);
v_res_3105_ = l_Lean_Meta_transformWithCache(v_m_3091_, v_inst_3092_, v_inst_3093_, v_inst_3094_, v_input_3095_, v_cache_3096_, v_pre_3097_, v_post_3098_, v_usedLetOnly_boxed_3102_, v_skipConstInApp_boxed_3103_, v_skipInstances_boxed_3104_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3106_, lean_object* v_x_3107_, lean_object* v_toBind_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_pre_3112_, lean_object* v_post_3113_, uint8_t v_usedLetOnly_3114_, uint8_t v_skipConstInApp_3115_, uint8_t v___x_3116_, lean_object* v_x_3117_, lean_object* v_input_3118_, lean_object* v_ref_3119_){
_start:
{
lean_object* v___f_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_inc(v_toBind_3108_);
lean_inc(v_x_3107_);
lean_inc(v_ref_3119_);
v___f_3120_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3120_, 0, v_toPure_3106_);
lean_closure_set(v___f_3120_, 1, v_ref_3119_);
lean_closure_set(v___f_3120_, 2, v_x_3107_);
lean_closure_set(v___f_3120_, 3, v_toBind_3108_);
v___x_3121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3109_, v_inst_3110_, v_inst_3111_, v_pre_3112_, v_post_3113_, v_usedLetOnly_3114_, v_skipConstInApp_3115_, v___x_3116_, v_x_3117_, v_x_3107_, v_input_3118_, v_ref_3119_);
lean_dec(v_ref_3119_);
v___x_3122_ = lean_apply_4(v_toBind_3108_, lean_box(0), lean_box(0), v___x_3121_, v___f_3120_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3123_, lean_object* v_x_3124_, lean_object* v_toBind_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_pre_3129_, lean_object* v_post_3130_, lean_object* v_usedLetOnly_3131_, lean_object* v_skipConstInApp_3132_, lean_object* v___x_3133_, lean_object* v_x_3134_, lean_object* v_input_3135_, lean_object* v_ref_3136_){
_start:
{
uint8_t v_usedLetOnly_boxed_3137_; uint8_t v_skipConstInApp_boxed_3138_; uint8_t v___x_114__boxed_3139_; lean_object* v_res_3140_; 
v_usedLetOnly_boxed_3137_ = lean_unbox(v_usedLetOnly_3131_);
v_skipConstInApp_boxed_3138_ = lean_unbox(v_skipConstInApp_3132_);
v___x_114__boxed_3139_ = lean_unbox(v___x_3133_);
v_res_3140_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3123_, v_x_3124_, v_toBind_3125_, v_inst_3126_, v_inst_3127_, v_inst_3128_, v_pre_3129_, v_post_3130_, v_usedLetOnly_boxed_3137_, v_skipConstInApp_boxed_3138_, v___x_114__boxed_3139_, v_x_3134_, v_input_3135_, v_ref_3136_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_input_3144_, lean_object* v_pre_3145_, lean_object* v_post_3146_, uint8_t v_usedLetOnly_3147_, uint8_t v_skipConstInApp_3148_){
_start:
{
lean_object* v_toApplicative_3149_; lean_object* v_toBind_3150_; lean_object* v_x_3151_; lean_object* v_toPure_3152_; lean_object* v_x_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___f_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_toApplicative_3149_ = lean_ctor_get(v_inst_3141_, 0);
v_toBind_3150_ = lean_ctor_get(v_inst_3141_, 1);
lean_inc_n(v_toBind_3150_, 3);
v_x_3151_ = lean_box(0);
v_toPure_3152_ = lean_ctor_get(v_toApplicative_3149_, 1);
lean_inc_n(v_toPure_3152_, 2);
lean_inc_n(v_inst_3142_, 2);
v_x_3153_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3153_, 0, v_inst_3142_);
v___x_3154_ = 0;
v___x_3155_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3156_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3142_, lean_box(0), v___x_3155_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3157_, 0, v_toPure_3152_);
v___x_3158_ = lean_box(v_usedLetOnly_3147_);
v___x_3159_ = lean_box(v_skipConstInApp_3148_);
v___x_3160_ = lean_box(v___x_3154_);
v___f_3161_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3161_, 0, v_toPure_3152_);
lean_closure_set(v___f_3161_, 1, v_x_3153_);
lean_closure_set(v___f_3161_, 2, v_toBind_3150_);
lean_closure_set(v___f_3161_, 3, v_inst_3141_);
lean_closure_set(v___f_3161_, 4, v_inst_3142_);
lean_closure_set(v___f_3161_, 5, v_inst_3143_);
lean_closure_set(v___f_3161_, 6, v_pre_3145_);
lean_closure_set(v___f_3161_, 7, v_post_3146_);
lean_closure_set(v___f_3161_, 8, v___x_3158_);
lean_closure_set(v___f_3161_, 9, v___x_3159_);
lean_closure_set(v___f_3161_, 10, v___x_3160_);
lean_closure_set(v___f_3161_, 11, v_x_3151_);
lean_closure_set(v___f_3161_, 12, v_input_3144_);
v___x_3162_ = lean_apply_4(v_toBind_3150_, lean_box(0), lean_box(0), v___x_3156_, v___f_3161_);
v___x_3163_ = lean_apply_4(v_toBind_3150_, lean_box(0), lean_box(0), v___x_3162_, v___f_3157_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_input_3167_, lean_object* v_pre_3168_, lean_object* v_post_3169_, lean_object* v_usedLetOnly_3170_, lean_object* v_skipConstInApp_3171_){
_start:
{
uint8_t v_usedLetOnly_boxed_3172_; uint8_t v_skipConstInApp_boxed_3173_; lean_object* v_res_3174_; 
v_usedLetOnly_boxed_3172_ = lean_unbox(v_usedLetOnly_3170_);
v_skipConstInApp_boxed_3173_ = lean_unbox(v_skipConstInApp_3171_);
v_res_3174_ = l_Lean_Meta_transform___redArg(v_inst_3164_, v_inst_3165_, v_inst_3166_, v_input_3167_, v_pre_3168_, v_post_3169_, v_usedLetOnly_boxed_3172_, v_skipConstInApp_boxed_3173_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_input_3179_, lean_object* v_pre_3180_, lean_object* v_post_3181_, uint8_t v_usedLetOnly_3182_, uint8_t v_skipConstInApp_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Meta_transform___redArg(v_inst_3176_, v_inst_3177_, v_inst_3178_, v_input_3179_, v_pre_3180_, v_post_3181_, v_usedLetOnly_3182_, v_skipConstInApp_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_input_3189_, lean_object* v_pre_3190_, lean_object* v_post_3191_, lean_object* v_usedLetOnly_3192_, lean_object* v_skipConstInApp_3193_){
_start:
{
uint8_t v_usedLetOnly_boxed_3194_; uint8_t v_skipConstInApp_boxed_3195_; lean_object* v_res_3196_; 
v_usedLetOnly_boxed_3194_ = lean_unbox(v_usedLetOnly_3192_);
v_skipConstInApp_boxed_3195_ = lean_unbox(v_skipConstInApp_3193_);
v_res_3196_ = l_Lean_Meta_transform(v_m_3185_, v_inst_3186_, v_inst_3187_, v_inst_3188_, v_input_3189_, v_pre_3190_, v_post_3191_, v_usedLetOnly_boxed_3194_, v_skipConstInApp_boxed_3195_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3197_, lean_object* v___y_3198_){
_start:
{
uint8_t v___x_3200_; 
v___x_3200_ = l_Lean_Expr_hasMVar(v_e_3197_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_e_3197_);
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; lean_object* v_mctx_3203_; lean_object* v___x_3204_; lean_object* v_fst_3205_; lean_object* v_snd_3206_; lean_object* v___x_3207_; lean_object* v_cache_3208_; lean_object* v_zetaDeltaFVarIds_3209_; lean_object* v_postponed_3210_; lean_object* v_diag_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3220_; 
v___x_3202_ = lean_st_ref_get(v___y_3198_);
v_mctx_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc_ref(v_mctx_3203_);
lean_dec(v___x_3202_);
v___x_3204_ = l_Lean_instantiateMVarsCore(v_mctx_3203_, v_e_3197_);
v_fst_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_fst_3205_);
v_snd_3206_ = lean_ctor_get(v___x_3204_, 1);
lean_inc(v_snd_3206_);
lean_dec_ref(v___x_3204_);
v___x_3207_ = lean_st_ref_take(v___y_3198_);
v_cache_3208_ = lean_ctor_get(v___x_3207_, 1);
v_zetaDeltaFVarIds_3209_ = lean_ctor_get(v___x_3207_, 2);
v_postponed_3210_ = lean_ctor_get(v___x_3207_, 3);
v_diag_3211_ = lean_ctor_get(v___x_3207_, 4);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3207_, 0);
lean_dec(v_unused_3221_);
v___x_3213_ = v___x_3207_;
v_isShared_3214_ = v_isSharedCheck_3220_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_diag_3211_);
lean_inc(v_postponed_3210_);
lean_inc(v_zetaDeltaFVarIds_3209_);
lean_inc(v_cache_3208_);
lean_dec(v___x_3207_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3220_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v_snd_3206_);
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_snd_3206_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_cache_3208_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_zetaDeltaFVarIds_3209_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v_postponed_3210_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v_diag_3211_);
v___x_3216_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_st_ref_set(v___y_3198_, v___x_3216_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_fst_3205_);
return v___x_3218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3222_, v___y_3223_);
lean_dec(v___y_3223_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3226_, v___y_3228_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3240_, lean_object* v___x_3241_, uint8_t v_zetaDelta_3242_, lean_object* v_fvarId_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3278_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3278_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3278_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
if (lean_obj_tag(v_a_3250_) == 1)
{
lean_object* v_val_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3273_; 
v_val_3254_ = lean_ctor_get(v_a_3250_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_a_3250_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3256_ = v_a_3250_;
v_isShared_3257_ = v_isSharedCheck_3273_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_val_3254_);
lean_dec(v_a_3250_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3273_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
uint8_t v___y_3259_; 
if (v_zetaDelta_3242_ == 0)
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = l_Lean_LocalDecl_index(v_val_3254_);
v___x_3268_ = lean_nat_dec_lt(v___x_3267_, v___x_3241_);
lean_dec(v___x_3267_);
if (v___x_3268_ == 0)
{
lean_del_object(v___x_3256_);
goto v___jp_3264_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
lean_dec(v_val_3254_);
lean_del_object(v___x_3252_);
v___x_3269_ = lean_box(0);
if (v_isShared_3257_ == 0)
{
lean_ctor_set_tag(v___x_3256_, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3269_);
v___x_3271_ = v___x_3256_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
else
{
lean_del_object(v___x_3256_);
goto v___jp_3264_;
}
v___jp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3260_ = l_Lean_LocalDecl_value_x3f(v_val_3254_, v___y_3259_);
lean_dec(v_val_3254_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3260_);
v___x_3262_ = v___x_3252_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
v___jp_3264_:
{
if (v_zetaHave_3240_ == 0)
{
v___y_3259_ = v_zetaHave_3240_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = l_Lean_LocalDecl_index(v_val_3254_);
v___x_3266_ = lean_nat_dec_le(v___x_3241_, v___x_3265_);
lean_dec(v___x_3265_);
v___y_3259_ = v___x_3266_;
goto v___jp_3258_;
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_dec(v_a_3250_);
v___x_3274_ = lean_box(0);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3274_);
v___x_3276_ = v___x_3252_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
v_a_3279_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3249_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3249_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3287_, lean_object* v___x_3288_, lean_object* v_zetaDelta_3289_, lean_object* v_fvarId_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v_zetaHave_boxed_3296_; uint8_t v_zetaDelta_boxed_3297_; lean_object* v_res_3298_; 
v_zetaHave_boxed_3296_ = lean_unbox(v_zetaHave_3287_);
v_zetaDelta_boxed_3297_ = lean_unbox(v_zetaDelta_3289_);
v_res_3298_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3296_, v___x_3288_, v_zetaDelta_boxed_3297_, v_fvarId_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___x_3288_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v_e_3299_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3314_, lean_object* v_e_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
if (lean_obj_tag(v_e_3315_) == 1)
{
lean_object* v_fvarId_3321_; lean_object* v___x_3322_; 
v_fvarId_3321_ = lean_ctor_get(v_e_3315_, 0);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc(v___y_3317_);
lean_inc_ref(v___y_3316_);
lean_inc(v_fvarId_3321_);
v___x_3322_ = lean_apply_6(v___f_3314_, v_fvarId_3321_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, lean_box(0));
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3348_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3348_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3348_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
if (lean_obj_tag(v_a_3323_) == 1)
{
lean_object* v_val_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3343_; 
lean_del_object(v___x_3325_);
lean_dec_ref(v_e_3315_);
v_val_3327_ = lean_ctor_get(v_a_3323_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_a_3323_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3329_ = v_a_3323_;
v_isShared_3330_ = v_isSharedCheck_3343_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_val_3327_);
lean_dec(v_a_3323_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3343_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3342_; 
v___x_3331_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3327_, v___y_3317_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3342_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3342_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v_a_3332_);
v___x_3337_ = v___x_3329_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3339_; 
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3337_);
v___x_3339_ = v___x_3334_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
lean_dec(v_a_3323_);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_e_3315_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3344_);
v___x_3346_ = v___x_3325_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v_e_3315_);
v_a_3349_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3322_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3322_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v_e_3315_);
lean_dec_ref(v___f_3314_);
v___x_3357_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3359_, lean_object* v_e_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3359_, v_e_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3367_, lean_object* v_e_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Expr_getAppFn(v_e_3368_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_fvarId_3375_; lean_object* v___x_3376_; 
v_fvarId_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_fvarId_3375_);
lean_dec_ref(v___x_3374_);
lean_inc(v___y_3372_);
lean_inc_ref(v___y_3371_);
lean_inc(v___y_3370_);
lean_inc_ref(v___y_3369_);
v___x_3376_ = lean_apply_6(v___f_3367_, v_fvarId_3375_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, lean_box(0));
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3409_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3409_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3409_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
if (lean_obj_tag(v_a_3377_) == 1)
{
lean_object* v_val_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3404_; 
lean_del_object(v___x_3379_);
v_val_3381_ = lean_ctor_get(v_a_3377_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3383_ = v_a_3377_;
v_isShared_3384_ = v_isSharedCheck_3404_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_val_3381_);
lean_dec(v_a_3377_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3404_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3403_; 
v___x_3385_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3381_, v___y_3370_);
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3403_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3403_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_dummy_3390_; lean_object* v_nargs_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v_dummy_3390_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3391_ = l_Lean_Expr_getAppNumArgs(v_e_3368_);
lean_inc(v_nargs_3391_);
v___x_3392_ = lean_mk_array(v_nargs_3391_, v_dummy_3390_);
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_nat_sub(v_nargs_3391_, v___x_3393_);
lean_dec(v_nargs_3391_);
v___x_3395_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3368_, v___x_3392_, v___x_3394_);
v___x_3396_ = l_Lean_Expr_beta(v_a_3386_, v___x_3395_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3396_);
v___x_3398_ = v___x_3383_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3398_);
v___x_3400_ = v___x_3388_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_dec(v_a_3377_);
lean_dec_ref(v_e_3368_);
v___x_3405_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3405_);
v___x_3407_ = v___x_3379_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v_e_3368_);
v_a_3410_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3376_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3376_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref(v___x_3374_);
lean_dec_ref(v_e_3368_);
lean_dec_ref(v___f_3367_);
v___x_3418_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3420_, lean_object* v_e_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3420_, v_e_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_apply_1(v_x_3429_, lean_box(0));
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3437_, lean_object* v_x_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3437_, v_x_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3445_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3459_, lean_object* v___y_3460_, lean_object* v_b_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3467_; 
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
lean_inc(v___y_3463_);
lean_inc_ref(v___y_3462_);
lean_inc(v___y_3460_);
v___x_3467_ = lean_apply_7(v_k_3459_, v_b_3461_, v___y_3460_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, lean_box(0));
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3468_, lean_object* v___y_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3468_, v___y_3469_, v_b_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3469_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3477_, uint8_t v_bi_3478_, lean_object* v_type_3479_, lean_object* v_k_3480_, uint8_t v_kind_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___f_3488_; lean_object* v___x_3489_; 
lean_inc(v___y_3482_);
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3488_, 0, v_k_3480_);
lean_closure_set(v___f_3488_, 1, v___y_3482_);
v___x_3489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3477_, v_bi_3478_, v_type_3479_, v___f_3488_, v_kind_3481_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
if (lean_obj_tag(v___x_3489_) == 0)
{
return v___x_3489_;
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3498_, lean_object* v_bi_3499_, lean_object* v_type_3500_, lean_object* v_k_3501_, lean_object* v_kind_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
uint8_t v_bi_boxed_3509_; uint8_t v_kind_boxed_3510_; lean_object* v_res_3511_; 
v_bi_boxed_3509_ = lean_unbox(v_bi_3499_);
v_kind_boxed_3510_ = lean_unbox(v_kind_3502_);
v_res_3511_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3498_, v_bi_boxed_3509_, v_type_3500_, v_k_3501_, v_kind_boxed_3510_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3512_, lean_object* v_type_3513_, lean_object* v_val_3514_, lean_object* v_k_3515_, uint8_t v_nondep_3516_, uint8_t v_kind_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___f_3524_; lean_object* v___x_3525_; 
lean_inc(v___y_3518_);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3524_, 0, v_k_3515_);
lean_closure_set(v___f_3524_, 1, v___y_3518_);
v___x_3525_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3512_, v_type_3513_, v_val_3514_, v___f_3524_, v_nondep_3516_, v_kind_3517_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3525_) == 0)
{
return v___x_3525_;
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3534_, lean_object* v_type_3535_, lean_object* v_val_3536_, lean_object* v_k_3537_, lean_object* v_nondep_3538_, lean_object* v_kind_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v_nondep_boxed_3546_; uint8_t v_kind_boxed_3547_; lean_object* v_res_3548_; 
v_nondep_boxed_3546_ = lean_unbox(v_nondep_3538_);
v_kind_boxed_3547_ = lean_unbox(v_kind_3539_);
v_res_3548_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3534_, v_type_3535_, v_val_3536_, v_k_3537_, v_nondep_boxed_3546_, v_kind_boxed_3547_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3549_, lean_object* v_x_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_apply_1(v_x_3550_, lean_box(0));
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3558_, lean_object* v_x_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3558_, v_x_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3566_){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3569_, 0, v_ref_3566_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3571_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___y_3582_; lean_object* v_fileName_3591_; lean_object* v_fileMap_3592_; lean_object* v_options_3593_; lean_object* v_currRecDepth_3594_; lean_object* v_maxRecDepth_3595_; lean_object* v_ref_3596_; lean_object* v_currNamespace_3597_; lean_object* v_openDecls_3598_; lean_object* v_initHeartbeats_3599_; lean_object* v_maxHeartbeats_3600_; lean_object* v_quotContext_3601_; lean_object* v_currMacroScope_3602_; uint8_t v_diag_3603_; lean_object* v_cancelTk_x3f_3604_; uint8_t v_suppressElabErrors_3605_; lean_object* v_inheritedTraceOptions_3606_; uint8_t v___x_3607_; 
v_fileName_3591_ = lean_ctor_get(v___y_3578_, 0);
v_fileMap_3592_ = lean_ctor_get(v___y_3578_, 1);
v_options_3593_ = lean_ctor_get(v___y_3578_, 2);
v_currRecDepth_3594_ = lean_ctor_get(v___y_3578_, 3);
v_maxRecDepth_3595_ = lean_ctor_get(v___y_3578_, 4);
v_ref_3596_ = lean_ctor_get(v___y_3578_, 5);
v_currNamespace_3597_ = lean_ctor_get(v___y_3578_, 6);
v_openDecls_3598_ = lean_ctor_get(v___y_3578_, 7);
v_initHeartbeats_3599_ = lean_ctor_get(v___y_3578_, 8);
v_maxHeartbeats_3600_ = lean_ctor_get(v___y_3578_, 9);
v_quotContext_3601_ = lean_ctor_get(v___y_3578_, 10);
v_currMacroScope_3602_ = lean_ctor_get(v___y_3578_, 11);
v_diag_3603_ = lean_ctor_get_uint8(v___y_3578_, sizeof(void*)*14);
v_cancelTk_x3f_3604_ = lean_ctor_get(v___y_3578_, 12);
v_suppressElabErrors_3605_ = lean_ctor_get_uint8(v___y_3578_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3606_ = lean_ctor_get(v___y_3578_, 13);
v___x_3607_ = lean_nat_dec_eq(v_currRecDepth_3594_, v_maxRecDepth_3595_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v_currRecDepth_3594_, v___x_3608_);
lean_inc_ref(v_inheritedTraceOptions_3606_);
lean_inc(v_cancelTk_x3f_3604_);
lean_inc(v_currMacroScope_3602_);
lean_inc(v_quotContext_3601_);
lean_inc(v_maxHeartbeats_3600_);
lean_inc(v_initHeartbeats_3599_);
lean_inc(v_openDecls_3598_);
lean_inc(v_currNamespace_3597_);
lean_inc(v_ref_3596_);
lean_inc(v_maxRecDepth_3595_);
lean_inc_ref(v_options_3593_);
lean_inc_ref(v_fileMap_3592_);
lean_inc_ref(v_fileName_3591_);
v___x_3610_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3610_, 0, v_fileName_3591_);
lean_ctor_set(v___x_3610_, 1, v_fileMap_3592_);
lean_ctor_set(v___x_3610_, 2, v_options_3593_);
lean_ctor_set(v___x_3610_, 3, v___x_3609_);
lean_ctor_set(v___x_3610_, 4, v_maxRecDepth_3595_);
lean_ctor_set(v___x_3610_, 5, v_ref_3596_);
lean_ctor_set(v___x_3610_, 6, v_currNamespace_3597_);
lean_ctor_set(v___x_3610_, 7, v_openDecls_3598_);
lean_ctor_set(v___x_3610_, 8, v_initHeartbeats_3599_);
lean_ctor_set(v___x_3610_, 9, v_maxHeartbeats_3600_);
lean_ctor_set(v___x_3610_, 10, v_quotContext_3601_);
lean_ctor_set(v___x_3610_, 11, v_currMacroScope_3602_);
lean_ctor_set(v___x_3610_, 12, v_cancelTk_x3f_3604_);
lean_ctor_set(v___x_3610_, 13, v_inheritedTraceOptions_3606_);
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*14, v_diag_3603_);
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*14 + 1, v_suppressElabErrors_3605_);
lean_inc(v___y_3579_);
lean_inc(v___y_3577_);
lean_inc_ref(v___y_3576_);
lean_inc(v___y_3575_);
v___x_3611_ = lean_apply_6(v_x_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___x_3610_, v___y_3579_, lean_box(0));
v___y_3582_ = v___x_3611_;
goto v___jp_3581_;
}
else
{
lean_object* v___x_3612_; 
lean_dec_ref(v_x_3574_);
lean_inc(v_ref_3596_);
v___x_3612_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3596_);
v___y_3582_ = v___x_3612_;
goto v___jp_3581_;
}
v___jp_3581_:
{
if (lean_obj_tag(v___y_3582_) == 0)
{
return v___y_3582_;
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___y_3582_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___y_3582_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___y_3582_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___y_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3621_, lean_object* v_pre_3622_, lean_object* v_post_3623_, uint8_t v_usedLetOnly_3624_, uint8_t v_skipConstInApp_3625_, uint8_t v_skipInstances_3626_, lean_object* v_body_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_array_push(v_fvars_3621_, v_x_3628_);
v___x_3636_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3622_, v_post_3623_, v_usedLetOnly_3624_, v_skipConstInApp_3625_, v_skipInstances_3626_, v___x_3635_, v_body_3627_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3637_, lean_object* v_pre_3638_, lean_object* v_post_3639_, lean_object* v_usedLetOnly_3640_, lean_object* v_skipConstInApp_3641_, lean_object* v_skipInstances_3642_, lean_object* v_body_3643_, lean_object* v_x_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v_usedLetOnly_boxed_3651_; uint8_t v_skipConstInApp_boxed_3652_; uint8_t v_skipInstances_boxed_3653_; lean_object* v_res_3654_; 
v_usedLetOnly_boxed_3651_ = lean_unbox(v_usedLetOnly_3640_);
v_skipConstInApp_boxed_3652_ = lean_unbox(v_skipConstInApp_3641_);
v_skipInstances_boxed_3653_ = lean_unbox(v_skipInstances_3642_);
v_res_3654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3637_, v_pre_3638_, v_post_3639_, v_usedLetOnly_boxed_3651_, v_skipConstInApp_boxed_3652_, v_skipInstances_boxed_3653_, v_body_3643_, v_x_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3655_, lean_object* v_post_3656_, uint8_t v_usedLetOnly_3657_, uint8_t v_skipConstInApp_3658_, uint8_t v_skipInstances_3659_, lean_object* v_e_3660_, lean_object* v_a_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; 
lean_inc_ref(v_post_3656_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
lean_inc_ref(v_e_3660_);
v___x_3667_ = lean_apply_6(v_post_3656_, v_e_3660_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3686_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3686_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3686_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
switch(lean_obj_tag(v_a_3668_))
{
case 0:
{
lean_object* v_e_3672_; lean_object* v___x_3674_; 
lean_dec_ref(v_e_3660_);
lean_dec_ref(v_post_3656_);
lean_dec_ref(v_pre_3655_);
v_e_3672_ = lean_ctor_get(v_a_3668_, 0);
lean_inc_ref(v_e_3672_);
lean_dec_ref(v_a_3668_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_e_3672_);
v___x_3674_ = v___x_3670_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_e_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
case 1:
{
lean_object* v_e_3676_; lean_object* v___x_3677_; 
lean_del_object(v___x_3670_);
lean_dec_ref(v_e_3660_);
v_e_3676_ = lean_ctor_get(v_a_3668_, 0);
lean_inc_ref(v_e_3676_);
lean_dec_ref(v_a_3668_);
v___x_3677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3655_, v_post_3656_, v_usedLetOnly_3657_, v_skipConstInApp_3658_, v_skipInstances_3659_, v_e_3676_, v_a_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3677_;
}
default: 
{
lean_object* v_e_x3f_3678_; 
lean_dec_ref(v_post_3656_);
lean_dec_ref(v_pre_3655_);
v_e_x3f_3678_ = lean_ctor_get(v_a_3668_, 0);
lean_inc(v_e_x3f_3678_);
lean_dec_ref(v_a_3668_);
if (lean_obj_tag(v_e_x3f_3678_) == 0)
{
lean_object* v___x_3680_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_e_3660_);
v___x_3680_ = v___x_3670_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_e_3660_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
else
{
lean_object* v_val_3682_; lean_object* v___x_3684_; 
lean_dec_ref(v_e_3660_);
v_val_3682_ = lean_ctor_get(v_e_x3f_3678_, 0);
lean_inc(v_val_3682_);
lean_dec_ref(v_e_x3f_3678_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_val_3682_);
v___x_3684_ = v___x_3670_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_val_3682_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec_ref(v_e_3660_);
lean_dec_ref(v_post_3656_);
lean_dec_ref(v_pre_3655_);
v_a_3687_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3667_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3667_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3695_, lean_object* v_post_3696_, uint8_t v_usedLetOnly_3697_, uint8_t v_skipConstInApp_3698_, uint8_t v_skipInstances_3699_, lean_object* v_fvars_3700_, lean_object* v_e_3701_, lean_object* v_a_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
if (lean_obj_tag(v_e_3701_) == 6)
{
lean_object* v_binderName_3708_; lean_object* v_binderType_3709_; lean_object* v_body_3710_; uint8_t v_binderInfo_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_binderName_3708_ = lean_ctor_get(v_e_3701_, 0);
lean_inc(v_binderName_3708_);
v_binderType_3709_ = lean_ctor_get(v_e_3701_, 1);
lean_inc_ref(v_binderType_3709_);
v_body_3710_ = lean_ctor_get(v_e_3701_, 2);
lean_inc_ref(v_body_3710_);
v_binderInfo_3711_ = lean_ctor_get_uint8(v_e_3701_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3701_);
v___x_3712_ = lean_expr_instantiate_rev(v_binderType_3709_, v_fvars_3700_);
lean_dec_ref(v_binderType_3709_);
lean_inc_ref(v_post_3696_);
lean_inc_ref(v_pre_3695_);
v___x_3713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3695_, v_post_3696_, v_usedLetOnly_3697_, v_skipConstInApp_3698_, v_skipInstances_3699_, v___x_3712_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___f_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v___x_3713_);
v___x_3715_ = lean_box(v_usedLetOnly_3697_);
v___x_3716_ = lean_box(v_skipConstInApp_3698_);
v___x_3717_ = lean_box(v_skipInstances_3699_);
v___f_3718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3718_, 0, v_fvars_3700_);
lean_closure_set(v___f_3718_, 1, v_pre_3695_);
lean_closure_set(v___f_3718_, 2, v_post_3696_);
lean_closure_set(v___f_3718_, 3, v___x_3715_);
lean_closure_set(v___f_3718_, 4, v___x_3716_);
lean_closure_set(v___f_3718_, 5, v___x_3717_);
lean_closure_set(v___f_3718_, 6, v_body_3710_);
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3708_, v_binderInfo_3711_, v_a_3714_, v___f_3718_, v___x_3719_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3720_;
}
else
{
lean_dec_ref(v_body_3710_);
lean_dec(v_binderName_3708_);
lean_dec_ref(v_fvars_3700_);
lean_dec_ref(v_post_3696_);
lean_dec_ref(v_pre_3695_);
return v___x_3713_;
}
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_expr_instantiate_rev(v_e_3701_, v_fvars_3700_);
lean_dec_ref(v_e_3701_);
lean_inc_ref(v_post_3696_);
lean_inc_ref(v_pre_3695_);
v___x_3722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3695_, v_post_3696_, v_usedLetOnly_3697_, v_skipConstInApp_3698_, v_skipInstances_3699_, v___x_3721_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; uint8_t v___x_3724_; uint8_t v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = 0;
v___x_3725_ = 1;
v___x_3726_ = 1;
v___x_3727_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3700_, v_a_3723_, v___x_3724_, v_usedLetOnly_3697_, v___x_3724_, v___x_3725_, v___x_3726_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec_ref(v_fvars_3700_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3695_, v_post_3696_, v_usedLetOnly_3697_, v_skipConstInApp_3698_, v_skipInstances_3699_, v_a_3728_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3729_;
}
else
{
lean_dec_ref(v_post_3696_);
lean_dec_ref(v_pre_3695_);
return v___x_3727_;
}
}
else
{
lean_dec_ref(v_fvars_3700_);
lean_dec_ref(v_post_3696_);
lean_dec_ref(v_pre_3695_);
return v___x_3722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3730_, lean_object* v_pre_3731_, lean_object* v_post_3732_, uint8_t v_usedLetOnly_3733_, uint8_t v_skipConstInApp_3734_, uint8_t v_skipInstances_3735_, lean_object* v_body_3736_, lean_object* v_x_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_array_push(v_fvars_3730_, v_x_3737_);
v___x_3745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3731_, v_post_3732_, v_usedLetOnly_3733_, v_skipConstInApp_3734_, v_skipInstances_3735_, v___x_3744_, v_body_3736_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3746_, lean_object* v_pre_3747_, lean_object* v_post_3748_, lean_object* v_usedLetOnly_3749_, lean_object* v_skipConstInApp_3750_, lean_object* v_skipInstances_3751_, lean_object* v_body_3752_, lean_object* v_x_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_usedLetOnly_boxed_3760_; uint8_t v_skipConstInApp_boxed_3761_; uint8_t v_skipInstances_boxed_3762_; lean_object* v_res_3763_; 
v_usedLetOnly_boxed_3760_ = lean_unbox(v_usedLetOnly_3749_);
v_skipConstInApp_boxed_3761_ = lean_unbox(v_skipConstInApp_3750_);
v_skipInstances_boxed_3762_ = lean_unbox(v_skipInstances_3751_);
v_res_3763_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3746_, v_pre_3747_, v_post_3748_, v_usedLetOnly_boxed_3760_, v_skipConstInApp_boxed_3761_, v_skipInstances_boxed_3762_, v_body_3752_, v_x_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3764_, lean_object* v_post_3765_, uint8_t v_usedLetOnly_3766_, uint8_t v_skipConstInApp_3767_, uint8_t v_skipInstances_3768_, lean_object* v_fvars_3769_, lean_object* v_e_3770_, lean_object* v_a_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
if (lean_obj_tag(v_e_3770_) == 8)
{
lean_object* v_declName_3777_; lean_object* v_type_3778_; lean_object* v_value_3779_; lean_object* v_body_3780_; uint8_t v_nondep_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_declName_3777_ = lean_ctor_get(v_e_3770_, 0);
lean_inc(v_declName_3777_);
v_type_3778_ = lean_ctor_get(v_e_3770_, 1);
lean_inc_ref(v_type_3778_);
v_value_3779_ = lean_ctor_get(v_e_3770_, 2);
lean_inc_ref(v_value_3779_);
v_body_3780_ = lean_ctor_get(v_e_3770_, 3);
lean_inc_ref(v_body_3780_);
v_nondep_3781_ = lean_ctor_get_uint8(v_e_3770_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3770_);
v___x_3782_ = lean_expr_instantiate_rev(v_type_3778_, v_fvars_3769_);
lean_dec_ref(v_type_3778_);
lean_inc_ref(v_post_3765_);
lean_inc_ref(v_pre_3764_);
v___x_3783_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3764_, v_post_3765_, v_usedLetOnly_3766_, v_skipConstInApp_3767_, v_skipInstances_3768_, v___x_3782_, v_a_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = lean_expr_instantiate_rev(v_value_3779_, v_fvars_3769_);
lean_dec_ref(v_value_3779_);
lean_inc_ref(v_post_3765_);
lean_inc_ref(v_pre_3764_);
v___x_3786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3764_, v_post_3765_, v_usedLetOnly_3766_, v_skipConstInApp_3767_, v_skipInstances_3768_, v___x_3785_, v_a_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___f_3791_; uint8_t v___x_3792_; lean_object* v___x_3793_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = lean_box(v_usedLetOnly_3766_);
v___x_3789_ = lean_box(v_skipConstInApp_3767_);
v___x_3790_ = lean_box(v_skipInstances_3768_);
v___f_3791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3791_, 0, v_fvars_3769_);
lean_closure_set(v___f_3791_, 1, v_pre_3764_);
lean_closure_set(v___f_3791_, 2, v_post_3765_);
lean_closure_set(v___f_3791_, 3, v___x_3788_);
lean_closure_set(v___f_3791_, 4, v___x_3789_);
lean_closure_set(v___f_3791_, 5, v___x_3790_);
lean_closure_set(v___f_3791_, 6, v_body_3780_);
v___x_3792_ = 0;
v___x_3793_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3777_, v_a_3784_, v_a_3787_, v___f_3791_, v_nondep_3781_, v___x_3792_, v_a_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
return v___x_3793_;
}
else
{
lean_dec(v_a_3784_);
lean_dec_ref(v_body_3780_);
lean_dec(v_declName_3777_);
lean_dec_ref(v_fvars_3769_);
lean_dec_ref(v_post_3765_);
lean_dec_ref(v_pre_3764_);
return v___x_3786_;
}
}
else
{
lean_dec_ref(v_body_3780_);
lean_dec_ref(v_value_3779_);
lean_dec(v_declName_3777_);
lean_dec_ref(v_fvars_3769_);
lean_dec_ref(v_post_3765_);
lean_dec_ref(v_pre_3764_);
return v___x_3783_;
}
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = lean_expr_instantiate_rev(v_e_3770_, v_fvars_3769_);
lean_dec_ref(v_e_3770_);
lean_inc_ref(v_post_3765_);
lean_inc_ref(v_pre_3764_);
v___x_3795_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3764_, v_post_3765_, v_usedLetOnly_3766_, v_skipConstInApp_3767_, v_skipInstances_3768_, v___x_3794_, v_a_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; uint8_t v___x_3797_; uint8_t v___x_3798_; lean_object* v___x_3799_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = 0;
v___x_3798_ = 1;
v___x_3799_ = l_Lean_Meta_mkLetFVars(v_fvars_3769_, v_a_3796_, v_usedLetOnly_3766_, v___x_3797_, v___x_3798_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec_ref(v_fvars_3769_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3801_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref(v___x_3799_);
v___x_3801_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3764_, v_post_3765_, v_usedLetOnly_3766_, v_skipConstInApp_3767_, v_skipInstances_3768_, v_a_3800_, v_a_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
return v___x_3801_;
}
else
{
lean_dec_ref(v_post_3765_);
lean_dec_ref(v_pre_3764_);
return v___x_3799_;
}
}
else
{
lean_dec_ref(v_fvars_3769_);
lean_dec_ref(v_post_3765_);
lean_dec_ref(v_pre_3764_);
return v___x_3795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3802_, lean_object* v_post_3803_, uint8_t v_usedLetOnly_3804_, uint8_t v_skipConstInApp_3805_, uint8_t v_skipInstances_3806_, size_t v_sz_3807_, size_t v_i_3808_, lean_object* v_bs_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
uint8_t v___x_3816_; 
v___x_3816_ = lean_usize_dec_lt(v_i_3808_, v_sz_3807_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; 
lean_dec_ref(v_post_3803_);
lean_dec_ref(v_pre_3802_);
v___x_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3817_, 0, v_bs_3809_);
return v___x_3817_;
}
else
{
lean_object* v_v_3818_; lean_object* v___x_3819_; 
v_v_3818_ = lean_array_uget_borrowed(v_bs_3809_, v_i_3808_);
lean_inc(v_v_3818_);
lean_inc_ref(v_post_3803_);
lean_inc_ref(v_pre_3802_);
v___x_3819_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3802_, v_post_3803_, v_usedLetOnly_3804_, v_skipConstInApp_3805_, v_skipInstances_3806_, v_v_3818_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v_bs_x27_3822_; size_t v___x_3823_; size_t v___x_3824_; lean_object* v___x_3825_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v_bs_x27_3822_ = lean_array_uset(v_bs_3809_, v_i_3808_, v___x_3821_);
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_add(v_i_3808_, v___x_3823_);
v___x_3825_ = lean_array_uset(v_bs_x27_3822_, v_i_3808_, v_a_3820_);
v_i_3808_ = v___x_3824_;
v_bs_3809_ = v___x_3825_;
goto _start;
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v_bs_3809_);
lean_dec_ref(v_post_3803_);
lean_dec_ref(v_pre_3802_);
v_a_3827_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3819_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3819_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3835_, lean_object* v_post_3836_, uint8_t v_usedLetOnly_3837_, uint8_t v_skipConstInApp_3838_, uint8_t v_skipInstances_3839_, lean_object* v___x_3840_, lean_object* v___y_3841_, lean_object* v_b_3842_, lean_object* v_a_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3835_, v_post_3836_, v_usedLetOnly_3837_, v_skipConstInApp_3838_, v_skipInstances_3839_, v___x_3840_, v___y_3841_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3859_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3852_ = v___x_3849_;
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3854_ = lean_array_fset(v_b_3842_, v_a_3843_, v_a_3850_);
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3855_);
v___x_3857_ = v___x_3852_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_b_3842_);
v_a_3860_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3849_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3849_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3868_, lean_object* v_post_3869_, lean_object* v_usedLetOnly_3870_, lean_object* v_skipConstInApp_3871_, lean_object* v_skipInstances_3872_, lean_object* v___x_3873_, lean_object* v___y_3874_, lean_object* v_b_3875_, lean_object* v_a_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
uint8_t v_usedLetOnly_boxed_3882_; uint8_t v_skipConstInApp_boxed_3883_; uint8_t v_skipInstances_boxed_3884_; lean_object* v_res_3885_; 
v_usedLetOnly_boxed_3882_ = lean_unbox(v_usedLetOnly_3870_);
v_skipConstInApp_boxed_3883_ = lean_unbox(v_skipConstInApp_3871_);
v_skipInstances_boxed_3884_ = lean_unbox(v_skipInstances_3872_);
v_res_3885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3868_, v_post_3869_, v_usedLetOnly_boxed_3882_, v_skipConstInApp_boxed_3883_, v_skipInstances_boxed_3884_, v___x_3873_, v___y_3874_, v_b_3875_, v_a_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v_a_3876_);
lean_dec(v___y_3874_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3886_, lean_object* v___x_3887_, lean_object* v_pre_3888_, lean_object* v_post_3889_, uint8_t v_usedLetOnly_3890_, uint8_t v_skipConstInApp_3891_, uint8_t v_skipInstances_3892_, lean_object* v_a_3893_, lean_object* v_b_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___y_3902_; uint8_t v___x_3925_; 
v___x_3925_ = lean_nat_dec_lt(v_a_3893_, v_upperBound_3886_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; 
lean_dec(v_a_3893_);
lean_dec_ref(v_post_3889_);
lean_dec_ref(v_pre_3888_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_b_3894_);
return v___x_3926_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; uint8_t v___x_3929_; 
v___x_3927_ = lean_array_fget_borrowed(v_b_3894_, v_a_3893_);
v___x_3928_ = lean_array_get_size(v___x_3887_);
v___x_3929_ = lean_nat_dec_lt(v_a_3893_, v___x_3928_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___f_3933_; 
lean_inc(v___x_3927_);
v___x_3930_ = lean_box(v_usedLetOnly_3890_);
v___x_3931_ = lean_box(v_skipConstInApp_3891_);
v___x_3932_ = lean_box(v_skipInstances_3892_);
lean_inc(v_a_3893_);
lean_inc(v___y_3895_);
lean_inc_ref(v_post_3889_);
lean_inc_ref(v_pre_3888_);
v___f_3933_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3933_, 0, v_pre_3888_);
lean_closure_set(v___f_3933_, 1, v_post_3889_);
lean_closure_set(v___f_3933_, 2, v___x_3930_);
lean_closure_set(v___f_3933_, 3, v___x_3931_);
lean_closure_set(v___f_3933_, 4, v___x_3932_);
lean_closure_set(v___f_3933_, 5, v___x_3927_);
lean_closure_set(v___f_3933_, 6, v___y_3895_);
lean_closure_set(v___f_3933_, 7, v_b_3894_);
lean_closure_set(v___f_3933_, 8, v_a_3893_);
v___y_3902_ = v___f_3933_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3934_; uint8_t v_isInstance_3935_; 
v___x_3934_ = lean_array_fget_borrowed(v___x_3887_, v_a_3893_);
v_isInstance_3935_ = lean_ctor_get_uint8(v___x_3934_, sizeof(void*)*1 + 4);
if (v_isInstance_3935_ == 0)
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___f_3939_; 
lean_inc(v___x_3927_);
v___x_3936_ = lean_box(v_usedLetOnly_3890_);
v___x_3937_ = lean_box(v_skipConstInApp_3891_);
v___x_3938_ = lean_box(v_skipInstances_3892_);
lean_inc(v_a_3893_);
lean_inc(v___y_3895_);
lean_inc_ref(v_post_3889_);
lean_inc_ref(v_pre_3888_);
v___f_3939_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3939_, 0, v_pre_3888_);
lean_closure_set(v___f_3939_, 1, v_post_3889_);
lean_closure_set(v___f_3939_, 2, v___x_3936_);
lean_closure_set(v___f_3939_, 3, v___x_3937_);
lean_closure_set(v___f_3939_, 4, v___x_3938_);
lean_closure_set(v___f_3939_, 5, v___x_3927_);
lean_closure_set(v___f_3939_, 6, v___y_3895_);
lean_closure_set(v___f_3939_, 7, v_b_3894_);
lean_closure_set(v___f_3939_, 8, v_a_3893_);
v___y_3902_ = v___f_3939_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3940_; lean_object* v___f_3941_; 
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v_b_3894_);
v___f_3941_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3941_, 0, v___x_3940_);
v___y_3902_ = v___f_3941_;
goto v___jp_3901_;
}
}
}
v___jp_3901_:
{
lean_object* v___x_3903_; 
lean_inc(v___y_3899_);
lean_inc_ref(v___y_3898_);
lean_inc(v___y_3897_);
lean_inc_ref(v___y_3896_);
v___x_3903_ = lean_apply_5(v___y_3902_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, lean_box(0));
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3916_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3916_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3916_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
if (lean_obj_tag(v_a_3904_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; 
lean_dec(v_a_3893_);
lean_dec_ref(v_post_3889_);
lean_dec_ref(v_pre_3888_);
v_a_3908_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v_a_3904_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_a_3908_);
v___x_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_del_object(v___x_3906_);
v_a_3912_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_a_3912_);
lean_dec_ref(v_a_3904_);
v___x_3913_ = lean_unsigned_to_nat(1u);
v___x_3914_ = lean_nat_add(v_a_3893_, v___x_3913_);
lean_dec(v_a_3893_);
v_a_3893_ = v___x_3914_;
v_b_3894_ = v_a_3912_;
goto _start;
}
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v_a_3893_);
lean_dec_ref(v_post_3889_);
lean_dec_ref(v_pre_3888_);
v_a_3917_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3903_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3903_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_3942_, lean_object* v_pre_3943_, lean_object* v_post_3944_, uint8_t v_usedLetOnly_3945_, uint8_t v_skipConstInApp_3946_, lean_object* v_x_3947_, lean_object* v_x_3948_, lean_object* v_x_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_f_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; 
if (lean_obj_tag(v_x_3947_) == 5)
{
lean_object* v_fn_4005_; lean_object* v_arg_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v_fn_4005_ = lean_ctor_get(v_x_3947_, 0);
lean_inc_ref(v_fn_4005_);
v_arg_4006_ = lean_ctor_get(v_x_3947_, 1);
lean_inc_ref(v_arg_4006_);
lean_dec_ref(v_x_3947_);
v___x_4007_ = lean_array_set(v_x_3948_, v_x_3949_, v_arg_4006_);
v___x_4008_ = lean_unsigned_to_nat(1u);
v___x_4009_ = lean_nat_sub(v_x_3949_, v___x_4008_);
lean_dec(v_x_3949_);
v_x_3947_ = v_fn_4005_;
v_x_3948_ = v___x_4007_;
v_x_3949_ = v___x_4009_;
goto _start;
}
else
{
lean_dec(v_x_3949_);
if (v_skipConstInApp_3946_ == 0)
{
goto v___jp_4002_;
}
else
{
uint8_t v___x_4011_; 
v___x_4011_ = l_Lean_Expr_isConst(v_x_3947_);
if (v___x_4011_ == 0)
{
goto v___jp_4002_;
}
else
{
v_f_3957_ = v_x_3947_;
v___y_3958_ = v___y_3950_;
v___y_3959_ = v___y_3951_;
v___y_3960_ = v___y_3952_;
v___y_3961_ = v___y_3953_;
v___y_3962_ = v___y_3954_;
goto v___jp_3956_;
}
}
}
v___jp_3956_:
{
if (v_skipInstances_3942_ == 0)
{
size_t v_sz_3963_; size_t v___x_3964_; lean_object* v___x_3965_; 
v_sz_3963_ = lean_array_size(v_x_3948_);
v___x_3964_ = ((size_t)0ULL);
lean_inc_ref(v_post_3944_);
lean_inc_ref(v_pre_3943_);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_3943_, v_post_3944_, v_usedLetOnly_3945_, v_skipConstInApp_3946_, v_skipInstances_3942_, v_sz_3963_, v___x_3964_, v_x_3948_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
v___x_3967_ = l_Lean_mkAppN(v_f_3957_, v_a_3966_);
lean_dec(v_a_3966_);
v___x_3968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3943_, v_post_3944_, v_usedLetOnly_3945_, v_skipConstInApp_3946_, v_skipInstances_3942_, v___x_3967_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3968_;
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec_ref(v_f_3957_);
lean_dec_ref(v_post_3944_);
lean_dec_ref(v_pre_3943_);
v_a_3969_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3965_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3965_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_array_get_size(v_x_3948_);
lean_inc_ref(v_f_3957_);
v___x_3978_ = l_Lean_Meta_getFunInfoNArgs(v_f_3957_, v___x_3977_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v_paramInfo_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref(v___x_3978_);
v_paramInfo_3980_ = lean_ctor_get(v_a_3979_, 0);
lean_inc_ref(v_paramInfo_3980_);
lean_dec(v_a_3979_);
v___x_3981_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3944_);
lean_inc_ref(v_pre_3943_);
v___x_3982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_3977_, v_paramInfo_3980_, v_pre_3943_, v_post_3944_, v_usedLetOnly_3945_, v_skipConstInApp_3946_, v_skipInstances_3942_, v___x_3981_, v_x_3948_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec_ref(v_paramInfo_3980_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = l_Lean_mkAppN(v_f_3957_, v_a_3983_);
lean_dec(v_a_3983_);
v___x_3985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3943_, v_post_3944_, v_usedLetOnly_3945_, v_skipConstInApp_3946_, v_skipInstances_3942_, v___x_3984_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3985_;
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec_ref(v_f_3957_);
lean_dec_ref(v_post_3944_);
lean_dec_ref(v_pre_3943_);
v_a_3986_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3982_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3982_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_f_3957_);
lean_dec_ref(v_x_3948_);
lean_dec_ref(v_post_3944_);
lean_dec_ref(v_pre_3943_);
v_a_3994_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3978_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3978_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
v___jp_4002_:
{
lean_object* v___x_4003_; 
lean_inc_ref(v_post_3944_);
lean_inc_ref(v_pre_3943_);
v___x_4003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3943_, v_post_3944_, v_usedLetOnly_3945_, v_skipConstInApp_3946_, v_skipInstances_3942_, v_x_3947_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref(v___x_4003_);
v_f_3957_ = v_a_4004_;
v___y_3958_ = v___y_3950_;
v___y_3959_ = v___y_3951_;
v___y_3960_ = v___y_3952_;
v___y_3961_ = v___y_3953_;
v___y_3962_ = v___y_3954_;
goto v___jp_3956_;
}
else
{
lean_dec_ref(v_x_3948_);
lean_dec_ref(v_post_3944_);
lean_dec_ref(v_pre_3943_);
return v___x_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v_pre_4012_, lean_object* v_e_4013_, lean_object* v_post_4014_, uint8_t v_usedLetOnly_4015_, uint8_t v_skipConstInApp_4016_, uint8_t v_skipInstances_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; 
lean_inc_ref(v_pre_4012_);
lean_inc(v___y_4022_);
lean_inc_ref(v___y_4021_);
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
lean_inc_ref(v_e_4013_);
v___x_4024_ = lean_apply_6(v_pre_4012_, v_e_4013_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, lean_box(0));
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4073_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4027_ = v___x_4024_;
v_isShared_4028_ = v_isSharedCheck_4073_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4024_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4073_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___y_4030_; 
switch(lean_obj_tag(v_a_4025_))
{
case 0:
{
lean_object* v_e_4065_; lean_object* v___x_4067_; 
lean_dec_ref(v_post_4014_);
lean_dec_ref(v_e_4013_);
lean_dec_ref(v_pre_4012_);
v_e_4065_ = lean_ctor_get(v_a_4025_, 0);
lean_inc_ref(v_e_4065_);
lean_dec_ref(v_a_4025_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v_e_4065_);
v___x_4067_ = v___x_4027_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_e_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
case 1:
{
lean_object* v_e_4069_; lean_object* v___x_4070_; 
lean_del_object(v___x_4027_);
lean_dec_ref(v_e_4013_);
v_e_4069_ = lean_ctor_get(v_a_4025_, 0);
lean_inc_ref(v_e_4069_);
lean_dec_ref(v_a_4025_);
v___x_4070_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v_e_4069_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4070_;
}
default: 
{
lean_object* v_e_x3f_4071_; 
lean_del_object(v___x_4027_);
v_e_x3f_4071_ = lean_ctor_get(v_a_4025_, 0);
lean_inc(v_e_x3f_4071_);
lean_dec_ref(v_a_4025_);
if (lean_obj_tag(v_e_x3f_4071_) == 0)
{
v___y_4030_ = v_e_4013_;
goto v___jp_4029_;
}
else
{
lean_object* v_val_4072_; 
lean_dec_ref(v_e_4013_);
v_val_4072_ = lean_ctor_get(v_e_x3f_4071_, 0);
lean_inc(v_val_4072_);
lean_dec_ref(v_e_x3f_4071_);
v___y_4030_ = v_val_4072_;
goto v___jp_4029_;
}
}
}
v___jp_4029_:
{
switch(lean_obj_tag(v___y_4030_))
{
case 7:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___x_4031_, v___y_4030_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4032_;
}
case 6:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___x_4033_, v___y_4030_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4034_;
}
case 8:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___x_4035_, v___y_4030_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4036_;
}
case 5:
{
lean_object* v_dummy_4037_; lean_object* v_nargs_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_dummy_4037_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4038_ = l_Lean_Expr_getAppNumArgs(v___y_4030_);
lean_inc(v_nargs_4038_);
v___x_4039_ = lean_mk_array(v_nargs_4038_, v_dummy_4037_);
v___x_4040_ = lean_unsigned_to_nat(1u);
v___x_4041_ = lean_nat_sub(v_nargs_4038_, v___x_4040_);
lean_dec(v_nargs_4038_);
v___x_4042_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4017_, v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v___y_4030_, v___x_4039_, v___x_4041_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4042_;
}
case 10:
{
lean_object* v_data_4043_; lean_object* v_expr_4044_; lean_object* v___x_4045_; 
v_data_4043_ = lean_ctor_get(v___y_4030_, 0);
v_expr_4044_ = lean_ctor_get(v___y_4030_, 1);
lean_inc_ref(v_expr_4044_);
lean_inc_ref(v_post_4014_);
lean_inc_ref(v_pre_4012_);
v___x_4045_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v_expr_4044_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; size_t v___x_4047_; size_t v___x_4048_; uint8_t v___x_4049_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref(v___x_4045_);
v___x_4047_ = lean_ptr_addr(v_expr_4044_);
v___x_4048_ = lean_ptr_addr(v_a_4046_);
v___x_4049_ = lean_usize_dec_eq(v___x_4047_, v___x_4048_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
lean_inc(v_data_4043_);
lean_dec_ref(v___y_4030_);
v___x_4050_ = l_Lean_Expr_mdata___override(v_data_4043_, v_a_4046_);
v___x_4051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___x_4050_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4051_;
}
else
{
lean_object* v___x_4052_; 
lean_dec(v_a_4046_);
v___x_4052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___y_4030_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4052_;
}
}
else
{
lean_dec_ref(v___y_4030_);
lean_dec_ref(v_post_4014_);
lean_dec_ref(v_pre_4012_);
return v___x_4045_;
}
}
case 11:
{
lean_object* v_typeName_4053_; lean_object* v_idx_4054_; lean_object* v_struct_4055_; lean_object* v___x_4056_; 
v_typeName_4053_ = lean_ctor_get(v___y_4030_, 0);
v_idx_4054_ = lean_ctor_get(v___y_4030_, 1);
v_struct_4055_ = lean_ctor_get(v___y_4030_, 2);
lean_inc_ref(v_struct_4055_);
lean_inc_ref(v_post_4014_);
lean_inc_ref(v_pre_4012_);
v___x_4056_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v_struct_4055_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; size_t v___x_4058_; size_t v___x_4059_; uint8_t v___x_4060_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = lean_ptr_addr(v_struct_4055_);
v___x_4059_ = lean_ptr_addr(v_a_4057_);
v___x_4060_ = lean_usize_dec_eq(v___x_4058_, v___x_4059_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_inc(v_idx_4054_);
lean_inc(v_typeName_4053_);
lean_dec_ref(v___y_4030_);
v___x_4061_ = l_Lean_Expr_proj___override(v_typeName_4053_, v_idx_4054_, v_a_4057_);
v___x_4062_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___x_4061_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4062_;
}
else
{
lean_object* v___x_4063_; 
lean_dec(v_a_4057_);
v___x_4063_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___y_4030_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4063_;
}
}
else
{
lean_dec_ref(v___y_4030_);
lean_dec_ref(v_post_4014_);
lean_dec_ref(v_pre_4012_);
return v___x_4056_;
}
}
default: 
{
lean_object* v___x_4064_; 
v___x_4064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4012_, v_post_4014_, v_usedLetOnly_4015_, v_skipConstInApp_4016_, v_skipInstances_4017_, v___y_4030_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4064_;
}
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v_post_4014_);
lean_dec_ref(v_e_4013_);
lean_dec_ref(v_pre_4012_);
v_a_4074_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4024_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4024_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v_pre_4082_, lean_object* v_e_4083_, lean_object* v_post_4084_, lean_object* v_usedLetOnly_4085_, lean_object* v_skipConstInApp_4086_, lean_object* v_skipInstances_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
uint8_t v_usedLetOnly_boxed_4094_; uint8_t v_skipConstInApp_boxed_4095_; uint8_t v_skipInstances_boxed_4096_; lean_object* v_res_4097_; 
v_usedLetOnly_boxed_4094_ = lean_unbox(v_usedLetOnly_4085_);
v_skipConstInApp_boxed_4095_ = lean_unbox(v_skipConstInApp_4086_);
v_skipInstances_boxed_4096_ = lean_unbox(v_skipInstances_4087_);
v_res_4097_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v_pre_4082_, v_e_4083_, v_post_4084_, v_usedLetOnly_boxed_4094_, v_skipConstInApp_boxed_4095_, v_skipInstances_boxed_4096_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4098_, lean_object* v_post_4099_, uint8_t v_usedLetOnly_4100_, uint8_t v_skipConstInApp_4101_, uint8_t v_skipInstances_4102_, lean_object* v_e_4103_, lean_object* v_a_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_inc(v_a_4104_);
v___x_4110_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4110_, 0, lean_box(0));
lean_closure_set(v___x_4110_, 1, lean_box(0));
lean_closure_set(v___x_4110_, 2, v_a_4104_);
v___x_4111_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4110_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4145_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4145_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4111_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4145_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4112_, v_e_4103_);
lean_dec(v_a_4112_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___f_4120_; lean_object* v___x_4121_; 
lean_del_object(v___x_4114_);
v___x_4117_ = lean_box(v_usedLetOnly_4100_);
v___x_4118_ = lean_box(v_skipConstInApp_4101_);
v___x_4119_ = lean_box(v_skipInstances_4102_);
lean_inc_ref(v_e_4103_);
v___f_4120_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 12, 6);
lean_closure_set(v___f_4120_, 0, v_pre_4098_);
lean_closure_set(v___f_4120_, 1, v_e_4103_);
lean_closure_set(v___f_4120_, 2, v_post_4099_);
lean_closure_set(v___f_4120_, 3, v___x_4117_);
lean_closure_set(v___f_4120_, 4, v___x_4118_);
lean_closure_set(v___f_4120_, 5, v___x_4119_);
v___x_4121_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4120_, v_a_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc_n(v_a_4122_, 2);
lean_dec_ref(v___x_4121_);
lean_inc(v_a_4104_);
v___f_4123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4123_, 0, v_a_4104_);
lean_closure_set(v___f_4123_, 1, v_e_4103_);
lean_closure_set(v___f_4123_, 2, v_a_4122_);
v___x_4124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4123_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4131_ == 0)
{
lean_object* v_unused_4132_; 
v_unused_4132_ = lean_ctor_get(v___x_4124_, 0);
lean_dec(v_unused_4132_);
v___x_4126_ = v___x_4124_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_dec(v___x_4124_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v_a_4122_);
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4122_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec(v_a_4122_);
v_a_4133_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4124_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4124_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
else
{
lean_dec_ref(v_e_4103_);
return v___x_4121_;
}
}
else
{
lean_object* v_val_4141_; lean_object* v___x_4143_; 
lean_dec_ref(v_e_4103_);
lean_dec_ref(v_post_4099_);
lean_dec_ref(v_pre_4098_);
v_val_4141_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_val_4141_);
lean_dec_ref(v___x_4116_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v_val_4141_);
v___x_4143_ = v___x_4114_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_val_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v_e_4103_);
lean_dec_ref(v_post_4099_);
lean_dec_ref(v_pre_4098_);
v_a_4146_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4111_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4111_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4154_, lean_object* v_pre_4155_, lean_object* v_post_4156_, lean_object* v_usedLetOnly_4157_, lean_object* v_skipConstInApp_4158_, lean_object* v_skipInstances_4159_, lean_object* v_body_4160_, lean_object* v_x_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v_usedLetOnly_boxed_4168_; uint8_t v_skipConstInApp_boxed_4169_; uint8_t v_skipInstances_boxed_4170_; lean_object* v_res_4171_; 
v_usedLetOnly_boxed_4168_ = lean_unbox(v_usedLetOnly_4157_);
v_skipConstInApp_boxed_4169_ = lean_unbox(v_skipConstInApp_4158_);
v_skipInstances_boxed_4170_ = lean_unbox(v_skipInstances_4159_);
v_res_4171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4154_, v_pre_4155_, v_post_4156_, v_usedLetOnly_boxed_4168_, v_skipConstInApp_boxed_4169_, v_skipInstances_boxed_4170_, v_body_4160_, v_x_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4172_, lean_object* v_post_4173_, uint8_t v_usedLetOnly_4174_, uint8_t v_skipConstInApp_4175_, uint8_t v_skipInstances_4176_, lean_object* v_fvars_4177_, lean_object* v_e_4178_, lean_object* v_a_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
if (lean_obj_tag(v_e_4178_) == 7)
{
lean_object* v_binderName_4185_; lean_object* v_binderType_4186_; lean_object* v_body_4187_; uint8_t v_binderInfo_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_binderName_4185_ = lean_ctor_get(v_e_4178_, 0);
lean_inc(v_binderName_4185_);
v_binderType_4186_ = lean_ctor_get(v_e_4178_, 1);
lean_inc_ref(v_binderType_4186_);
v_body_4187_ = lean_ctor_get(v_e_4178_, 2);
lean_inc_ref(v_body_4187_);
v_binderInfo_4188_ = lean_ctor_get_uint8(v_e_4178_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4178_);
v___x_4189_ = lean_expr_instantiate_rev(v_binderType_4186_, v_fvars_4177_);
lean_dec_ref(v_binderType_4186_);
lean_inc_ref(v_post_4173_);
lean_inc_ref(v_pre_4172_);
v___x_4190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4172_, v_post_4173_, v_usedLetOnly_4174_, v_skipConstInApp_4175_, v_skipInstances_4176_, v___x_4189_, v_a_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___f_4195_; uint8_t v___x_4196_; lean_object* v___x_4197_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref(v___x_4190_);
v___x_4192_ = lean_box(v_usedLetOnly_4174_);
v___x_4193_ = lean_box(v_skipConstInApp_4175_);
v___x_4194_ = lean_box(v_skipInstances_4176_);
v___f_4195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4195_, 0, v_fvars_4177_);
lean_closure_set(v___f_4195_, 1, v_pre_4172_);
lean_closure_set(v___f_4195_, 2, v_post_4173_);
lean_closure_set(v___f_4195_, 3, v___x_4192_);
lean_closure_set(v___f_4195_, 4, v___x_4193_);
lean_closure_set(v___f_4195_, 5, v___x_4194_);
lean_closure_set(v___f_4195_, 6, v_body_4187_);
v___x_4196_ = 0;
v___x_4197_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4185_, v_binderInfo_4188_, v_a_4191_, v___f_4195_, v___x_4196_, v_a_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
return v___x_4197_;
}
else
{
lean_dec_ref(v_body_4187_);
lean_dec(v_binderName_4185_);
lean_dec_ref(v_fvars_4177_);
lean_dec_ref(v_post_4173_);
lean_dec_ref(v_pre_4172_);
return v___x_4190_;
}
}
else
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_expr_instantiate_rev(v_e_4178_, v_fvars_4177_);
lean_dec_ref(v_e_4178_);
lean_inc_ref(v_post_4173_);
lean_inc_ref(v_pre_4172_);
v___x_4199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4172_, v_post_4173_, v_usedLetOnly_4174_, v_skipConstInApp_4175_, v_skipInstances_4176_, v___x_4198_, v_a_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; uint8_t v___x_4201_; uint8_t v___x_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref(v___x_4199_);
v___x_4201_ = 0;
v___x_4202_ = 1;
v___x_4203_ = 1;
v___x_4204_ = l_Lean_Meta_mkForallFVars(v_fvars_4177_, v_a_4200_, v___x_4201_, v_usedLetOnly_4174_, v___x_4202_, v___x_4203_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec_ref(v_fvars_4177_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4204_);
v___x_4206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4172_, v_post_4173_, v_usedLetOnly_4174_, v_skipConstInApp_4175_, v_skipInstances_4176_, v_a_4205_, v_a_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
return v___x_4206_;
}
else
{
lean_dec_ref(v_post_4173_);
lean_dec_ref(v_pre_4172_);
return v___x_4204_;
}
}
else
{
lean_dec_ref(v_fvars_4177_);
lean_dec_ref(v_post_4173_);
lean_dec_ref(v_pre_4172_);
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4207_, lean_object* v_pre_4208_, lean_object* v_post_4209_, uint8_t v_usedLetOnly_4210_, uint8_t v_skipConstInApp_4211_, uint8_t v_skipInstances_4212_, lean_object* v_body_4213_, lean_object* v_x_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = lean_array_push(v_fvars_4207_, v_x_4214_);
v___x_4222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4208_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___x_4221_, v_body_4213_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4223_, lean_object* v_post_4224_, lean_object* v_usedLetOnly_4225_, lean_object* v_skipConstInApp_4226_, lean_object* v_skipInstances_4227_, lean_object* v_e_4228_, lean_object* v_a_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
uint8_t v_usedLetOnly_boxed_4235_; uint8_t v_skipConstInApp_boxed_4236_; uint8_t v_skipInstances_boxed_4237_; lean_object* v_res_4238_; 
v_usedLetOnly_boxed_4235_ = lean_unbox(v_usedLetOnly_4225_);
v_skipConstInApp_boxed_4236_ = lean_unbox(v_skipConstInApp_4226_);
v_skipInstances_boxed_4237_ = lean_unbox(v_skipInstances_4227_);
v_res_4238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4223_, v_post_4224_, v_usedLetOnly_boxed_4235_, v_skipConstInApp_boxed_4236_, v_skipInstances_boxed_4237_, v_e_4228_, v_a_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v_a_4229_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4239_, lean_object* v_post_4240_, lean_object* v_usedLetOnly_4241_, lean_object* v_skipConstInApp_4242_, lean_object* v_skipInstances_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_bs_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
uint8_t v_usedLetOnly_boxed_4253_; uint8_t v_skipConstInApp_boxed_4254_; uint8_t v_skipInstances_boxed_4255_; size_t v_sz_boxed_4256_; size_t v_i_boxed_4257_; lean_object* v_res_4258_; 
v_usedLetOnly_boxed_4253_ = lean_unbox(v_usedLetOnly_4241_);
v_skipConstInApp_boxed_4254_ = lean_unbox(v_skipConstInApp_4242_);
v_skipInstances_boxed_4255_ = lean_unbox(v_skipInstances_4243_);
v_sz_boxed_4256_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4257_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4239_, v_post_4240_, v_usedLetOnly_boxed_4253_, v_skipConstInApp_boxed_4254_, v_skipInstances_boxed_4255_, v_sz_boxed_4256_, v_i_boxed_4257_, v_bs_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4259_, lean_object* v_post_4260_, lean_object* v_usedLetOnly_4261_, lean_object* v_skipConstInApp_4262_, lean_object* v_skipInstances_4263_, lean_object* v_e_4264_, lean_object* v_a_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v_usedLetOnly_boxed_4271_; uint8_t v_skipConstInApp_boxed_4272_; uint8_t v_skipInstances_boxed_4273_; lean_object* v_res_4274_; 
v_usedLetOnly_boxed_4271_ = lean_unbox(v_usedLetOnly_4261_);
v_skipConstInApp_boxed_4272_ = lean_unbox(v_skipConstInApp_4262_);
v_skipInstances_boxed_4273_ = lean_unbox(v_skipInstances_4263_);
v_res_4274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4259_, v_post_4260_, v_usedLetOnly_boxed_4271_, v_skipConstInApp_boxed_4272_, v_skipInstances_boxed_4273_, v_e_4264_, v_a_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v_a_4265_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4275_, lean_object* v_post_4276_, lean_object* v_usedLetOnly_4277_, lean_object* v_skipConstInApp_4278_, lean_object* v_skipInstances_4279_, lean_object* v_fvars_4280_, lean_object* v_e_4281_, lean_object* v_a_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
uint8_t v_usedLetOnly_boxed_4288_; uint8_t v_skipConstInApp_boxed_4289_; uint8_t v_skipInstances_boxed_4290_; lean_object* v_res_4291_; 
v_usedLetOnly_boxed_4288_ = lean_unbox(v_usedLetOnly_4277_);
v_skipConstInApp_boxed_4289_ = lean_unbox(v_skipConstInApp_4278_);
v_skipInstances_boxed_4290_ = lean_unbox(v_skipInstances_4279_);
v_res_4291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4275_, v_post_4276_, v_usedLetOnly_boxed_4288_, v_skipConstInApp_boxed_4289_, v_skipInstances_boxed_4290_, v_fvars_4280_, v_e_4281_, v_a_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v_a_4282_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4292_, lean_object* v_post_4293_, lean_object* v_usedLetOnly_4294_, lean_object* v_skipConstInApp_4295_, lean_object* v_skipInstances_4296_, lean_object* v_fvars_4297_, lean_object* v_e_4298_, lean_object* v_a_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
uint8_t v_usedLetOnly_boxed_4305_; uint8_t v_skipConstInApp_boxed_4306_; uint8_t v_skipInstances_boxed_4307_; lean_object* v_res_4308_; 
v_usedLetOnly_boxed_4305_ = lean_unbox(v_usedLetOnly_4294_);
v_skipConstInApp_boxed_4306_ = lean_unbox(v_skipConstInApp_4295_);
v_skipInstances_boxed_4307_ = lean_unbox(v_skipInstances_4296_);
v_res_4308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4292_, v_post_4293_, v_usedLetOnly_boxed_4305_, v_skipConstInApp_boxed_4306_, v_skipInstances_boxed_4307_, v_fvars_4297_, v_e_4298_, v_a_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v_a_4299_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4309_, lean_object* v_post_4310_, lean_object* v_usedLetOnly_4311_, lean_object* v_skipConstInApp_4312_, lean_object* v_skipInstances_4313_, lean_object* v_fvars_4314_, lean_object* v_e_4315_, lean_object* v_a_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
uint8_t v_usedLetOnly_boxed_4322_; uint8_t v_skipConstInApp_boxed_4323_; uint8_t v_skipInstances_boxed_4324_; lean_object* v_res_4325_; 
v_usedLetOnly_boxed_4322_ = lean_unbox(v_usedLetOnly_4311_);
v_skipConstInApp_boxed_4323_ = lean_unbox(v_skipConstInApp_4312_);
v_skipInstances_boxed_4324_ = lean_unbox(v_skipInstances_4313_);
v_res_4325_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4309_, v_post_4310_, v_usedLetOnly_boxed_4322_, v_skipConstInApp_boxed_4323_, v_skipInstances_boxed_4324_, v_fvars_4314_, v_e_4315_, v_a_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v_a_4316_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4326_, lean_object* v___x_4327_, lean_object* v_pre_4328_, lean_object* v_post_4329_, lean_object* v_usedLetOnly_4330_, lean_object* v_skipConstInApp_4331_, lean_object* v_skipInstances_4332_, lean_object* v_a_4333_, lean_object* v_b_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
uint8_t v_usedLetOnly_boxed_4341_; uint8_t v_skipConstInApp_boxed_4342_; uint8_t v_skipInstances_boxed_4343_; lean_object* v_res_4344_; 
v_usedLetOnly_boxed_4341_ = lean_unbox(v_usedLetOnly_4330_);
v_skipConstInApp_boxed_4342_ = lean_unbox(v_skipConstInApp_4331_);
v_skipInstances_boxed_4343_ = lean_unbox(v_skipInstances_4332_);
v_res_4344_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4326_, v___x_4327_, v_pre_4328_, v_post_4329_, v_usedLetOnly_boxed_4341_, v_skipConstInApp_boxed_4342_, v_skipInstances_boxed_4343_, v_a_4333_, v_b_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___x_4327_);
lean_dec(v_upperBound_4326_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4345_, lean_object* v_pre_4346_, lean_object* v_post_4347_, lean_object* v_usedLetOnly_4348_, lean_object* v_skipConstInApp_4349_, lean_object* v_x_4350_, lean_object* v_x_4351_, lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
uint8_t v_skipInstances_boxed_4359_; uint8_t v_usedLetOnly_boxed_4360_; uint8_t v_skipConstInApp_boxed_4361_; lean_object* v_res_4362_; 
v_skipInstances_boxed_4359_ = lean_unbox(v_skipInstances_4345_);
v_usedLetOnly_boxed_4360_ = lean_unbox(v_usedLetOnly_4348_);
v_skipConstInApp_boxed_4361_ = lean_unbox(v_skipConstInApp_4349_);
v_res_4362_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4359_, v_pre_4346_, v_post_4347_, v_usedLetOnly_boxed_4360_, v_skipConstInApp_boxed_4361_, v_x_4350_, v_x_4351_, v_x_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4363_, lean_object* v_pre_4364_, lean_object* v_post_4365_, uint8_t v_usedLetOnly_4366_, uint8_t v_skipConstInApp_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v_a_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; 
v___x_4373_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4374_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4373_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref(v___x_4374_);
v___x_4376_ = 0;
v___x_4377_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4364_, v_post_4365_, v_usedLetOnly_4366_, v_skipConstInApp_4367_, v___x_4376_, v_input_4363_, v_a_4375_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4379_, 0, lean_box(0));
lean_closure_set(v___x_4379_, 1, lean_box(0));
lean_closure_set(v___x_4379_, 2, v_a_4375_);
v___x_4380_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4379_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4387_ == 0)
{
lean_object* v_unused_4388_; 
v_unused_4388_ = lean_ctor_get(v___x_4380_, 0);
lean_dec(v_unused_4388_);
v___x_4382_ = v___x_4380_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_dec(v___x_4380_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v_a_4378_);
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4378_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
else
{
lean_dec(v_a_4375_);
return v___x_4377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4389_, lean_object* v_pre_4390_, lean_object* v_post_4391_, lean_object* v_usedLetOnly_4392_, lean_object* v_skipConstInApp_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v_usedLetOnly_boxed_4399_; uint8_t v_skipConstInApp_boxed_4400_; lean_object* v_res_4401_; 
v_usedLetOnly_boxed_4399_ = lean_unbox(v_usedLetOnly_4392_);
v_skipConstInApp_boxed_4400_ = lean_unbox(v_skipConstInApp_4393_);
v_res_4401_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4389_, v_pre_4390_, v_post_4391_, v_usedLetOnly_boxed_4399_, v_skipConstInApp_boxed_4400_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4403_, uint8_t v_zetaDelta_4404_, uint8_t v_zetaHave_4405_, uint8_t v_beta_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v_lctx_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___f_4416_; uint8_t v___x_4417_; 
v_lctx_4412_ = lean_ctor_get(v_a_4407_, 2);
lean_inc_ref(v_lctx_4412_);
v___x_4413_ = lean_local_ctx_num_indices(v_lctx_4412_);
v___x_4414_ = lean_box(v_zetaHave_4405_);
v___x_4415_ = lean_box(v_zetaDelta_4404_);
v___f_4416_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4416_, 0, v___x_4414_);
lean_closure_set(v___f_4416_, 1, v___x_4413_);
lean_closure_set(v___f_4416_, 2, v___x_4415_);
v___x_4417_ = 1;
if (v_beta_4406_ == 0)
{
lean_object* v___f_4418_; lean_object* v___f_4419_; lean_object* v___x_4420_; 
v___f_4418_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4419_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4419_, 0, v___f_4416_);
v___x_4420_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4403_, v___f_4419_, v___f_4418_, v___x_4417_, v_beta_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
return v___x_4420_;
}
else
{
lean_object* v___f_4421_; lean_object* v___f_4422_; uint8_t v___x_4423_; lean_object* v___x_4424_; 
v___f_4421_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4422_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4422_, 0, v___f_4416_);
v___x_4423_ = 0;
v___x_4424_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4403_, v___f_4422_, v___f_4421_, v___x_4417_, v___x_4423_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
return v___x_4424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4425_, lean_object* v_zetaDelta_4426_, lean_object* v_zetaHave_4427_, lean_object* v_beta_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
uint8_t v_zetaDelta_boxed_4434_; uint8_t v_zetaHave_boxed_4435_; uint8_t v_beta_boxed_4436_; lean_object* v_res_4437_; 
v_zetaDelta_boxed_4434_ = lean_unbox(v_zetaDelta_4426_);
v_zetaHave_boxed_4435_ = lean_unbox(v_zetaHave_4427_);
v_beta_boxed_4436_ = lean_unbox(v_beta_4428_);
v_res_4437_ = l_Lean_Meta_zetaReduce(v_e_4425_, v_zetaDelta_boxed_4434_, v_zetaHave_boxed_4435_, v_beta_boxed_4436_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4438_, lean_object* v___x_4439_, lean_object* v_pre_4440_, lean_object* v_post_4441_, uint8_t v_usedLetOnly_4442_, uint8_t v_skipConstInApp_4443_, uint8_t v_skipInstances_4444_, lean_object* v___x_4445_, lean_object* v_inst_4446_, lean_object* v_R_4447_, lean_object* v_a_4448_, lean_object* v_b_4449_, lean_object* v_c_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4438_, v___x_4439_, v_pre_4440_, v_post_4441_, v_usedLetOnly_4442_, v_skipConstInApp_4443_, v_skipInstances_4444_, v_a_4448_, v_b_4449_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4458_ = _args[0];
lean_object* v___x_4459_ = _args[1];
lean_object* v_pre_4460_ = _args[2];
lean_object* v_post_4461_ = _args[3];
lean_object* v_usedLetOnly_4462_ = _args[4];
lean_object* v_skipConstInApp_4463_ = _args[5];
lean_object* v_skipInstances_4464_ = _args[6];
lean_object* v___x_4465_ = _args[7];
lean_object* v_inst_4466_ = _args[8];
lean_object* v_R_4467_ = _args[9];
lean_object* v_a_4468_ = _args[10];
lean_object* v_b_4469_ = _args[11];
lean_object* v_c_4470_ = _args[12];
lean_object* v___y_4471_ = _args[13];
lean_object* v___y_4472_ = _args[14];
lean_object* v___y_4473_ = _args[15];
lean_object* v___y_4474_ = _args[16];
lean_object* v___y_4475_ = _args[17];
lean_object* v___y_4476_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4477_; uint8_t v_skipConstInApp_boxed_4478_; uint8_t v_skipInstances_boxed_4479_; lean_object* v_res_4480_; 
v_usedLetOnly_boxed_4477_ = lean_unbox(v_usedLetOnly_4462_);
v_skipConstInApp_boxed_4478_ = lean_unbox(v_skipConstInApp_4463_);
v_skipInstances_boxed_4479_ = lean_unbox(v_skipInstances_4464_);
v_res_4480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4458_, v___x_4459_, v_pre_4460_, v_post_4461_, v_usedLetOnly_boxed_4477_, v_skipConstInApp_boxed_4478_, v_skipInstances_boxed_4479_, v___x_4465_, v_inst_4466_, v_R_4467_, v_a_4468_, v_b_4469_, v_c_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec(v___x_4465_);
lean_dec_ref(v___x_4459_);
lean_dec(v_upperBound_4458_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4481_, lean_object* v_name_4482_, uint8_t v_bi_4483_, lean_object* v_type_4484_, lean_object* v_k_4485_, uint8_t v_kind_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4482_, v_bi_4483_, v_type_4484_, v_k_4485_, v_kind_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4494_, lean_object* v_name_4495_, lean_object* v_bi_4496_, lean_object* v_type_4497_, lean_object* v_k_4498_, lean_object* v_kind_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v_bi_boxed_4506_; uint8_t v_kind_boxed_4507_; lean_object* v_res_4508_; 
v_bi_boxed_4506_ = lean_unbox(v_bi_4496_);
v_kind_boxed_4507_ = lean_unbox(v_kind_4499_);
v_res_4508_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4494_, v_name_4495_, v_bi_boxed_4506_, v_type_4497_, v_k_4498_, v_kind_boxed_4507_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4509_, lean_object* v_name_4510_, lean_object* v_type_4511_, lean_object* v_val_4512_, lean_object* v_k_4513_, uint8_t v_nondep_4514_, uint8_t v_kind_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4510_, v_type_4511_, v_val_4512_, v_k_4513_, v_nondep_4514_, v_kind_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4523_, lean_object* v_name_4524_, lean_object* v_type_4525_, lean_object* v_val_4526_, lean_object* v_k_4527_, lean_object* v_nondep_4528_, lean_object* v_kind_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v_nondep_boxed_4536_; uint8_t v_kind_boxed_4537_; lean_object* v_res_4538_; 
v_nondep_boxed_4536_ = lean_unbox(v_nondep_4528_);
v_kind_boxed_4537_ = lean_unbox(v_kind_4529_);
v_res_4538_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4523_, v_name_4524_, v_type_4525_, v_val_4526_, v_k_4527_, v_nondep_boxed_4536_, v_kind_boxed_4537_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4539_, lean_object* v_ref_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4540_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4547_, lean_object* v_ref_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4547_, v_ref_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4555_, lean_object* v_x_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4564_, lean_object* v_x_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4564_, v_x_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
return v_res_4572_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4573_, lean_object* v_as_4574_, size_t v_i_4575_, size_t v_stop_4576_){
_start:
{
uint8_t v___x_4577_; 
v___x_4577_ = lean_usize_dec_eq(v_i_4575_, v_stop_4576_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = lean_array_uget_borrowed(v_as_4574_, v_i_4575_);
v___x_4579_ = l_Lean_instBEqFVarId_beq(v_a_4573_, v___x_4578_);
if (v___x_4579_ == 0)
{
size_t v___x_4580_; size_t v___x_4581_; 
v___x_4580_ = ((size_t)1ULL);
v___x_4581_ = lean_usize_add(v_i_4575_, v___x_4580_);
v_i_4575_ = v___x_4581_;
goto _start;
}
else
{
return v___x_4579_;
}
}
else
{
uint8_t v___x_4583_; 
v___x_4583_ = 0;
return v___x_4583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4584_, lean_object* v_as_4585_, lean_object* v_i_4586_, lean_object* v_stop_4587_){
_start:
{
size_t v_i_boxed_4588_; size_t v_stop_boxed_4589_; uint8_t v_res_4590_; lean_object* v_r_4591_; 
v_i_boxed_4588_ = lean_unbox_usize(v_i_4586_);
lean_dec(v_i_4586_);
v_stop_boxed_4589_ = lean_unbox_usize(v_stop_4587_);
lean_dec(v_stop_4587_);
v_res_4590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4584_, v_as_4585_, v_i_boxed_4588_, v_stop_boxed_4589_);
lean_dec_ref(v_as_4585_);
lean_dec(v_a_4584_);
v_r_4591_ = lean_box(v_res_4590_);
return v_r_4591_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v___x_4594_ = lean_unsigned_to_nat(0u);
v___x_4595_ = lean_array_get_size(v_as_4592_);
v___x_4596_ = lean_nat_dec_lt(v___x_4594_, v___x_4595_);
if (v___x_4596_ == 0)
{
return v___x_4596_;
}
else
{
if (v___x_4596_ == 0)
{
return v___x_4596_;
}
else
{
size_t v___x_4597_; size_t v___x_4598_; uint8_t v___x_4599_; 
v___x_4597_ = ((size_t)0ULL);
v___x_4598_ = lean_usize_of_nat(v___x_4595_);
v___x_4599_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4593_, v_as_4592_, v___x_4597_, v___x_4598_);
return v___x_4599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4600_, lean_object* v_a_4601_){
_start:
{
uint8_t v_res_4602_; lean_object* v_r_4603_; 
v_res_4602_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4600_, v_a_4601_);
lean_dec(v_a_4601_);
lean_dec_ref(v_as_4600_);
v_r_4603_ = lean_box(v_res_4602_);
return v_r_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4604_, lean_object* v_e_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l_Lean_Expr_getAppFn(v_e_4605_);
if (lean_obj_tag(v___x_4614_) == 1)
{
lean_object* v_fvarId_4615_; uint8_t v___x_4616_; 
v_fvarId_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_fvarId_4615_);
lean_dec_ref(v___x_4614_);
v___x_4616_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4604_, v_fvarId_4615_);
if (v___x_4616_ == 0)
{
lean_dec(v_fvarId_4615_);
lean_dec_ref(v_e_4605_);
goto v___jp_4611_;
}
else
{
uint8_t v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = 0;
v___x_4618_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4615_, v___x_4617_, v___y_4606_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc(v_a_4619_);
lean_dec_ref(v___x_4618_);
if (lean_obj_tag(v_a_4619_) == 1)
{
lean_object* v_val_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4643_; 
v_val_4620_ = lean_ctor_get(v_a_4619_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_a_4619_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4622_ = v_a_4619_;
v_isShared_4623_ = v_isSharedCheck_4643_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_val_4620_);
lean_dec(v_a_4619_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4643_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4624_; lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4642_; 
v___x_4624_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4620_, v___y_4607_);
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4642_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4642_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v_dummy_4629_; lean_object* v_nargs_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
v_dummy_4629_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4630_ = l_Lean_Expr_getAppNumArgs(v_e_4605_);
lean_inc(v_nargs_4630_);
v___x_4631_ = lean_mk_array(v_nargs_4630_, v_dummy_4629_);
v___x_4632_ = lean_unsigned_to_nat(1u);
v___x_4633_ = lean_nat_sub(v_nargs_4630_, v___x_4632_);
lean_dec(v_nargs_4630_);
v___x_4634_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4605_, v___x_4631_, v___x_4633_);
v___x_4635_ = l_Lean_Expr_beta(v_a_4625_, v___x_4634_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 0, v___x_4635_);
v___x_4637_ = v___x_4622_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4639_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v___x_4637_);
v___x_4639_ = v___x_4627_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4637_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
}
else
{
lean_dec(v_a_4619_);
lean_dec_ref(v_e_4605_);
goto v___jp_4611_;
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec_ref(v_e_4605_);
v_a_4644_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4618_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4618_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
}
else
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
lean_dec_ref(v___x_4614_);
lean_dec_ref(v_e_4605_);
v___x_4652_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
v___jp_4611_:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4612_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4612_);
return v___x_4613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4654_, lean_object* v_e_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4654_, v_e_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec_ref(v_fvars_4654_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4662_, lean_object* v_fvars_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v___f_4669_; lean_object* v_pre_4670_; uint8_t v___x_4671_; lean_object* v___x_4672_; 
v___f_4669_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4670_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4670_, 0, v_fvars_4663_);
v___x_4671_ = 0;
v___x_4672_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4662_, v_pre_4670_, v___f_4669_, v___x_4671_, v___x_4671_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4673_, lean_object* v_fvars_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_Lean_Meta_zetaDeltaFVars(v_e_4673_, v_fvars_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
return v_res_4680_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4681_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
return v___x_4683_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v___x_4689_; lean_object* v_nextMacroScope_4690_; lean_object* v_ngen_4691_; lean_object* v_auxDeclNGen_4692_; lean_object* v_traceState_4693_; lean_object* v_messages_4694_; lean_object* v_infoState_4695_; lean_object* v_snapshotTasks_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4707_; 
v___x_4689_ = lean_st_ref_take(v___y_4687_);
v_nextMacroScope_4690_ = lean_ctor_get(v___x_4689_, 1);
v_ngen_4691_ = lean_ctor_get(v___x_4689_, 2);
v_auxDeclNGen_4692_ = lean_ctor_get(v___x_4689_, 3);
v_traceState_4693_ = lean_ctor_get(v___x_4689_, 4);
v_messages_4694_ = lean_ctor_get(v___x_4689_, 6);
v_infoState_4695_ = lean_ctor_get(v___x_4689_, 7);
v_snapshotTasks_4696_ = lean_ctor_get(v___x_4689_, 8);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; lean_object* v_unused_4709_; 
v_unused_4708_ = lean_ctor_get(v___x_4689_, 5);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v___x_4689_, 0);
lean_dec(v_unused_4709_);
v___x_4698_ = v___x_4689_;
v_isShared_4699_ = v_isSharedCheck_4707_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_snapshotTasks_4696_);
lean_inc(v_infoState_4695_);
lean_inc(v_messages_4694_);
lean_inc(v_traceState_4693_);
lean_inc(v_auxDeclNGen_4692_);
lean_inc(v_ngen_4691_);
lean_inc(v_nextMacroScope_4690_);
lean_dec(v___x_4689_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4707_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4700_; lean_object* v___x_4702_; 
v___x_4700_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 5, v___x_4700_);
lean_ctor_set(v___x_4698_, 0, v_env_4686_);
v___x_4702_ = v___x_4698_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_env_4686_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_nextMacroScope_4690_);
lean_ctor_set(v_reuseFailAlloc_4706_, 2, v_ngen_4691_);
lean_ctor_set(v_reuseFailAlloc_4706_, 3, v_auxDeclNGen_4692_);
lean_ctor_set(v_reuseFailAlloc_4706_, 4, v_traceState_4693_);
lean_ctor_set(v_reuseFailAlloc_4706_, 5, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4706_, 6, v_messages_4694_);
lean_ctor_set(v_reuseFailAlloc_4706_, 7, v_infoState_4695_);
lean_ctor_set(v_reuseFailAlloc_4706_, 8, v_snapshotTasks_4696_);
v___x_4702_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4703_ = lean_st_ref_set(v___y_4687_, v___x_4702_);
v___x_4704_ = lean_box(0);
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4704_);
return v___x_4705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4710_, v___y_4711_);
lean_dec(v___y_4711_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4714_, v___y_4716_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4719_, v___y_4720_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4724_, lean_object* v___x_4725_, uint8_t v___x_4726_, lean_object* v_e_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
if (lean_obj_tag(v_e_4727_) == 4)
{
lean_object* v_declName_4731_; lean_object* v_us_4732_; uint8_t v___x_4733_; uint8_t v___x_4734_; 
v_declName_4731_ = lean_ctor_get(v_e_4727_, 0);
v_us_4732_ = lean_ctor_get(v_e_4727_, 1);
v___x_4733_ = 1;
lean_inc(v_declName_4731_);
v___x_4734_ = l_Lean_Environment_contains(v_env_4724_, v_declName_4731_, v___x_4733_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; 
lean_inc(v_declName_4731_);
v___x_4735_ = l_Lean_Environment_find_x3f(v___x_4725_, v_declName_4731_, v___x_4726_);
if (lean_obj_tag(v___x_4735_) == 1)
{
lean_object* v_val_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4765_; 
v_val_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4765_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_val_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4765_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
uint8_t v___x_4740_; 
v___x_4740_ = l_Lean_ConstantInfo_hasValue(v_val_4736_, v___x_4733_);
if (v___x_4740_ == 0)
{
lean_object* v___x_4742_; 
lean_dec(v_val_4736_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set_tag(v___x_4738_, 0);
lean_ctor_set(v___x_4738_, 0, v_e_4727_);
v___x_4742_ = v___x_4738_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_e_4727_);
v___x_4742_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
return v___x_4743_;
}
}
else
{
lean_object* v___x_4745_; 
lean_inc(v_us_4732_);
lean_dec_ref(v_e_4727_);
v___x_4745_ = l_Lean_Core_instantiateValueLevelParams(v_val_4736_, v_us_4732_, v___x_4733_, v___y_4728_, v___y_4729_);
lean_dec(v_val_4736_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4756_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4756_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4756_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v_a_4746_);
v___x_4751_ = v___x_4738_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4753_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4751_);
v___x_4753_ = v___x_4748_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_del_object(v___x_4738_);
v_a_4757_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4745_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4745_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
}
}
else
{
lean_object* v___x_4766_; lean_object* v___x_4767_; 
lean_dec(v___x_4735_);
v___x_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4766_, 0, v_e_4727_);
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
return v___x_4767_;
}
}
else
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
lean_dec_ref(v___x_4725_);
v___x_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4768_, 0, v_e_4727_);
v___x_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
return v___x_4769_;
}
}
else
{
lean_object* v___x_4770_; lean_object* v___x_4771_; 
lean_dec_ref(v_e_4727_);
lean_dec_ref(v___x_4725_);
lean_dec_ref(v_env_4724_);
v___x_4770_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
return v___x_4771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4772_, lean_object* v___x_4773_, lean_object* v___x_4774_, lean_object* v_e_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
uint8_t v___x_2152__boxed_4779_; lean_object* v_res_4780_; 
v___x_2152__boxed_4779_ = lean_unbox(v___x_4774_);
v_res_4780_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4772_, v___x_4773_, v___x_2152__boxed_4779_, v_e_4775_, v___y_4776_, v___y_4777_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4781_, lean_object* v_e_4782_, lean_object* v___f_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v___x_4787_; uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v_env_4791_; lean_object* v___x_4792_; lean_object* v___f_4793_; lean_object* v___x_4794_; 
v___x_4787_ = lean_st_ref_get(v___y_4785_);
v___x_4788_ = 0;
v___x_4789_ = l_Lean_Environment_setExporting(v_biggerEnv_4781_, v___x_4788_);
lean_inc_ref(v___x_4789_);
v___x_4790_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4789_, v___y_4785_);
lean_dec_ref(v___x_4790_);
v_env_4791_ = lean_ctor_get(v___x_4787_, 0);
lean_inc_ref(v_env_4791_);
lean_dec(v___x_4787_);
v___x_4792_ = lean_box(v___x_4788_);
v___f_4793_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4793_, 0, v_env_4791_);
lean_closure_set(v___f_4793_, 1, v___x_4789_);
lean_closure_set(v___f_4793_, 2, v___x_4792_);
v___x_4794_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4782_, v___f_4793_, v___f_4783_, v___y_4784_, v___y_4785_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4795_, lean_object* v_e_4796_, lean_object* v___f_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4795_, v_e_4796_, v___f_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4802_, lean_object* v_x_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v___x_4807_; lean_object* v_env_4808_; lean_object* v_a_4810_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4807_ = lean_st_ref_get(v___y_4805_);
v_env_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc_ref(v_env_4808_);
lean_dec(v___x_4807_);
v___x_4820_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4802_, v___y_4805_);
lean_dec_ref(v___x_4820_);
lean_inc(v___y_4805_);
lean_inc_ref(v___y_4804_);
v___x_4821_ = lean_apply_3(v_x_4803_, v___y_4804_, v___y_4805_, lean_box(0));
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref(v___x_4821_);
v___x_4823_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4808_, v___y_4805_);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4830_ == 0)
{
lean_object* v_unused_4831_; 
v_unused_4831_ = lean_ctor_get(v___x_4823_, 0);
lean_dec(v_unused_4831_);
v___x_4825_ = v___x_4823_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_dec(v___x_4823_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v_a_4822_);
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4822_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
else
{
lean_object* v_a_4832_; 
v_a_4832_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4832_);
lean_dec_ref(v___x_4821_);
v_a_4810_ = v_a_4832_;
goto v___jp_4809_;
}
v___jp_4809_:
{
lean_object* v___x_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
v___x_4811_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4808_, v___y_4805_);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; 
v_unused_4819_ = lean_ctor_get(v___x_4811_, 0);
lean_dec(v_unused_4819_);
v___x_4813_ = v___x_4811_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_dec(v___x_4811_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
lean_ctor_set_tag(v___x_4813_, 1);
lean_ctor_set(v___x_4813_, 0, v_a_4810_);
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4810_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4833_, lean_object* v_x_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4833_, v_x_4834_, v___y_4835_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_4839_, lean_object* v_e_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4844_; lean_object* v_env_4845_; lean_object* v___f_4846_; lean_object* v___f_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4844_ = lean_st_ref_get(v_a_4842_);
v_env_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc_ref(v_env_4845_);
lean_dec(v___x_4844_);
v___f_4846_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_4847_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_4847_, 0, v_biggerEnv_4839_);
lean_closure_set(v___f_4847_, 1, v_e_4840_);
lean_closure_set(v___f_4847_, 2, v___f_4846_);
v___x_4848_ = l_Lean_Environment_unlockAsync(v_env_4845_);
v___x_4849_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_4848_, v___f_4847_, v_a_4841_, v_a_4842_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_4850_, lean_object* v_e_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_4850_, v_e_4851_, v_a_4852_, v_a_4853_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_4856_, lean_object* v_env_4857_, lean_object* v_x_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4857_, v_x_4858_, v___y_4859_, v___y_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_4863_, lean_object* v_env_4864_, lean_object* v_x_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_4863_, v_env_4864_, v_x_4865_, v___y_4866_, v___y_4867_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
return v_res_4869_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_4870_, lean_object* v_axs_4871_, lean_object* v_numSectionVars_4872_, lean_object* v_as_4873_, size_t v_i_4874_, size_t v_stop_4875_){
_start:
{
uint8_t v___x_4876_; 
v___x_4876_ = lean_usize_dec_eq(v_i_4874_, v_stop_4875_);
if (v___x_4876_ == 0)
{
uint8_t v___x_4877_; uint8_t v___y_4879_; lean_object* v___x_4883_; lean_object* v___x_4884_; uint8_t v___x_4885_; 
v___x_4877_ = 1;
v___x_4883_ = lean_array_uget_borrowed(v_as_4873_, v_i_4874_);
v___x_4884_ = l_Lean_Expr_constName_x21(v_af_4870_);
v___x_4885_ = lean_name_eq(v___x_4884_, v___x_4883_);
lean_dec(v___x_4884_);
if (v___x_4885_ == 0)
{
v___y_4879_ = v___x_4885_;
goto v___jp_4878_;
}
else
{
lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4886_ = lean_array_get_size(v_axs_4871_);
v___x_4887_ = lean_nat_dec_le(v___x_4886_, v_numSectionVars_4872_);
v___y_4879_ = v___x_4887_;
goto v___jp_4878_;
}
v___jp_4878_:
{
if (v___y_4879_ == 0)
{
size_t v___x_4880_; size_t v___x_4881_; 
v___x_4880_ = ((size_t)1ULL);
v___x_4881_ = lean_usize_add(v_i_4874_, v___x_4880_);
v_i_4874_ = v___x_4881_;
goto _start;
}
else
{
return v___x_4877_;
}
}
}
else
{
uint8_t v___x_4888_; 
v___x_4888_ = 0;
return v___x_4888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_4889_, lean_object* v_axs_4890_, lean_object* v_numSectionVars_4891_, lean_object* v_as_4892_, lean_object* v_i_4893_, lean_object* v_stop_4894_){
_start:
{
size_t v_i_boxed_4895_; size_t v_stop_boxed_4896_; uint8_t v_res_4897_; lean_object* v_r_4898_; 
v_i_boxed_4895_ = lean_unbox_usize(v_i_4893_);
lean_dec(v_i_4893_);
v_stop_boxed_4896_ = lean_unbox_usize(v_stop_4894_);
lean_dec(v_stop_4894_);
v_res_4897_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_4889_, v_axs_4890_, v_numSectionVars_4891_, v_as_4892_, v_i_boxed_4895_, v_stop_boxed_4896_);
lean_dec_ref(v_as_4892_);
lean_dec(v_numSectionVars_4891_);
lean_dec_ref(v_axs_4890_);
lean_dec_ref(v_af_4889_);
v_r_4898_ = lean_box(v_res_4897_);
return v_r_4898_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_4899_, lean_object* v_numSectionVars_4900_, lean_object* v_x_4901_, lean_object* v_x_4902_, lean_object* v_x_4903_){
_start:
{
if (lean_obj_tag(v_x_4901_) == 5)
{
lean_object* v_fn_4904_; lean_object* v_arg_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v_fn_4904_ = lean_ctor_get(v_x_4901_, 0);
lean_inc_ref(v_fn_4904_);
v_arg_4905_ = lean_ctor_get(v_x_4901_, 1);
lean_inc_ref(v_arg_4905_);
lean_dec_ref(v_x_4901_);
v___x_4906_ = lean_array_set(v_x_4902_, v_x_4903_, v_arg_4905_);
v___x_4907_ = lean_unsigned_to_nat(1u);
v___x_4908_ = lean_nat_sub(v_x_4903_, v___x_4907_);
lean_dec(v_x_4903_);
v_x_4901_ = v_fn_4904_;
v_x_4902_ = v___x_4906_;
v_x_4903_ = v___x_4908_;
goto _start;
}
else
{
uint8_t v___x_4910_; 
lean_dec(v_x_4903_);
v___x_4910_ = l_Lean_Expr_isConst(v_x_4901_);
if (v___x_4910_ == 0)
{
lean_dec_ref(v_x_4902_);
lean_dec_ref(v_x_4901_);
return v___x_4910_;
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4911_ = lean_unsigned_to_nat(0u);
v___x_4912_ = lean_array_get_size(v_fnNames_4899_);
v___x_4913_ = lean_nat_dec_lt(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_dec_ref(v_x_4902_);
lean_dec_ref(v_x_4901_);
return v___x_4913_;
}
else
{
if (v___x_4913_ == 0)
{
lean_dec_ref(v_x_4902_);
lean_dec_ref(v_x_4901_);
return v___x_4913_;
}
else
{
size_t v___x_4914_; size_t v___x_4915_; uint8_t v___x_4916_; 
v___x_4914_ = ((size_t)0ULL);
v___x_4915_ = lean_usize_of_nat(v___x_4912_);
v___x_4916_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_4901_, v_x_4902_, v_numSectionVars_4900_, v_fnNames_4899_, v___x_4914_, v___x_4915_);
lean_dec_ref(v_x_4902_);
lean_dec_ref(v_x_4901_);
return v___x_4916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_4917_, lean_object* v_numSectionVars_4918_, lean_object* v_x_4919_, lean_object* v_x_4920_, lean_object* v_x_4921_){
_start:
{
uint8_t v_res_4922_; lean_object* v_r_4923_; 
v_res_4922_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_4917_, v_numSectionVars_4918_, v_x_4919_, v_x_4920_, v_x_4921_);
lean_dec(v_numSectionVars_4918_);
lean_dec_ref(v_fnNames_4917_);
v_r_4923_ = lean_box(v_res_4922_);
return v_r_4923_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_4924_, lean_object* v_fnNames_4925_, lean_object* v_x_4926_, lean_object* v_x_4927_, lean_object* v_x_4928_){
_start:
{
if (lean_obj_tag(v_x_4926_) == 5)
{
lean_object* v_fn_4929_; lean_object* v_arg_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; 
v_fn_4929_ = lean_ctor_get(v_x_4926_, 0);
lean_inc_ref(v_fn_4929_);
v_arg_4930_ = lean_ctor_get(v_x_4926_, 1);
lean_inc_ref(v_arg_4930_);
lean_dec_ref(v_x_4926_);
v___x_4931_ = lean_array_set(v_x_4927_, v_x_4928_, v_arg_4930_);
v___x_4932_ = lean_unsigned_to_nat(1u);
v___x_4933_ = lean_nat_sub(v_x_4928_, v___x_4932_);
v___x_4934_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_4925_, v_numSectionVars_4924_, v_fn_4929_, v___x_4931_, v___x_4933_);
return v___x_4934_;
}
else
{
uint8_t v___x_4935_; 
v___x_4935_ = l_Lean_Expr_isConst(v_x_4926_);
if (v___x_4935_ == 0)
{
lean_dec_ref(v_x_4927_);
lean_dec_ref(v_x_4926_);
return v___x_4935_;
}
else
{
lean_object* v___x_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4936_ = lean_unsigned_to_nat(0u);
v___x_4937_ = lean_array_get_size(v_fnNames_4925_);
v___x_4938_ = lean_nat_dec_lt(v___x_4936_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_dec_ref(v_x_4927_);
lean_dec_ref(v_x_4926_);
return v___x_4938_;
}
else
{
if (v___x_4938_ == 0)
{
lean_dec_ref(v_x_4927_);
lean_dec_ref(v_x_4926_);
return v___x_4938_;
}
else
{
size_t v___x_4939_; size_t v___x_4940_; uint8_t v___x_4941_; 
v___x_4939_ = ((size_t)0ULL);
v___x_4940_ = lean_usize_of_nat(v___x_4937_);
v___x_4941_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_4926_, v_x_4927_, v_numSectionVars_4924_, v_fnNames_4925_, v___x_4939_, v___x_4940_);
lean_dec_ref(v_x_4927_);
lean_dec_ref(v_x_4926_);
return v___x_4941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_4942_, lean_object* v_fnNames_4943_, lean_object* v_x_4944_, lean_object* v_x_4945_, lean_object* v_x_4946_){
_start:
{
uint8_t v_res_4947_; lean_object* v_r_4948_; 
v_res_4947_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_4942_, v_fnNames_4943_, v_x_4944_, v_x_4945_, v_x_4946_);
lean_dec(v_x_4946_);
lean_dec_ref(v_fnNames_4943_);
lean_dec(v_numSectionVars_4942_);
v_r_4948_ = lean_box(v_res_4947_);
return v_r_4948_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_4949_, lean_object* v_numSectionVars_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v_dummy_4952_; lean_object* v_nargs_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; uint8_t v___x_4957_; 
v_dummy_4952_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4953_ = l_Lean_Expr_getAppNumArgs(v_a_4951_);
lean_inc(v_nargs_4953_);
v___x_4954_ = lean_mk_array(v_nargs_4953_, v_dummy_4952_);
v___x_4955_ = lean_unsigned_to_nat(1u);
v___x_4956_ = lean_nat_sub(v_nargs_4953_, v___x_4955_);
lean_dec(v_nargs_4953_);
v___x_4957_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_4950_, v_fnNames_4949_, v_a_4951_, v___x_4954_, v___x_4956_);
lean_dec(v___x_4956_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_4958_, lean_object* v_numSectionVars_4959_, lean_object* v_a_4960_){
_start:
{
uint8_t v_res_4961_; lean_object* v_r_4962_; 
v_res_4961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_4958_, v_numSectionVars_4959_, v_a_4960_);
lean_dec(v_numSectionVars_4959_);
lean_dec_ref(v_fnNames_4958_);
v_r_4962_ = lean_box(v_res_4961_);
return v_r_4962_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_4963_, lean_object* v_numSectionVars_4964_, lean_object* v_as_4965_, size_t v_i_4966_, size_t v_stop_4967_){
_start:
{
uint8_t v___x_4968_; 
v___x_4968_ = lean_usize_dec_eq(v_i_4966_, v_stop_4967_);
if (v___x_4968_ == 0)
{
lean_object* v___x_4969_; uint8_t v___x_4970_; 
v___x_4969_ = lean_array_uget_borrowed(v_as_4965_, v_i_4966_);
lean_inc(v___x_4969_);
v___x_4970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_4963_, v_numSectionVars_4964_, v___x_4969_);
if (v___x_4970_ == 0)
{
size_t v___x_4971_; size_t v___x_4972_; 
v___x_4971_ = ((size_t)1ULL);
v___x_4972_ = lean_usize_add(v_i_4966_, v___x_4971_);
v_i_4966_ = v___x_4972_;
goto _start;
}
else
{
return v___x_4970_;
}
}
else
{
uint8_t v___x_4974_; 
v___x_4974_ = 0;
return v___x_4974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_4975_, lean_object* v_numSectionVars_4976_, lean_object* v_as_4977_, lean_object* v_i_4978_, lean_object* v_stop_4979_){
_start:
{
size_t v_i_boxed_4980_; size_t v_stop_boxed_4981_; uint8_t v_res_4982_; lean_object* v_r_4983_; 
v_i_boxed_4980_ = lean_unbox_usize(v_i_4978_);
lean_dec(v_i_4978_);
v_stop_boxed_4981_ = lean_unbox_usize(v_stop_4979_);
lean_dec(v_stop_4979_);
v_res_4982_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_4975_, v_numSectionVars_4976_, v_as_4977_, v_i_boxed_4980_, v_stop_boxed_4981_);
lean_dec_ref(v_as_4977_);
lean_dec(v_numSectionVars_4976_);
lean_dec_ref(v_fnNames_4975_);
v_r_4983_ = lean_box(v_res_4982_);
return v_r_4983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_4984_, lean_object* v_numSectionVars_4985_, lean_object* v___x_4986_, lean_object* v_x_4987_, lean_object* v_x_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
if (lean_obj_tag(v_x_4987_) == 5)
{
lean_object* v_fn_4995_; lean_object* v_arg_4996_; lean_object* v___x_4997_; 
v_fn_4995_ = lean_ctor_get(v_x_4987_, 0);
lean_inc_ref(v_fn_4995_);
v_arg_4996_ = lean_ctor_get(v_x_4987_, 1);
lean_inc_ref(v_arg_4996_);
lean_dec_ref(v_x_4987_);
v___x_4997_ = lean_array_push(v_x_4988_, v_arg_4996_);
v_x_4987_ = v_fn_4995_;
v_x_4988_ = v___x_4997_;
goto _start;
}
else
{
uint8_t v___x_4999_; 
v___x_4999_ = l_Lean_Expr_isConst(v_x_4987_);
if (v___x_4999_ == 0)
{
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_x_4987_);
lean_dec_ref(v___x_4986_);
goto v___jp_4992_;
}
else
{
lean_object* v___x_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v___x_5000_ = lean_unsigned_to_nat(0u);
v___x_5001_ = lean_array_get_size(v_x_4988_);
v___x_5002_ = lean_nat_dec_lt(v___x_5000_, v___x_5001_);
if (v___x_5002_ == 0)
{
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_x_4987_);
lean_dec_ref(v___x_4986_);
goto v___jp_4992_;
}
else
{
if (v___x_5002_ == 0)
{
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_x_4987_);
lean_dec_ref(v___x_4986_);
goto v___jp_4992_;
}
else
{
size_t v___x_5003_; size_t v___x_5004_; uint8_t v___x_5005_; 
v___x_5003_ = ((size_t)0ULL);
v___x_5004_ = lean_usize_of_nat(v___x_5001_);
v___x_5005_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_4984_, v_numSectionVars_4985_, v_x_4988_, v___x_5003_, v___x_5004_);
if (v___x_5005_ == 0)
{
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_x_4987_);
lean_dec_ref(v___x_4986_);
goto v___jp_4992_;
}
else
{
lean_object* v___x_5006_; uint8_t v___x_5007_; lean_object* v___x_5008_; 
v___x_5006_ = l_Lean_Expr_constName_x21(v_x_4987_);
v___x_5007_ = 0;
v___x_5008_ = l_Lean_Environment_find_x3f(v___x_4986_, v___x_5006_, v___x_5007_);
if (lean_obj_tag(v___x_5008_) == 1)
{
lean_object* v_val_5009_; 
v_val_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_val_5009_);
lean_dec_ref(v___x_5008_);
if (lean_obj_tag(v_val_5009_) == 2)
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5035_; 
v___x_5010_ = l_Lean_Expr_constLevels_x21(v_x_4987_);
lean_dec_ref(v_x_4987_);
v___x_5011_ = l_Lean_Core_instantiateValueLevelParams(v_val_5009_, v___x_5010_, v___x_4999_, v___y_4989_, v___y_4990_);
v_isSharedCheck_5035_ = !lean_is_exclusive(v_val_5009_);
if (v_isSharedCheck_5035_ == 0)
{
lean_object* v_unused_5036_; 
v_unused_5036_ = lean_ctor_get(v_val_5009_, 0);
lean_dec(v_unused_5036_);
v___x_5013_ = v_val_5009_;
v_isShared_5014_ = v_isSharedCheck_5035_;
goto v_resetjp_5012_;
}
else
{
lean_dec(v_val_5009_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5035_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5026_; 
v_a_5015_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5017_ = v___x_5011_;
v_isShared_5018_ = v_isSharedCheck_5026_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_5011_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5026_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = l_Lean_Expr_betaRev(v_a_5015_, v_x_4988_, v___x_5007_, v___x_5007_);
lean_dec_ref(v_x_4988_);
if (v_isShared_5014_ == 0)
{
lean_ctor_set_tag(v___x_5013_, 1);
lean_ctor_set(v___x_5013_, 0, v___x_5019_);
v___x_5021_ = v___x_5013_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5023_; 
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 0, v___x_5021_);
v___x_5023_ = v___x_5017_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5034_; 
lean_del_object(v___x_5013_);
lean_dec_ref(v_x_4988_);
v_a_5027_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5029_ = v___x_5011_;
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5011_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5032_; 
if (v_isShared_5030_ == 0)
{
v___x_5032_ = v___x_5029_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_a_5027_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
}
}
else
{
lean_dec(v_val_5009_);
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_x_4987_);
goto v___jp_4992_;
}
}
else
{
lean_dec(v___x_5008_);
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_x_4987_);
goto v___jp_4992_;
}
}
}
}
}
}
v___jp_4992_:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5037_, lean_object* v_numSectionVars_5038_, lean_object* v___x_5039_, lean_object* v_x_5040_, lean_object* v_x_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5037_, v_numSectionVars_5038_, v___x_5039_, v_x_5040_, v_x_5041_, v___y_5042_, v___y_5043_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v_numSectionVars_5038_);
lean_dec_ref(v_fnNames_5037_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5046_, lean_object* v_numSectionVars_5047_, lean_object* v_env_5048_, lean_object* v_e_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5053_ = l_Lean_Expr_getAppNumArgs(v_e_5049_);
v___x_5054_ = lean_mk_empty_array_with_capacity(v___x_5053_);
lean_dec(v___x_5053_);
v___x_5055_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5046_, v_numSectionVars_5047_, v_env_5048_, v_e_5049_, v___x_5054_, v___y_5050_, v___y_5051_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5056_, lean_object* v_numSectionVars_5057_, lean_object* v_env_5058_, lean_object* v_e_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5056_, v_numSectionVars_5057_, v_env_5058_, v_e_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v_numSectionVars_5057_);
lean_dec_ref(v_fnNames_5056_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5064_, lean_object* v_numSectionVars_5065_, lean_object* v_e_5066_, lean_object* v___f_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v___x_5071_; lean_object* v_env_5072_; lean_object* v___f_5073_; lean_object* v___x_5074_; 
v___x_5071_ = lean_st_ref_get(v___y_5069_);
v_env_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc_ref(v_env_5072_);
lean_dec(v___x_5071_);
v___f_5073_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5073_, 0, v_fnNames_5064_);
lean_closure_set(v___f_5073_, 1, v_numSectionVars_5065_);
lean_closure_set(v___f_5073_, 2, v_env_5072_);
v___x_5074_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5066_, v___f_5073_, v___f_5067_, v___y_5068_, v___y_5069_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5075_, lean_object* v_numSectionVars_5076_, lean_object* v_e_5077_, lean_object* v___f_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5075_, v_numSectionVars_5076_, v_e_5077_, v___f_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5083_, uint8_t v_isExporting_5084_, lean_object* v___x_5085_, lean_object* v_a_x3f_5086_){
_start:
{
lean_object* v___x_5088_; lean_object* v_env_5089_; lean_object* v_nextMacroScope_5090_; lean_object* v_ngen_5091_; lean_object* v_auxDeclNGen_5092_; lean_object* v_traceState_5093_; lean_object* v_messages_5094_; lean_object* v_infoState_5095_; lean_object* v_snapshotTasks_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5107_; 
v___x_5088_ = lean_st_ref_take(v___y_5083_);
v_env_5089_ = lean_ctor_get(v___x_5088_, 0);
v_nextMacroScope_5090_ = lean_ctor_get(v___x_5088_, 1);
v_ngen_5091_ = lean_ctor_get(v___x_5088_, 2);
v_auxDeclNGen_5092_ = lean_ctor_get(v___x_5088_, 3);
v_traceState_5093_ = lean_ctor_get(v___x_5088_, 4);
v_messages_5094_ = lean_ctor_get(v___x_5088_, 6);
v_infoState_5095_ = lean_ctor_get(v___x_5088_, 7);
v_snapshotTasks_5096_ = lean_ctor_get(v___x_5088_, 8);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v___x_5088_, 5);
lean_dec(v_unused_5108_);
v___x_5098_ = v___x_5088_;
v_isShared_5099_ = v_isSharedCheck_5107_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_snapshotTasks_5096_);
lean_inc(v_infoState_5095_);
lean_inc(v_messages_5094_);
lean_inc(v_traceState_5093_);
lean_inc(v_auxDeclNGen_5092_);
lean_inc(v_ngen_5091_);
lean_inc(v_nextMacroScope_5090_);
lean_inc(v_env_5089_);
lean_dec(v___x_5088_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5107_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5100_; lean_object* v___x_5102_; 
v___x_5100_ = l_Lean_Environment_setExporting(v_env_5089_, v_isExporting_5084_);
if (v_isShared_5099_ == 0)
{
lean_ctor_set(v___x_5098_, 5, v___x_5085_);
lean_ctor_set(v___x_5098_, 0, v___x_5100_);
v___x_5102_ = v___x_5098_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v_nextMacroScope_5090_);
lean_ctor_set(v_reuseFailAlloc_5106_, 2, v_ngen_5091_);
lean_ctor_set(v_reuseFailAlloc_5106_, 3, v_auxDeclNGen_5092_);
lean_ctor_set(v_reuseFailAlloc_5106_, 4, v_traceState_5093_);
lean_ctor_set(v_reuseFailAlloc_5106_, 5, v___x_5085_);
lean_ctor_set(v_reuseFailAlloc_5106_, 6, v_messages_5094_);
lean_ctor_set(v_reuseFailAlloc_5106_, 7, v_infoState_5095_);
lean_ctor_set(v_reuseFailAlloc_5106_, 8, v_snapshotTasks_5096_);
v___x_5102_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5103_ = lean_st_ref_set(v___y_5083_, v___x_5102_);
v___x_5104_ = lean_box(0);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
return v___x_5105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5109_, lean_object* v_isExporting_5110_, lean_object* v___x_5111_, lean_object* v_a_x3f_5112_, lean_object* v___y_5113_){
_start:
{
uint8_t v_isExporting_boxed_5114_; lean_object* v_res_5115_; 
v_isExporting_boxed_5114_ = lean_unbox(v_isExporting_5110_);
v_res_5115_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5109_, v_isExporting_boxed_5114_, v___x_5111_, v_a_x3f_5112_);
lean_dec(v_a_x3f_5112_);
lean_dec(v___y_5109_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5116_, uint8_t v_isExporting_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
lean_object* v___x_5121_; lean_object* v_env_5122_; uint8_t v_isExporting_5123_; lean_object* v___x_5124_; lean_object* v_env_5125_; lean_object* v_nextMacroScope_5126_; lean_object* v_ngen_5127_; lean_object* v_auxDeclNGen_5128_; lean_object* v_traceState_5129_; lean_object* v_messages_5130_; lean_object* v_infoState_5131_; lean_object* v_snapshotTasks_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5171_; 
v___x_5121_ = lean_st_ref_get(v___y_5119_);
v_env_5122_ = lean_ctor_get(v___x_5121_, 0);
lean_inc_ref(v_env_5122_);
lean_dec(v___x_5121_);
v_isExporting_5123_ = lean_ctor_get_uint8(v_env_5122_, sizeof(void*)*8);
lean_dec_ref(v_env_5122_);
v___x_5124_ = lean_st_ref_take(v___y_5119_);
v_env_5125_ = lean_ctor_get(v___x_5124_, 0);
v_nextMacroScope_5126_ = lean_ctor_get(v___x_5124_, 1);
v_ngen_5127_ = lean_ctor_get(v___x_5124_, 2);
v_auxDeclNGen_5128_ = lean_ctor_get(v___x_5124_, 3);
v_traceState_5129_ = lean_ctor_get(v___x_5124_, 4);
v_messages_5130_ = lean_ctor_get(v___x_5124_, 6);
v_infoState_5131_ = lean_ctor_get(v___x_5124_, 7);
v_snapshotTasks_5132_ = lean_ctor_get(v___x_5124_, 8);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5171_ == 0)
{
lean_object* v_unused_5172_; 
v_unused_5172_ = lean_ctor_get(v___x_5124_, 5);
lean_dec(v_unused_5172_);
v___x_5134_ = v___x_5124_;
v_isShared_5135_ = v_isSharedCheck_5171_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_snapshotTasks_5132_);
lean_inc(v_infoState_5131_);
lean_inc(v_messages_5130_);
lean_inc(v_traceState_5129_);
lean_inc(v_auxDeclNGen_5128_);
lean_inc(v_ngen_5127_);
lean_inc(v_nextMacroScope_5126_);
lean_inc(v_env_5125_);
lean_dec(v___x_5124_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5171_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5139_; 
v___x_5136_ = l_Lean_Environment_setExporting(v_env_5125_, v_isExporting_5117_);
v___x_5137_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 5, v___x_5137_);
lean_ctor_set(v___x_5134_, 0, v___x_5136_);
v___x_5139_ = v___x_5134_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_nextMacroScope_5126_);
lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_ngen_5127_);
lean_ctor_set(v_reuseFailAlloc_5170_, 3, v_auxDeclNGen_5128_);
lean_ctor_set(v_reuseFailAlloc_5170_, 4, v_traceState_5129_);
lean_ctor_set(v_reuseFailAlloc_5170_, 5, v___x_5137_);
lean_ctor_set(v_reuseFailAlloc_5170_, 6, v_messages_5130_);
lean_ctor_set(v_reuseFailAlloc_5170_, 7, v_infoState_5131_);
lean_ctor_set(v_reuseFailAlloc_5170_, 8, v_snapshotTasks_5132_);
v___x_5139_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5140_; lean_object* v_r_5141_; 
v___x_5140_ = lean_st_ref_set(v___y_5119_, v___x_5139_);
lean_inc(v___y_5119_);
lean_inc_ref(v___y_5118_);
v_r_5141_ = lean_apply_3(v_x_5116_, v___y_5118_, v___y_5119_, lean_box(0));
if (lean_obj_tag(v_r_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5158_; 
v_a_5142_ = lean_ctor_get(v_r_5141_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_r_5141_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5144_ = v_r_5141_;
v_isShared_5145_ = v_isSharedCheck_5158_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v_r_5141_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5158_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
lean_inc(v_a_5142_);
if (v_isShared_5145_ == 0)
{
lean_ctor_set_tag(v___x_5144_, 1);
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5142_);
v___x_5147_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
lean_object* v___x_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
v___x_5148_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5119_, v_isExporting_5123_, v___x_5137_, v___x_5147_);
lean_dec_ref(v___x_5147_);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5155_ == 0)
{
lean_object* v_unused_5156_; 
v_unused_5156_ = lean_ctor_get(v___x_5148_, 0);
lean_dec(v_unused_5156_);
v___x_5150_ = v___x_5148_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_dec(v___x_5148_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 0, v_a_5142_);
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5142_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
v_a_5159_ = lean_ctor_get(v_r_5141_, 0);
lean_inc(v_a_5159_);
lean_dec_ref(v_r_5141_);
v___x_5160_ = lean_box(0);
v___x_5161_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5119_, v_isExporting_5123_, v___x_5137_, v___x_5160_);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5168_ == 0)
{
lean_object* v_unused_5169_; 
v_unused_5169_ = lean_ctor_get(v___x_5161_, 0);
lean_dec(v_unused_5169_);
v___x_5163_ = v___x_5161_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_dec(v___x_5161_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
lean_ctor_set_tag(v___x_5163_, 1);
lean_ctor_set(v___x_5163_, 0, v_a_5159_);
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5159_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5173_, lean_object* v_isExporting_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
uint8_t v_isExporting_boxed_5178_; lean_object* v_res_5179_; 
v_isExporting_boxed_5178_ = lean_unbox(v_isExporting_5174_);
v_res_5179_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5173_, v_isExporting_boxed_5178_, v___y_5175_, v___y_5176_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5180_, uint8_t v_when_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
if (v_when_5181_ == 0)
{
lean_object* v___x_5185_; 
lean_inc(v___y_5183_);
lean_inc_ref(v___y_5182_);
v___x_5185_ = lean_apply_3(v_x_5180_, v___y_5182_, v___y_5183_, lean_box(0));
return v___x_5185_;
}
else
{
uint8_t v___x_5186_; lean_object* v___x_5187_; 
v___x_5186_ = 0;
v___x_5187_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5180_, v___x_5186_, v___y_5182_, v___y_5183_);
return v___x_5187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5188_, lean_object* v_when_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
uint8_t v_when_boxed_5193_; lean_object* v_res_5194_; 
v_when_boxed_5193_ = lean_unbox(v_when_5189_);
v_res_5194_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5188_, v_when_boxed_5193_, v___y_5190_, v___y_5191_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5195_, lean_object* v_numSectionVars_5196_, lean_object* v_e_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v___f_5201_; lean_object* v___f_5202_; uint8_t v___x_5203_; lean_object* v___x_5204_; 
v___f_5201_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5202_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5202_, 0, v_fnNames_5195_);
lean_closure_set(v___f_5202_, 1, v_numSectionVars_5196_);
lean_closure_set(v___f_5202_, 2, v_e_5197_);
lean_closure_set(v___f_5202_, 3, v___f_5201_);
v___x_5203_ = 1;
v___x_5204_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5202_, v___x_5203_, v_a_5198_, v_a_5199_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5205_, lean_object* v_numSectionVars_5206_, lean_object* v_e_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5205_, v_numSectionVars_5206_, v_e_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_a_5209_);
lean_dec_ref(v_a_5208_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5212_, lean_object* v_x_5213_, uint8_t v_isExporting_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v___x_5218_; 
v___x_5218_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5213_, v_isExporting_5214_, v___y_5215_, v___y_5216_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5219_, lean_object* v_x_5220_, lean_object* v_isExporting_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
uint8_t v_isExporting_boxed_5225_; lean_object* v_res_5226_; 
v_isExporting_boxed_5225_ = lean_unbox(v_isExporting_5221_);
v_res_5226_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5219_, v_x_5220_, v_isExporting_boxed_5225_, v___y_5222_, v___y_5223_);
lean_dec(v___y_5223_);
lean_dec_ref(v___y_5222_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5227_, lean_object* v_x_5228_, uint8_t v_when_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5228_, v_when_5229_, v___y_5230_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5234_, lean_object* v_x_5235_, lean_object* v_when_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
uint8_t v_when_boxed_5240_; lean_object* v_res_5241_; 
v_when_boxed_5240_ = lean_unbox(v_when_5236_);
v_res_5241_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5234_, v_x_5235_, v_when_boxed_5240_, v___y_5237_, v___y_5238_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5246_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5246_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec_ref(v_x_5248_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v___y_5258_; lean_object* v___x_5261_; 
v___x_5261_ = l_Lean_inaccessible_x3f(v_e_5253_);
if (lean_obj_tag(v___x_5261_) == 1)
{
lean_object* v_val_5262_; 
lean_dec_ref(v_e_5253_);
v_val_5262_ = lean_ctor_get(v___x_5261_, 0);
lean_inc(v_val_5262_);
lean_dec_ref(v___x_5261_);
v___y_5258_ = v_val_5262_;
goto v___jp_5257_;
}
else
{
lean_dec(v___x_5261_);
v___y_5258_ = v_e_5253_;
goto v___jp_5257_;
}
v___jp_5257_:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5259_, 0, v___y_5258_);
v___x_5260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
return v___x_5260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5263_, v___y_5264_, v___y_5265_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v___f_5274_; lean_object* v___f_5275_; lean_object* v___x_5276_; 
v___f_5274_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5275_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5276_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5270_, v___f_5274_, v___f_5275_, v_a_5271_, v_a_5272_);
return v___x_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5277_, v_a_5278_, v_a_5279_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v___y_5287_; lean_object* v___x_5290_; 
v___x_5290_ = l_Lean_patternWithRef_x3f(v_e_5282_);
if (lean_obj_tag(v___x_5290_) == 1)
{
lean_object* v_val_5291_; lean_object* v_snd_5292_; 
lean_dec_ref(v_e_5282_);
v_val_5291_ = lean_ctor_get(v___x_5290_, 0);
lean_inc(v_val_5291_);
lean_dec_ref(v___x_5290_);
v_snd_5292_ = lean_ctor_get(v_val_5291_, 1);
lean_inc(v_snd_5292_);
lean_dec(v_val_5291_);
v___y_5287_ = v_snd_5292_;
goto v___jp_5286_;
}
else
{
lean_dec(v___x_5290_);
v___y_5287_ = v_e_5282_;
goto v___jp_5286_;
}
v___jp_5286_:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5288_, 0, v___y_5287_);
v___x_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
return v___x_5289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_){
_start:
{
lean_object* v_res_5297_; 
v_res_5297_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5293_, v___y_5294_, v___y_5295_);
lean_dec(v___y_5295_);
lean_dec_ref(v___y_5294_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_){
_start:
{
lean_object* v___f_5303_; lean_object* v___f_5304_; lean_object* v___x_5305_; 
v___f_5303_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5304_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5305_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5299_, v___f_5303_, v___f_5304_, v_a_5300_, v_a_5301_);
return v___x_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5306_, v_a_5307_, v_a_5308_);
lean_dec(v_a_5308_);
lean_dec_ref(v_a_5307_);
return v_res_5310_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedTransformStep_default = _init_l_Lean_instInhabitedTransformStep_default();
lean_mark_persistent(l_Lean_instInhabitedTransformStep_default);
l_Lean_instInhabitedTransformStep = _init_l_Lean_instInhabitedTransformStep();
lean_mark_persistent(l_Lean_instInhabitedTransformStep);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Transform(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Transform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Transform(builtin);
}
#ifdef __cplusplus
}
#endif
